#!/usr/bin/env python3
"""Profile Wang 2026 text-format rank lower-bound certificates.

The certificate is a text-format protobuf. We avoid depending on generated
protobuf bindings and scan only the fields needed for research triage: orbit
index, decoded A-side restrictions, claimed lower bound, proof type, projection
or extra-constraint metadata, and backtracking proof size.

For the matrix_q02_n333 certificate, each restriction row is a GFVec<2,1,9>
serialized as a little-endian 16-bit value whose low nine bits are row-major
A-coordinates a00,related analysis,related analysis,a10,...,a22. The verifier computes the subspace
rank/dimension from these rows; for this certificate they are RREF rows.
"""
from __future__ import annotations

import argparse
import ast
import json
import re
from collections import Counter, defaultdict
from pathlib import Path


def decode_textproto_bytes(quoted: str) -> bytes:
    """Decode a protobuf text-format bytes literal as Python bytes.

    The input includes surrounding double quotes, e.g. "\\001\\000$\\000".
    ast.literal_eval gives a Python str with code points 0..255 for protobuf
    byte escapes; latin1 preserves those code points as bytes.
    """
    return ast.literal_eval(quoted).encode("latin1")


def decode_constraints(quoted: str | None) -> list[int]:
    if not quoted:
        return []
    b = decode_textproto_bytes(quoted)
    if len(b) % 2 != 0:
        raise ValueError(f"constraint byte length not divisible by 2: {len(b)}")
    vals = []
    for i in range(0, len(b), 2):
        vals.append(b[i] | (b[i + 1] << 8))
    return vals


def mask_to_terms(mask: int) -> list[str]:
    terms = []
    for bit in range(9):
        if mask & (1 << bit):
            terms.append(f"a{bit//3+1}{bit%3+1}")
    return terms


def mask_to_matrix(mask: int) -> list[list[int]]:
    return [[1 if mask & (1 << (3*r+c)) else 0 for c in range(3)] for r in range(3)]


def constraint_summary(vals: list[int]) -> list[dict]:
    return [
        {"value": v, "hex": hex(v), "terms": mask_to_terms(v), "matrix": mask_to_matrix(v)}
        for v in vals
    ]


def parse_cert(path: Path):
    text = path.read_text(errors="replace")
    top = {}
    for key in ["problem_name", "characteristic", "extension_degree", "na", "nb", "nc"]:
        m = re.search(rf'^\s*{key}:\s*(.+)$', text, flags=re.M)
        if m:
            raw = m.group(1).strip()
            if raw.startswith('"'):
                top[key] = ast.literal_eval(raw)
            else:
                top[key] = int(raw)

    blocks = text.split('constrained_tensors {')[1:]
    orbits = []
    for block in blocks:
        # Conservative enough for this flat repeated message: split at a line
        # that closes the constrained_tensors block before the next block.
        block = block.split('\n}\n', 1)[0]
        rec = {"index": 0, "rank_lower_bound": None, "proof_type": "none",
               "projection_type": None, "extra_constraint": None,
               "backtracking_proof_size": None, "raw_constraints_line": None,
               "constraint_values": [], "constraint_count": 0}
        m = re.search(r'\n\s*index:\s*(\d+)', '\n' + block)
        if m:
            rec["index"] = int(m.group(1))
        m = re.search(r'\n\s*rank_lower_bound:\s*(-?\d+)', '\n' + block)
        if m:
            rec["rank_lower_bound"] = int(m.group(1))
        m = re.search(r'\n\s*constraints:\s*(".*")', '\n' + block)
        if m:
            rec["raw_constraints_line"] = m.group(1)
            vals = decode_constraints(rec["raw_constraints_line"])
            rec["constraint_values"] = vals
            rec["constraint_count"] = len(vals)
        for ptype, key in [("flatten", "flatten_matrix_proof"),
                           ("forced_product", "forced_product_proof"),
                           ("degenerate", "degenerate_proof"),
                           ("backtracking", "backtracking_proof")]:
            if key in block:
                rec["proof_type"] = ptype
                break
        m = re.search(r'projection_type:\s*(\d+)', block)
        if m:
            rec["projection_type"] = int(m.group(1))
        m = re.search(r'extra_constraint:\s*(\d+)', block)
        if m:
            rec["extra_constraint"] = int(m.group(1))
        m = re.search(r'proof_size:\s*(\d+)', block)
        if m:
            rec["backtracking_proof_size"] = int(m.group(1))
        orbits.append(rec)

    ranks = Counter(r["rank_lower_bound"] for r in orbits)
    proofs = Counter(r["proof_type"] for r in orbits)
    dims = Counter(r["constraint_count"] for r in orbits)
    rank_by_dim = defaultdict(Counter)
    proof_by_dim = defaultdict(Counter)
    rank_by_proof = defaultdict(Counter)
    for r in orbits:
        rank_by_dim[r["constraint_count"]][r["rank_lower_bound"]] += 1
        proof_by_dim[r["constraint_count"]][r["proof_type"]] += 1
        rank_by_proof[r["proof_type"]][r["rank_lower_bound"]] += 1
    forced_proj = Counter(r["projection_type"] for r in orbits if r["proof_type"] == "forced_product")
    bt_sizes = [r for r in orbits if r["proof_type"] == "backtracking"]
    bt_sizes_sorted = sorted(bt_sizes, key=lambda r: r["backtracking_proof_size"] or 0, reverse=True)

    def public_orbit(r, with_constraints=False):
        out = {k: r[k] for k in ["index", "constraint_count", "rank_lower_bound",
                                 "proof_type", "projection_type", "extra_constraint",
                                 "backtracking_proof_size"]}
        out["constraint_values"] = r["constraint_values"]
        if with_constraints:
            out["constraints_decoded"] = constraint_summary(r["constraint_values"])
        return out

    one_dim = [public_orbit(r, True) for r in orbits if r["constraint_count"] == 1]
    zero_dim = [public_orbit(r, True) for r in orbits if r["constraint_count"] == 0]
    two_dim = [public_orbit(r, True) for r in orbits if r["constraint_count"] == 2]
    hard = [public_orbit(r, True) for r in bt_sizes_sorted[:20]]

    return {
        "certificate": str(path),
        "top_fields": top,
        "orbit_count": len(orbits),
        "dimension_distribution": dict(sorted(dims.items())),
        "rank_distribution": dict(sorted(ranks.items(), key=lambda kv: (kv[0] is None, kv[0]))),
        "rank_by_dimension": {str(k): dict(sorted(v.items(), key=lambda kv: (kv[0] is None, kv[0]))) for k, v in sorted(rank_by_dim.items())},
        "proof_type_distribution": dict(proofs),
        "proof_by_dimension": {str(k): dict(v) for k, v in sorted(proof_by_dim.items())},
        "rank_by_proof_type": {k: dict(sorted(v.items(), key=lambda kv: (kv[0] is None, kv[0]))) for k, v in sorted(rank_by_proof.items())},
        "forced_product_projection_distribution": dict(sorted(forced_proj.items(), key=lambda kv: str(kv[0]))),
        "backtracking_count": len(bt_sizes),
        "backtracking_total_recorded_leaf_count": sum(r["backtracking_proof_size"] or 0 for r in bt_sizes),
        "backtracking_top20": hard,
        "dimension_0_orbits": zero_dim,
        "dimension_1_orbits": one_dim,
        "dimension_2_orbits": two_dim,
        "last_orbit": public_orbit(orbits[-1], True) if orbits else None,
        "first_orbits": [public_orbit(r, True) for r in orbits[:10]],
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cert", type=Path)
    ap.add_argument("--out", type=Path)
    args = ap.parse_args()
    profile = parse_cert(args.cert)
    payload = json.dumps(profile, indent=2, sort_keys=True)
    print(payload)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(payload + "\n")

if __name__ == "__main__":
    main()
