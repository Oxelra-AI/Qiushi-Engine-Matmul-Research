#!/usr/bin/env python3
"""Audit Wang certificate/LUT expansion and quotient row invariance.

This script addresses the proof-chain middle link used by the quotient support
searches.  It does not re-prove Wang's 496 certificate nodes; instead it checks:
  * pinned file hashes and recorded verifier receipt fields;
  * LUT coverage/conflict metadata and 496 orbit-node profile counts;
  * quotient row generation semantics against the full 9-dimensional LUT;
  * invariance of quotient row lower bounds under the computed pivot stabilizer;
  * proof-type distribution for quotient rows, and optionally for used DFS rows.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import pickle
import struct
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable, Sequence

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import in_rowspace, pack_basis, rref_basis, unpack_basis  # type: ignore
from profile_wang_cert import parse_cert  # type: ignore
from quotient_line_caps_and_controls import quotient_project  # type: ignore
from quotient_stabilizer_orbits import compute_stabilizer, quotient_action  # type: ignore

CERT = Path("data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt")
BTP = Path("data/wang_f2_lb20/cert_matrix_q02_n333.btp")
RECEIPT = Path("data/wang_f2_lb20/verify_receipt.json")
LUT = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
LUT_META = Path("data/wang_f2_lb20/wang_subspace_lut.meta.json")
CERT_PROFILE = Path("data/wang_f2_lb20/cert_profile.json")
BIN_DIR = SESSION / "workspace/data/wang_native/quotient_binaries"
OUTDIR = SESSION / "workspace/data/wang_native/audit"
EXPECTED_CERT_SHA = "25595a883ce877eecd802139ff4e07646e154b2797ad6fe7f9ec737ab0c6135d"
EXPECTED_BTP_SHA = "4e824eb13c235e69045881d173d8ababe622421055a238005afce413aabe3289"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def gf2_reduce(v: int, basis: Sequence[int]) -> int:
    x = int(v)
    piv = {int(b).bit_length() - 1: int(b) for b in basis if b}
    while x:
        p = x.bit_length() - 1
        b = piv.get(p)
        if b is None:
            return x
        x ^= b
    return 0


def in_span(point: int, basis: Sequence[int]) -> bool:
    return gf2_reduce(point, basis) == 0


def quotient_subspace_key(key9: int, pivot: int) -> int | None:
    basis = list(unpack_basis(int(key9)))
    if not in_span(pivot, basis):
        return None
    qrows = []
    for b in basis:
        qp = quotient_project(int(b), pivot)
        if qp:
            qrows.append(qp)
    qb = rref_basis(qrows, n=8)
    return pack_basis(qb)


def quotient_projected_points_from_key9(key9: int, pivot: int) -> tuple[int, ...]:
    basis = list(unpack_basis(int(key9)))
    qpts = set()
    for m in range(1, 1 << len(basis)):
        v = 0
        for i, b in enumerate(basis):
            if (m >> i) & 1:
                v ^= int(b)
        qp = quotient_project(v, pivot)
        if qp:
            qpts.add(qp)
    return tuple(sorted(qpts))


def words_from_points(points: Iterable[int]) -> tuple[int, int, int, int]:
    words = [0, 0, 0, 0]
    for p in points:
        words[p >> 6] |= 1 << (p & 63)
    return tuple(words)  # type: ignore[return-value]


def load_lut_payload() -> tuple[dict[int, int], dict[str, Any]]:
    with LUT.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}, payload.get("meta", {})


def build_node_lookup() -> tuple[dict[int, int], list[dict[str, Any]]]:
    # Parse profile from the certificate directly to avoid trusting stale JSON,
    # but keep field names compatible with profile_wang_cert.py output.
    prof = parse_cert(CERT)
    cert_orbits = prof["first_orbits"]  # not complete; use cert_profile for complete richer table if available
    # The complete cert_profile is already a parsed profile containing full node details only in first/last/top lists.
    # Re-parse via wang_capacity_lazy.parse_cert for all 496 records.
    from wang_capacity_lazy import parse_cert as parse_records  # type: ignore
    records = parse_records(CERT)
    lookup = {}
    nodes = []
    for pos, rec in enumerate(records):
        basis = rref_basis(rec.constraints, n=9)
        key = pack_basis(basis)
        lookup[key] = pos
        nodes.append({
            "position": pos,
            "cert_index": int(rec.index),
            "basis9": [int(x) for x in basis],
            "dim9": len(basis),
            "lb": int(rec.lb),
            "proof_type": rec.proof_type,
        })
    return lookup, nodes


def lookup_orbit_for_key9(key9: int, lut_lb: int, node_lookup: dict[int, int], nodes: Sequence[dict[str, Any]]) -> int | None:
    # Direct node key works only for representatives.  For arbitrary LUT rows,
    # use the group-expanded LUT metadata orbit order is not available in LUT.
    # Build a slower full expansion map lazily if needed?  For proof-type attribution
    # to all quotient rows we need an orbit map.  Use research_record closed orbit cache if present;
    # it stores key_to_orbit with the same 496-node order as parse_cert.
    return None


def load_key_to_orbit() -> tuple[dict[int, int], list[dict[str, Any]]]:
    cache = Path("data/wang_f2_lb20/wang_orbit_closed_cache.pkl")
    with cache.open("rb") as f:
        payload = pickle.load(f)
    key_to_orbit = {int(k): int(v) for k, v in payload["key_to_orbit"].items()}
    orbits = payload["orbits"]
    return key_to_orbit, orbits


def read_e11wang_binary(path: Path) -> list[tuple[int, int, tuple[int, int, int, int]]]:
    rows = []
    with path.open("rb") as f:
        magic = f.read(8)
        if magic != b"E11WANG1":
            raise ValueError(f"bad magic {magic!r}")
        nrows = struct.unpack("<I", f.read(4))[0]
        for _ in range(nrows):
            cap, dim, _res = struct.unpack("<BBH", f.read(4))
            words = struct.unpack("<QQQQ", f.read(32))
            rows.append((cap, dim, tuple(int(w) for w in words)))
    return rows


def quotient_rows_from_lut(pivot: int, target: int, max_cap: int) -> dict[int, dict[str, Any]]:
    lut, _ = load_lut_payload()
    key_to_orbit, orbits = load_key_to_orbit()
    qrows: dict[int, dict[str, Any]] = {}
    containing = 0
    negative = 0
    for key9, lb in lut.items():
        basis = list(unpack_basis(key9))
        if not in_span(pivot, basis):
            continue
        containing += 1
        cap = target - int(lb)
        if cap < 0:
            negative += 1
            continue
        if cap > max_cap or cap >= target:
            continue
        qkey = quotient_subspace_key(key9, pivot)
        if qkey is None or qkey == 0:
            continue
        qpts = quotient_projected_points_from_key9(key9, pivot)
        if not qpts:
            continue
        oi = key_to_orbit[key9]
        rec = orbits[oi]
        old = qrows.get(qkey)
        info = {
            "qkey": int(qkey),
            "key9": int(key9),
            "lb": int(lb),
            "cap": int(cap),
            "dim8": int(qkey & 0xF),
            "dim9": int(key9 & 0xF),
            "words": words_from_points(qpts),
            "orbit": int(oi),
            "cert_index": int(rec.get("cert_index", oi)),
            "proof_type": rec.get("proof_type", "unknown"),
        }
        if old is not None:
            # In principle the same quotient subspace can be represented by the same unique
            # original subspace containing pivot: preimage under quotient.  Treat any duplicate
            # as a semantic issue unless all data agree.
            if old["lb"] != info["lb"] or old["words"] != info["words"]:
                raise RuntimeError(f"quotient row duplicate disagreement for qkey={qkey}")
        qrows[qkey] = info
    return qrows


def transform8(v: int, basis_images: Sequence[int]) -> int:
    out = 0
    x = int(v)
    bit = 0
    while x:
        if x & 1:
            out ^= int(basis_images[bit])
        bit += 1
        x >>= 1
    return out


def transform_key8_fast(key8: int, basis_images: Sequence[int]) -> int:
    rows = list(unpack_basis(int(key8)))
    transformed = [transform8(int(r), basis_images) for r in rows]
    return pack_basis(rref_basis(transformed, n=8))


def compose_perm(g: tuple[int, ...], h: tuple[int, ...]) -> tuple[int, ...]:
    """Return g o h for point permutations stored as perm[p]."""
    return tuple(g[h[i]] for i in range(256))


def close_perm_group(gens: Sequence[tuple[int, ...]]) -> set[tuple[int, ...]]:
    from collections import deque
    ident = tuple(range(256))
    group: set[tuple[int, ...]] = {ident}
    q: deque[tuple[int, ...]] = deque()
    for g in gens:
        if g not in group:
            group.add(g)
            q.append(g)
    while q:
        a = q.popleft()
        snapshot = list(group)
        for b in snapshot:
            for c in (compose_perm(a, b), compose_perm(b, a)):
                if c not in group:
                    group.add(c)
                    q.append(c)
    return group


def greedy_perm_generators(perms: Sequence[tuple[int, ...]]) -> tuple[list[tuple[int, ...]], list[dict[str, int]]]:
    target = set(perms)
    ident = tuple(range(256))
    gens: list[tuple[int, ...]] = []
    group: set[tuple[int, ...]] = {ident}
    history: list[dict[str, int]] = []
    candidates = [p for p in perms if p != ident]
    while len(group) < len(target):
        chosen = None
        chosen_group = None
        best = len(group)
        for cand in candidates:
            if cand in group:
                continue
            trial = close_perm_group(gens + [cand])
            if not trial <= target:
                raise RuntimeError("candidate generators produced permutation outside stabilizer action")
            if len(trial) > best:
                chosen = cand
                chosen_group = trial
                best = len(trial)
                if best >= 2 * max(1, len(group)) or best == len(target):
                    break
        if chosen is None or chosen_group is None:
            raise RuntimeError(f"could not grow quotient stabilizer permutation group from {len(group)} toward {len(target)}")
        gens.append(chosen)
        group = chosen_group
        history.append({"generator_index": len(gens) - 1, "closure_size": len(group)})
    return gens, history


def stabilizer_point_permutations(pivot: int) -> tuple[list[tuple[int, ...]], int]:
    stab = compute_stabilizer(pivot)
    perms = []
    for P, Q in stab:
        perm = [0]
        for p in range(1, 256):
            perm.append(int(quotient_action(P, Q, pivot, p)))
        # sanity: stabilizer must induce a linear permutation of quotient points
        if sorted(perm) != list(range(256)):
            raise RuntimeError("stabilizer element did not induce a permutation of quotient points")
        perms.append(tuple(perm))
    # remove duplicates while preserving order
    seen = set()
    uniq = []
    for p in perms:
        if p not in seen:
            seen.add(p)
            uniq.append(p)
    return uniq, len(stab)


def basis_images_from_perm(perm: Sequence[int]) -> tuple[int, ...]:
    return tuple(int(perm[1 << i]) for i in range(8))


def audit_pivot(pivot_name: str, pivot: int, target: int, max_cap: int, sample_used: list[Path]) -> dict[str, Any]:
    qrows = quotient_rows_from_lut(pivot, target, max_cap)
    bin_path = BIN_DIR / f"{pivot_name}_all_n{target}.bin"
    binary_rows = read_e11wang_binary(bin_path) if bin_path.exists() else []
    bin_counter = Counter((cap, dim, words) for cap, dim, words in binary_rows)
    gen_counter = Counter((r["cap"], r["dim8"], r["words"]) for r in qrows.values())
    binary_match = bin_counter == gen_counter

    proof_hist = Counter(r["proof_type"] for r in qrows.values())
    dim_proof_hist: dict[str, Counter[str]] = defaultdict(Counter)
    cap_proof_hist: dict[str, Counter[str]] = defaultdict(Counter)
    for r in qrows.values():
        dim_proof_hist[str(r["dim8"])] [r["proof_type"]] += 1
        cap_proof_hist[str(r["cap"])] [r["proof_type"]] += 1

    # Invariance under the stabilizer.  Checking all 96/168 elements against all
    # 417k rows is possible but slow in Python.  It is enough to check a generator
    # set whose closure is the full induced stabilizer permutation group.
    perms, raw_stab_size = stabilizer_point_permutations(pivot)
    gens, gen_history = greedy_perm_generators(perms)
    mismatch_head = []
    checked_pairs = 0
    qkey_to_lb = {k: r["lb"] for k, r in qrows.items()}
    qkey_to_cap = {k: r["cap"] for k, r in qrows.items()}
    keys = list(qrows.keys())
    for gi, perm in enumerate(gens):
        imgs = basis_images_from_perm(perm)
        for qkey in keys:
            k2 = transform_key8_fast(qkey, imgs)
            checked_pairs += 1
            if k2 not in qrows or qkey_to_lb[k2] != qkey_to_lb[qkey] or qkey_to_cap[k2] != qkey_to_cap[qkey]:
                if len(mismatch_head) < 20:
                    mismatch_head.append({
                        "generator_index": gi,
                        "qkey": int(qkey),
                        "image_qkey": int(k2),
                        "lb": qkey_to_lb[qkey],
                        "image_lb": qkey_to_lb.get(k2),
                        "cap": qkey_to_cap[qkey],
                        "image_cap": qkey_to_cap.get(k2),
                    })
    used_summaries = []
    for upath in sample_used:
        if not upath.exists():
            continue
        used = json.loads(upath.read_text())
        all_used_idx = set()
        for key in ("small_saturated_file_rows", "small_overcap_file_rows", "big_overcap_file_rows"):
            all_used_idx.update(int(x) for x in used.get(key, []))
        rows_by_file_idx = list(qrows.values())
        # qrows insertion order follows LUT scan and binary generation, matching file_idx.
        proof = Counter()
        caph = Counter()
        dimh = Counter()
        for idx in all_used_idx:
            if 0 <= idx < len(rows_by_file_idx):
                r = rows_by_file_idx[idx]
                proof[r["proof_type"]] += 1
                caph[r["cap"]] += 1
                dimh[r["dim8"]] += 1
        used_summaries.append({
            "used_rows_file": str(upath),
            "used_row_count": len(all_used_idx),
            "proof_type_hist": dict(sorted(proof.items())),
            "cap_hist": dict(sorted((int(k), int(v)) for k, v in caph.items())),
            "dim8_hist": dict(sorted((int(k), int(v)) for k, v in dimh.items())),
            "head_file_indices": sorted(all_used_idx)[:50],
        })

    return {
        "pivot_name": pivot_name,
        "pivot": pivot,
        "target": target,
        "max_cap": max_cap,
        "quotient_rows_recomputed": len(qrows),
        "binary_path": str(bin_path),
        "binary_rows": len(binary_rows),
        "binary_sha256": sha256(bin_path) if bin_path.exists() else None,
        "binary_matches_recomputed_rows": binary_match,
        "binary_minus_recomputed_counter_examples": [str(x) for x, c in list((bin_counter - gen_counter).items())[:5]],
        "recomputed_minus_binary_counter_examples": [str(x) for x, c in list((gen_counter - bin_counter).items())[:5]],
        "proof_type_hist": dict(sorted(proof_hist.items())),
        "dim8_by_proof_type": {d: dict(sorted(c.items())) for d, c in sorted(dim_proof_hist.items(), key=lambda kv: int(kv[0]))},
        "cap_by_proof_type": {d: dict(sorted(c.items())) for d, c in sorted(cap_proof_hist.items(), key=lambda kv: int(kv[0]))},
        "stabilizer_size_raw_pairs": raw_stab_size,
        "stabilizer_induced_permutation_count": len(perms),
        "stabilizer_generator_count": len(gens),
        "stabilizer_generator_history": gen_history,
        "stabilizer_invariance_checked_generator_pairs": checked_pairs,
        "stabilizer_invariance_mismatch_count_head_only": len(mismatch_head),
        "stabilizer_invariance_mismatch_head": mismatch_head,
        "stabilizer_invariance_passed": not mismatch_head,
        "used_row_summaries": used_summaries,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--max-cap", type=int, default=18)
    ap.add_argument("--pivots", default="rank2,rank3")
    ap.add_argument("--used-rows", nargs="*", type=Path, default=[])
    ap.add_argument("--out", type=Path, default=OUTDIR / "quotient_wang_audit.json")
    args = ap.parse_args()

    OUTDIR.mkdir(parents=True, exist_ok=True)
    cert_sha = sha256(CERT)
    btp_sha = sha256(BTP)
    receipt = json.loads(RECEIPT.read_text())
    meta = json.loads(LUT_META.read_text())
    profile = json.loads(CERT_PROFILE.read_text())

    result: dict[str, Any] = {
        "schema": "quotient_wang_audit_v1",
        "wang_certificate": {
            "cert_path": str(CERT),
            "btp_path": str(BTP),
            "cert_sha256": cert_sha,
            "btp_sha256": btp_sha,
            "cert_sha256_matches_expected": cert_sha == EXPECTED_CERT_SHA,
            "btp_sha256_matches_expected": btp_sha == EXPECTED_BTP_SHA,
            "receipt_status": receipt.get("status"),
            "receipt_exit_code": receipt.get("verifier_exit_code"),
            "receipt_claimed_lower_bound": receipt.get("claimed_lower_bound"),
            "receipt_contains_verified_line": "Verified. Rank lower bound for matrix_q02_n333 is 20" in receipt.get("verifier_stderr", ""),
            "profile_orbit_count": profile.get("orbit_count"),
            "profile_dimension_distribution": profile.get("dimension_distribution"),
            "profile_proof_type_distribution": profile.get("proof_type_distribution"),
        },
        "lut_expansion_meta": {
            "coverage_ok": meta.get("coverage_ok"),
            "conflict_count": meta.get("conflict_count"),
            "expected_subspace_count": meta.get("expected_subspace_count"),
            "actual_by_dimension": meta.get("actual_by_dimension"),
            "expected_by_dimension": meta.get("expected_by_dimension"),
            "action_count": meta.get("action_count"),
            "build_elapsed_sec": meta.get("build_elapsed_sec"),
        },
        "quotients": {},
    }

    pivots = {"rank2": 17, "rank3": 273, "rank1": 1}
    for name in [x.strip() for x in args.pivots.split(",") if x.strip()]:
        print(f"Auditing {name} pivot {pivots[name]}...", flush=True)
        result["quotients"][name] = audit_pivot(name, pivots[name], args.target, args.max_cap, args.used_rows)
        q = result["quotients"][name]
        print(f"  rows={q['quotient_rows_recomputed']} binary_match={q['binary_matches_recomputed_rows']} invariant={q['stabilizer_invariance_passed']}", flush=True)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(args.out), "certificate_ok": result["wang_certificate"], "quotient_brief": {k: {"rows": v["quotient_rows_recomputed"], "binary_match": v["binary_matches_recomputed_rows"], "invariant": v["stabilizer_invariance_passed"], "proof_type_hist": v["proof_type_hist"]} for k, v in result["quotients"].items()}}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
