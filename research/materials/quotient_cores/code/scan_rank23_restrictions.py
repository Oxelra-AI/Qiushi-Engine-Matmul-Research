#!/usr/bin/env python3
"""Scan exact rank-23 3x3 matrix-multiplication schemes over F2 for
short codimension-one restricted-core decompositions.

Scientific purpose
------------------
For a rank-23 decomposition T = sum_t u_t⊗v_t⊗w_t over F2 and a nonzero
linear functional ell on one slot, restricting that slot to ker(ell) kills
exactly the terms whose slot factor is the projective vector ell. If ell
appears m times in one slot, the restricted tensor has a rank-(23-m)
decomposition. In particular:
  m >= 4 gives a length <=19 Wang codim-1 core and hence R_F2(T<3,3,3>) <= 22
       after adding the removed rank-3 slice;
  m == 3 gives a length-20 core seed, one term away from the critical length.

This script scans all locally available exact rank-23 schemes it can parse,
including FMM JSON/Mathematica/reduced schemes, QMM files produced in this
research, and Palladin challenge reproductions. It verifies every parsed F2
scheme against the 729 Brent identities before using it.

Conventions
-----------
this investigation's tensor convention is C index c = 3*i + k for output C_{ik}.
Some upstream files use the transposed C-factor convention z_{ki}, i.e. c =
3*k + i. We test both and convert accepted schemes into this investigation convention
before applying Wang restrictions.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import re
import sys
import zipfile
from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np

ROOT = Path.cwd()
OUTDIR = Path("data/rank23_restriction_scan")
FMM_ROOT = Path(os.environ.get("FMM_ROOT", ""))
PALLADIN_ZIP_DEFAULT = Path(
    "Knowledge/objects/code/palladin-sat-challenges--4dd5c4c398ad--888477704863/"
    "originals/palladin-sat-challenges-27c77e14ec33ebfc6321d4f717274f124874a3f1.zip"
)

MASKS = [
    (1, "E11"),
    (10, "E12+E21"),
    (84, "E13+E22+E31"),
]
SLOT_NAMES = ["A", "B", "C"]

# ---------- F2 tensor utilities ----------

def bitvec_to_mask(v: Sequence[int]) -> int:
    mask = 0
    for i, x in enumerate(v):
        if int(x) & 1:
            mask |= 1 << i
    return mask


def mask_to_vec(mask: int, n: int = 9) -> List[int]:
    return [(mask >> i) & 1 for i in range(n)]


def transpose_3x3_mask(mask: int) -> int:
    out = 0
    for i in range(3):
        for j in range(3):
            if (mask >> (3 * i + j)) & 1:
                out |= 1 << (3 * j + i)
    return out


def build_T_session() -> np.ndarray:
    """T[a,b,c] with A_{ij}, B_{jk}, C_{ik} all row-major."""
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1
    return T


def build_T_fmm_c_transposed() -> np.ndarray:
    """T[a,b,c] with C factor ordered z_{ki}, as in many Brent-equation papers."""
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * k + i] = 1
    return T


def apply_constraint_tensor(T: np.ndarray, mask: int, slot: int) -> Tuple[np.ndarray, int, List[int]]:
    """Apply an F2 one-functional constraint to one mode; return core."""
    pivot = mask.bit_length() - 1
    free_bits = mask ^ (1 << pivot)
    result = T.copy()
    for i in range(9):
        if (free_bits >> i) & 1:
            if slot == 0:
                result[i, :, :] ^= result[pivot, :, :]
            elif slot == 1:
                result[:, i, :] ^= result[:, pivot, :]
            else:
                result[:, :, i] ^= result[:, :, pivot]
    if slot == 0:
        result[pivot, :, :] = 0
        keep = [i for i in range(9) if i != pivot]
        core = result[keep, :, :]
    elif slot == 1:
        result[:, pivot, :] = 0
        keep = [i for i in range(9) if i != pivot]
        core = result[:, keep, :]
    else:
        result[:, :, pivot] = 0
        keep = [i for i in range(9) if i != pivot]
        core = result[:, :, keep]
    return core, pivot, keep


def project_factor(mask_value: int, ell: int) -> Tuple[int, bool, int, List[int]]:
    """Apply constraint ell to one 9-bit factor and drop pivot coordinate.
    Returns (8-bit projected mask, killed?, pivot, keep_indices).
    """
    pivot = ell.bit_length() - 1
    free_bits = ell ^ (1 << pivot)
    bits = mask_to_vec(mask_value, 9)
    for i in range(9):
        if (free_bits >> i) & 1:
            bits[i] ^= bits[pivot]
    bits[pivot] = 0
    keep = [i for i in range(9) if i != pivot]
    out = 0
    for pos, old in enumerate(keep):
        if bits[old]:
            out |= 1 << pos
    return out, out == 0, pivot, keep


def reconstruct_from_masks(terms: Sequence[Tuple[int, int, int]]) -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for a, b, c in terms:
        avec = np.array(mask_to_vec(a, 9), dtype=np.uint8)
        bvec = np.array(mask_to_vec(b, 9), dtype=np.uint8)
        cvec = np.array(mask_to_vec(c, 9), dtype=np.uint8)
        T ^= (avec[:, None, None] & bvec[None, :, None] & cvec[None, None, :])
    return T


def verify_terms_session(terms: Sequence[Tuple[int, int, int]]) -> Tuple[bool, str, int]:
    """Verify and, if necessary, transpose C into research convention.

    Returns (ok, convention, mismatch_count). convention is one of:
      research: already uses C_{ik};
      c_transposed_input: input uses z_{ki}, returned terms must have C transposed.
    """
    T_s = build_T_session()
    R = reconstruct_from_masks(terms)
    if np.array_equal(R, T_s):
        return True, "research", 0
    T_t = build_T_fmm_c_transposed()
    if np.array_equal(R, T_t):
        return True, "c_transposed_input", 0
    return False, "invalid", int(np.sum(R ^ T_s))


def convert_terms_to_session(terms: Sequence[Tuple[int, int, int]], convention: str) -> List[Tuple[int, int, int]]:
    if convention == "research":
        return list(terms)
    if convention == "c_transposed_input":
        return [(a, b, transpose_3x3_mask(c)) for a, b, c in terms]
    raise ValueError(convention)


def verify_restricted_terms(
    full_terms_session: Sequence[Tuple[int, int, int]], slot: int, ell: int
) -> Tuple[bool, int, int]:
    """Verify the restricted decomposition against the corresponding restricted core.
    Returns (ok, raw_length, effective_length_after_exact_duplicate_cancellation).
    """
    T = build_T_session()
    core, pivot, keep = apply_constraint_tensor(T, ell, slot)
    shape = core.shape
    recon = np.zeros(shape, dtype=np.uint8)
    restricted_triples = []
    for a, b, c in full_terms_session:
        masks = [a, b, c]
        proj, killed, _, _ = project_factor(masks[slot], ell)
        if killed:
            continue
        masks8 = list(masks)
        masks8[slot] = proj
        restricted_triples.append(tuple(masks8))
        vecs = []
        for s, m in enumerate(masks8):
            vecs.append(np.array(mask_to_vec(m, 8 if s == slot else 9), dtype=np.uint8))
        if slot == 0:
            recon ^= (vecs[0][:, None, None] & vecs[1][None, :, None] & vecs[2][None, None, :])
        elif slot == 1:
            recon ^= (vecs[0][:, None, None] & vecs[1][None, :, None] & vecs[2][None, None, :])
        else:
            recon ^= (vecs[0][:, None, None] & vecs[1][None, :, None] & vecs[2][None, None, :])
    # exact duplicate cancellation in F2
    counts = Counter(restricted_triples)
    effective = sum(v & 1 for v in counts.values())
    return bool(np.array_equal(recon, core)), len(restricted_triples), effective


def scheme_hash(terms: Sequence[Tuple[int, int, int]]) -> str:
    payload = "\n".join(f"{a},{b},{c}" for a, b, c in terms).encode()
    return hashlib.sha256(payload).hexdigest()

# ---------- parsers ----------

@dataclass
class SchemeRecord:
    name: str
    source: str
    terms: List[Tuple[int, int, int]]  # in source convention before verification conversion
    parser: str
    metadata: Dict[str, Any]


def parse_qmm(path: Path, name: Optional[str] = None) -> SchemeRecord:
    terms: List[Tuple[int, int, int]] = []
    cur: Dict[str, List[int]] = {}
    idx = None
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.startswith("term "):
            if {"u", "v", "w"} <= cur.keys():
                terms.append((bitvec_to_mask(cur["u"]), bitvec_to_mask(cur["v"]), bitvec_to_mask(cur["w"])))
            cur = {}
            idx = int(line.split()[1])
        elif line.startswith("u "):
            cur["u"] = [abs(int(x)) % 2 for x in line.split()[1:]]
        elif line.startswith("v "):
            cur["v"] = [abs(int(x)) % 2 for x in line.split()[1:]]
        elif line.startswith("w "):
            cur["w"] = [abs(int(x)) % 2 for x in line.split()[1:]]
    if {"u", "v", "w"} <= cur.keys():
        terms.append((bitvec_to_mask(cur["u"]), bitvec_to_mask(cur["v"]), bitvec_to_mask(cur["w"])))
    return SchemeRecord(name or path.stem, str(path), terms, "qmm", {})


def parse_value(x: Any) -> Any:
    if isinstance(x, str):
        f = Fraction(x)
        return f.numerator if f.denominator == 1 else f
    return x


def parse_reduced_vars(fresh_vars: List[dict], real_variables: int) -> Dict[int, List[dict]]:
    parsed: Dict[int, List[dict]] = {}
    for i, fresh_var in enumerate(fresh_vars):
        idx = real_variables + i
        parsed[idx] = fresh_var
        parsed[-idx] = [{"index": variable["index"], "value": -variable["value"]} for variable in fresh_var]
    return parsed


def replace_fresh_vars(expression: List[dict], fresh_vars: Dict[int, List[dict]], value: Any = 1) -> List[Tuple[int, Any]]:
    replaced: List[Tuple[int, Any]] = []
    for variable in expression:
        var_index = variable["index"]
        var_value = variable["value"] * value
        if var_index in fresh_vars:
            replaced.extend(replace_fresh_vars(fresh_vars[var_index], fresh_vars, var_value))
        else:
            replaced.append((var_index, var_value))
    return replaced


def parse_json_scheme(path: Path, name: Optional[str] = None) -> SchemeRecord:
    data = json.loads(path.read_text())
    n = data["n"]
    if isinstance(n, int):
        n1 = n2 = n3 = n
    else:
        n1, n2, n3 = n
    assert [n1, n2, n3] == [3, 3, 3], path
    m = data["m"]
    assert m == 23, (path, m)

    if path.name.lower().endswith("reduced.json"):
        u = [[0 for _ in range(n1 * n2)] for _ in range(m)]
        v = [[0 for _ in range(n2 * n3)] for _ in range(m)]
        w = [[0 for _ in range(n3 * n1)] for _ in range(m)]
        u_vars = parse_reduced_vars(data["u_fresh"], real_variables=n1 * n2)
        v_vars = parse_reduced_vars(data["v_fresh"], real_variables=n2 * n3)
        w_vars = parse_reduced_vars(data["w_fresh"], real_variables=m)
        for index, expr in enumerate(data["u"]):
            for var, val in replace_fresh_vars(expr, u_vars, 1):
                u[index][var] += val
        for index, expr in enumerate(data["v"]):
            for var, val in replace_fresh_vars(expr, v_vars, 1):
                v[index][var] += val
        # reduced w is output-coordinate -> expression in product indices
        for coord, expr in enumerate(data["w"]):
            for var, val in replace_fresh_vars(expr, w_vars, 1):
                w[var][coord] += val
    else:
        u = [[parse_value(x) for x in row] for row in data["u"]]
        v = [[parse_value(x) for x in row] for row in data["v"]]
        w = [[parse_value(x) for x in row] for row in data["w"]]
    terms = [(bitvec_to_mask(row), bitvec_to_mask(v[i]), bitvec_to_mask(w[i])) for i, row in enumerate(u)]
    return SchemeRecord(name or path.stem, str(path), terms, "json" + ("_reduced" if path.name.lower().endswith("reduced.json") else ""), {"complexity": data.get("complexity"), "z2": data.get("z2")})


def parse_mathematica_scheme(path: Path, name: Optional[str] = None) -> SchemeRecord:
    text = path.read_text(encoding="utf-8").replace("{", "[").replace("}", "]")
    text = re.sub(r"(-?\d+/\d+)", r'Fraction("\1")', text)
    data = eval(text, {"Fraction": Fraction})  # controlled local corpus of numeric lists
    terms = []
    for triad in data:
        u_mat, v_mat, w_mat = triad
        u = [u_mat[i][j] for i in range(3) for j in range(3)]
        v = [v_mat[i][j] for i in range(3) for j in range(3)]
        w = [w_mat[i][j] for i in range(3) for j in range(3)]
        terms.append((bitvec_to_mask(u), bitvec_to_mask(v), bitvec_to_mask(w)))
    return SchemeRecord(name or path.stem, str(path), terms, "mathematica_m", {})


def parse_palladin_md_zip(zip_path: Path) -> List[SchemeRecord]:
    records: List[SchemeRecord] = []
    with zipfile.ZipFile(zip_path) as z:
        names = [n for n in z.namelist() if n.endswith(".md") and "mm23_complete_reproduction" in n]
        for n in sorted(names):
            text = z.read(n).decode("utf-8", errors="replace")
            m = re.search(r"## Machine-readable masks\s*```text\s*(.*?)\s*```", text, flags=re.S)
            if not m:
                continue
            terms: List[Tuple[int, int, int]] = []
            for line in m.group(1).splitlines():
                line = line.strip()
                mm = re.match(r"(\d+)\s*:\s*(\d+)\s+(\d+)\s+(\d+)", line)
                if mm:
                    terms.append((int(mm.group(2)), int(mm.group(3)), int(mm.group(4))))
            if terms:
                base = Path(n).stem
                records.append(SchemeRecord(base, f"{zip_path}!{n}", terms, "palladin_md_masks", {}))
    return records


def discover_fmm_records(fmm_root: Path) -> List[SchemeRecord]:
    records: List[SchemeRecord] = []
    status = fmm_root / "schemes/status.json"
    if not status.exists():
        return records
    obj = json.loads(status.read_text())
    seen = set()
    for ring, arr in obj["3x3x3"]["schemes"].items():
        for entry in arr:
            path = fmm_root / entry["path"]
            # Use status normalized paths when available; they are full schemes.
            if not path.exists():
                path = fmm_root / entry.get("source", "")
            if not path.exists() or path in seen:
                continue
            seen.add(path)
            name = f"FMM_{ring}_{path.stem}"
            try:
                if path.suffix.lower() == ".json":
                    rec = parse_json_scheme(path, name=name)
                elif path.suffix.lower() == ".m":
                    rec = parse_mathematica_scheme(path, name=name)
                elif path.suffix.lower() in [".txt", ".mpl"]:
                    # skip for now unless direct parser needed
                    continue
                else:
                    continue
                rec.metadata.update({"ring_bucket": ring, "status_entry": entry})
                records.append(rec)
            except Exception as e:
                records.append(SchemeRecord(name, str(path), [], "parse_error", {"error": repr(e), "ring_bucket": ring, "status_entry": entry}))
    # Add some source duplicates not in status if they carry different tensors.
    extras = [
        "schemes/known/a_60_addition/3x3x3_m23_additions60_ZT.json",
        "schemes/results/addition_reduced_ZT/3x3x3_m23_cr58_cn119_ZT_reduced.json",
        "schemes/results/addition_reduced_ZT/3x3x3_m23_cr58_cn120_ZT_reduced.json",
        "schemes/results/addition_reduced_ZT/3x3x3_m23_cr58_cn122_ZT_reduced.json",
        "schemes/results/addition_reduced_ZT/3x3x3_m23_cr60_cn97_ZT_reduced.json",
        "schemes/results/serendipitous_base/3x3x3_m23_8d34d377660f8f8d8b32cd4b6a1e1c40a5093dd0_ZT.json",
        "schemes/results/naive_addition_reduced_ZT/3x3x3_m23_c88_ZT.json",
        "schemes/known/alpha_tensor/3x3x3_m23_Z.json",
        "schemes/known/classic/Laderman-333-23-98.m",
        "schemes/known/classic/Smirnov-333-23-139.m",
    ]
    for rel in extras:
        path = fmm_root / rel
        if not path.exists() or path in seen:
            continue
        try:
            if path.suffix.lower() == ".json":
                rec = parse_json_scheme(path, name="FMM_extra_" + path.stem)
            else:
                rec = parse_mathematica_scheme(path, name="FMM_extra_" + path.stem)
            rec.metadata.update({"extra_relpath": rel})
            records.append(rec)
            seen.add(path)
        except Exception as e:
            records.append(SchemeRecord("FMM_extra_" + path.stem, str(path), [], "parse_error", {"error": repr(e)}))
    return records


def discover_qmm_records() -> List[SchemeRecord]:
    paths = [
        Path("data/cn122_3x3_r23_repro/scheme.qmm"),
        Path("data/fmm_r23_schemes/serendipitous_8d34.qmm"),
        Path("data/fmm_r23_schemes/naive_c88.qmm"),
    ]
    records = []
    for p in paths:
        if p.exists() and p.stat().st_size > 0:
            records.append(parse_qmm(p, name="QMM_" + p.parent.name + "_" + p.stem))
    return records

# ---------- scanning ----------

def multiset_after_duplicate_cancellation(terms: Sequence[Tuple[int, int, int]]) -> Tuple[int, int, Dict[str, int]]:
    """Effective full-scheme length over F2 after exact duplicate triple cancellation."""
    counts = Counter(terms)
    eff = sum(v & 1 for v in counts.values())
    dup = {f"{k[0]},{k[1]},{k[2]}": v for k, v in counts.items() if v > 1}
    return len(terms), eff, dup


def scan_record(rec: SchemeRecord, materialize_limit: int = 50) -> Dict[str, Any]:
    out: Dict[str, Any] = {
        "name": rec.name,
        "source": rec.source,
        "parser": rec.parser,
        "metadata": rec.metadata,
        "term_count": len(rec.terms),
    }
    if not rec.terms:
        out["valid"] = False
        out["error"] = rec.metadata.get("error", "no terms")
        return out
    ok, conv, mismatch = verify_terms_session(rec.terms)
    out["input_convention"] = conv
    out["initial_mismatch_to_session"] = mismatch
    if not ok:
        out["valid"] = False
        return out
    terms = convert_terms_to_session(rec.terms, conv)
    ok2, conv2, mismatch2 = verify_terms_session(terms)
    out["post_conversion_convention_check"] = {"ok": ok2, "conv": conv2, "mismatch": mismatch2}
    raw_len, eff_len, dup = multiset_after_duplicate_cancellation(terms)
    out["valid"] = bool(ok2 and conv2 == "research" and eff_len == 23)
    out["session_hash"] = scheme_hash(terms)
    out["raw_length"] = raw_len
    out["effective_full_length_after_duplicate_cancellation"] = eff_len
    out["duplicate_full_triples"] = dup
    if not out["valid"]:
        return out

    # Multiplicity distribution for every nonzero projective factor in each slot.
    slot_summaries = []
    best_events: List[Dict[str, Any]] = []
    materialized: List[Dict[str, Any]] = []
    for slot in range(3):
        counts = Counter(t[slot] for t in terms)
        counts.pop(0, None)  # should not happen for valid rank-one terms
        max_mult = max(counts.values()) if counts else 0
        hist = Counter(counts.values())
        events = []
        for ell, cnt in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])):
            if cnt >= 3:
                verified, raw_restr_len, eff_restr_len = verify_restricted_terms(terms, slot, ell)
                event = {
                    "slot": SLOT_NAMES[slot],
                    "slot_index": slot,
                    "functional_mask": ell,
                    "functional_binary": f"0b{ell:09b}",
                    "multiplicity": cnt,
                    "restricted_raw_length": raw_restr_len,
                    "restricted_effective_length": eff_restr_len,
                    "restricted_verified": verified,
                    "decisive_rank22_if_length_le_19": eff_restr_len <= 19,
                    "length20_seed": eff_restr_len == 20,
                    "term_indices_killed_0_based": [i for i, t in enumerate(terms) if t[slot] == ell],
                }
                events.append(event)
                best_events.append(event | {"scheme": rec.name})
                if len(materialized) < materialize_limit and (eff_restr_len <= 20 or cnt >= 3):
                    materialized.append(event)
        slot_summaries.append({
            "slot": SLOT_NAMES[slot],
            "max_multiplicity": max_mult,
            "multiplicity_histogram": dict(sorted((str(k), v) for k, v in hist.items())),
            "num_distinct_projective_factors": len(counts),
            "events_multiplicity_at_least_3": events,
        })
    out["slot_summaries"] = slot_summaries
    out["best_events"] = best_events
    return out


def write_seed_json(rec: SchemeRecord, scan: Dict[str, Any], outdir: Path) -> int:
    if not scan.get("valid"):
        return 0
    terms = convert_terms_to_session(rec.terms, scan["input_convention"])
    count = 0
    seeds_dir = outdir / "seeds"
    seeds_dir.mkdir(parents=True, exist_ok=True)
    for event in scan.get("best_events", []):
        if event["restricted_effective_length"] > 20:
            continue
        slot = event["slot_index"]
        ell = event["functional_mask"]
        restricted = []
        for i, (a, b, c) in enumerate(terms):
            masks = [a, b, c]
            proj, killed, pivot, keep = project_factor(masks[slot], ell)
            if killed:
                continue
            masks[slot] = proj
            restricted.append({
                "source_term_index_0_based": i,
                "u": mask_to_vec(masks[0], 8 if slot == 0 else 9),
                "v": mask_to_vec(masks[1], 8 if slot == 1 else 9),
                "w": mask_to_vec(masks[2], 8 if slot == 2 else 9),
                "masks": masks,
            })
        # cancel exact duplicate restricted triples over F2 for a minimal explicit seed list
        grouped = defaultdict(list)
        for t in restricted:
            grouped[tuple(t["masks"])].append(t)
        reduced = []
        canceled_groups = []
        for key, arr in grouped.items():
            if len(arr) & 1:
                reduced.append(arr[0])
            if len(arr) > 1:
                canceled_groups.append({"masks": list(key), "count": len(arr), "source_indices": [x["source_term_index_0_based"] for x in arr]})
        payload = {
            "scheme": scan["name"],
            "source": scan["source"],
            "scheme_hash": scan["session_hash"],
            "slot": event["slot"],
            "slot_index": slot,
            "functional_mask": ell,
            "functional_binary": f"0b{ell:09b}",
            "pivot": ell.bit_length() - 1,
            "killed_term_indices_0_based": event["term_indices_killed_0_based"],
            "raw_restricted_terms": restricted,
            "reduced_restricted_terms_after_duplicate_cancellation": reduced,
            "canceled_duplicate_groups": canceled_groups,
            "restricted_effective_length": event["restricted_effective_length"],
            "restricted_verified": event["restricted_verified"],
            "note": "All factor vectors are in research convention C_{ik}; restricted slot has dimension 8 after dropping the pivot coordinate.",
        }
        safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", scan["name"])
        path = seeds_dir / f"{safe}_{event['slot']}_ell{ell:03d}_len{event['restricted_effective_length']}.json"
        path.write_text(json.dumps(payload, indent=2) + "\n")
        count += 1
    return count


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--fmm-root", default=os.environ.get("FMM_ROOT", ""), help="FastMatrixMultiplication checkout root")
    ap.add_argument("--palladin-zip", default=str(PALLADIN_ZIP_DEFAULT))
    ap.add_argument("--outdir", default=str(OUTDIR))
    args = ap.parse_args()

    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    records: List[SchemeRecord] = []
    if args.fmm_root:
        records.extend(discover_fmm_records(Path(os.path.expandvars(args.fmm_root))))
    records.extend(discover_qmm_records())
    pzip = Path(args.palladin_zip)
    if pzip.exists():
        records.extend(parse_palladin_md_zip(pzip))

    # Deduplicate exact research-convention schemes, but keep aliases.
    scans = []
    hash_to_first: Dict[str, str] = {}
    aliases: Dict[str, List[str]] = defaultdict(list)
    rec_by_name = {r.name: r for r in records}

    for rec in records:
        scan = scan_record(rec)
        if scan.get("valid"):
            h = scan["session_hash"]
            if h in hash_to_first:
                aliases[hash_to_first[h]].append(scan["name"])
                scan["duplicate_of"] = hash_to_first[h]
            else:
                hash_to_first[h] = scan["name"]
        scans.append(scan)

    # Materialize seeds for all valid schemes, including duplicates because names map to distinct provenance.
    seed_count = 0
    for rec, scan in zip(records, scans):
        seed_count += write_seed_json(rec, scan, outdir)

    valid_scans = [s for s in scans if s.get("valid")]
    invalid_scans = [s for s in scans if not s.get("valid")]
    all_events = []
    for s in valid_scans:
        for e in s.get("best_events", []):
            ee = dict(e)
            ee["scheme"] = s["name"]
            ee["source"] = s["source"]
            ee["scheme_hash"] = s["session_hash"]
            all_events.append(ee)

    top_events = sorted(all_events, key=lambda e: (e["restricted_effective_length"], -e["multiplicity"], e["scheme"], e["slot"], e["functional_mask"]))
    decisive = [e for e in top_events if e["restricted_effective_length"] <= 19]
    length20 = [e for e in top_events if e["restricted_effective_length"] == 20]

    max_by_slot = {slot: 0 for slot in SLOT_NAMES}
    hist_by_slot = {slot: Counter() for slot in SLOT_NAMES}
    for s in valid_scans:
        for slot_summary in s.get("slot_summaries", []):
            slot = slot_summary["slot"]
            max_by_slot[slot] = max(max_by_slot[slot], slot_summary["max_multiplicity"])
            for k, v in slot_summary["multiplicity_histogram"].items():
                hist_by_slot[slot][int(k)] += v

    summary = {
        "records_loaded": len(records),
        "valid_rank23_f2_schemes": len(valid_scans),
        "unique_valid_session_hashes": len(hash_to_first),
        "invalid_or_unusable_records": len(invalid_scans),
        "aliases_by_first_hash_name": {k: v for k, v in aliases.items() if v},
        "seed_files_written": seed_count,
        "max_multiplicity_by_slot": max_by_slot,
        "aggregate_multiplicity_histogram_by_slot": {k: dict(sorted((str(kk), vv) for kk, vv in c.items())) for k, c in hist_by_slot.items()},
        "num_events_multiplicity_at_least_3": len(all_events),
        "num_decisive_length_le_19_events": len(decisive),
        "num_length20_seed_events": len(length20),
        "best_restricted_events_first_100": top_events[:100],
        "decisive_events": decisive,
        "length20_events_first_200": length20[:200],
        "source_classes": dict(Counter(s.get("parser", "") for s in scans)),
    }

    (outdir / "scan_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (outdir / "scan_records.json").write_text(json.dumps(scans, indent=2) + "\n")
    (outdir / "length20_events.json").write_text(json.dumps(length20, indent=2) + "\n")
    (outdir / "decisive_length_le19_events.json").write_text(json.dumps(decisive, indent=2) + "\n")

    print(json.dumps(summary, indent=2))
    if decisive:
        print("DECISIVE length <=19 restricted core found; inspect seeds/ and verify as rank-22 F2 upper bound.", file=sys.stderr)
    elif length20:
        print(f"Found {len(length20)} length-20 core seeds; inspect seeds/ for one-term-away search starts.", file=sys.stderr)
    else:
        print("No multiplicity-3 or -4 events found in valid local corpus.", file=sys.stderr)

if __name__ == "__main__":
    main()
