#!/usr/bin/env python3
"""analysis: map a general face DRAT input core back to restricted and full Wang rows.

This regenerates the clause stream produced by general_face_cnf.py for a
chosen target/run face, matches the drat-trim input core as a multiset, and
records which restricted complete-Wang constraints contributed clauses.  The
result is explanatory evidence about the face proof mechanism; it is not a new
mathematical statement beyond the verified CNF/DRAT proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Sequence

import numpy as np
from pysat.card import CardEnc, EncType

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints  # noqa: E402

DEFAULT_TARGET = ROOT / "workspace/data/j65_transport/lp_with_transported_J65_cuts.json"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
OUTDIR = ROOT / "workspace/data/face_core"


def sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def sha_payload(obj) -> str:
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def norm_clause(clause: Sequence[int]) -> tuple[int, ...]:
    return tuple(sorted(int(x) for x in clause if int(x) != 0))


def parse_dimacs(path: Path) -> tuple[Counter, dict]:
    counts = Counter()
    header = None
    nclauses_seen = 0
    empty = 0
    max_abs = 0
    with path.open("r") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p"):
                parts = line.split()
                header = {"format": parts[1], "variables": int(parts[2]), "clauses": int(parts[3])}
                continue
            cur = []
            for token in line.split():
                lit = int(token)
                if lit == 0:
                    break
                cur.append(lit)
                max_abs = max(max_abs, abs(lit))
            key = norm_clause(cur)
            if not key:
                empty += 1
            counts[key] += 1
            nclauses_seen += 1
    return counts, {"header": header, "clauses_seen": nclauses_seen, "empty_clause_count": empty, "max_abs_lit": max_abs, "sha256": sha256(path), "path": str(path)}


def gen_card(lits: Sequence[int], relation: str, bound: int, top: int):
    lits = list(map(int, lits))
    if relation == "atmost":
        if bound < 0:
            return top, [[]], 0
        if len(lits) <= bound:
            return top, [], 0
        if bound == 0:
            return top, [[-lit] for lit in lits], 0
        enc = CardEnc.atmost(lits=lits, bound=int(bound), top_id=int(top), encoding=EncType.seqcounter)
    elif relation == "equals":
        if bound < 0 or bound > len(lits):
            return top, [[]], 0
        enc = CardEnc.equals(lits=lits, bound=int(bound), top_id=int(top), encoding=EncType.seqcounter)
    else:
        raise ValueError(relation)
    new_top = max(int(top), int(enc.nv))
    return new_top, enc.clauses, max(0, new_top - int(top))


def load_x_and_label(path: Path, run_index: int, tol: float):
    d = json.loads(path.read_text())
    if "runs" in d:
        run = d["runs"][run_index]
        coords = run.get("nonzero_coordinates")
        if coords is not None:
            x = np.zeros(255, dtype=float)
            for p, v in coords:
                x[int(p) - 1] = float(v)
        elif "x_full" in run:
            x = np.array(run["x_full"], dtype=float)
        else:
            raise ValueError(f"run {run_index} has no coordinate data")
        label = f"{path.stem}_run{run_index}_{run.get('objective_kind', 'unknown')}_{run.get('seed', 'noseed')}"
        source_meta = {"run_index": run_index, "objective_kind": run.get("objective_kind"), "seed": run.get("seed"), "sum_x": run.get("sum_x")}
    elif "global_lp" in d and "x_full" in d["global_lp"]:
        x = np.array(d["global_lp"]["x_full"], dtype=float)
        label = f"{path.stem}_global_lp"
        source_meta = {"source_kind": "global_lp"}
    elif "x_full" in d:
        x = np.array(d["x_full"], dtype=float)
        label = f"{path.stem}_xfull"
        source_meta = {"source_kind": "x_full"}
    elif "J_points" in d:
        x = np.zeros(255, dtype=float)
        for p in d["J_points"]:
            x[int(p) - 1] = 1.0
        label = f"{path.stem}_Jpoints"
        source_meta = {"source_kind": "J_points"}
    else:
        raise ValueError(f"Unsupported target JSON: {path}")
    J = [p for p in range(1, 256) if x[p - 1] > tol]
    outside = [p for p in range(1, 256) if x[p - 1] <= tol]
    return d, x, J, outside, label, source_meta


def restrict_mask_to_J(point_bitset: int, full_to_local_bit: Dict[int, int], J_full_mask: int) -> int:
    bs = int(point_bitset) & J_full_mask
    out = 0
    while bs:
        bit = bs & -bs
        p = bit.bit_length()
        out |= 1 << full_to_local_bit[p]
        bs ^= bit
    return out


def local_points(mask: int, J: Sequence[int]) -> list[int]:
    pts = []
    bs = int(mask)
    while bs:
        bit = bs & -bs
        pts.append(int(J[bit.bit_length() - 1]))
        bs ^= bit
    return pts


def full_points(mask: int) -> list[int]:
    pts = []
    bs = int(mask)
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())
        bs ^= bit
    return pts


def build_constraints(J: Sequence[int]):
    lut, lut_meta = load_lut(LUT_PATH)
    records, complete_meta = build_core_constraints(CoreQuotient(1), lut)
    full_to_local_bit = {p: i for i, p in enumerate(J)}
    J_full_mask = 0
    for p in J:
        J_full_mask |= 1 << (p - 1)
    constraints_by_mask: Dict[int, int] = {}
    source_count_by_mask = Counter()
    min_source_count_by_mask = Counter()
    strongest_source_by_mask: Dict[int, dict] = {}
    min_sources_by_mask: Dict[int, list] = defaultdict(list)
    raw_relevant = 0
    skipped_pop_le_cap = 0
    zero_intersection = 0
    raw_by_dim = Counter()
    raw_by_L = Counter()
    for idx, rec in enumerate(records):
        L = int(rec["L"])
        cap = 19 - L
        if cap >= 19:
            continue
        mask = restrict_mask_to_J(int(rec["point_bitset"]), full_to_local_bit, J_full_mask)
        pop = mask.bit_count()
        if pop == 0:
            zero_intersection += 1
            continue
        if pop <= cap:
            skipped_pop_le_cap += 1
            continue
        raw_relevant += 1
        raw_by_dim[int(rec["dim8"])] += 1
        raw_by_L[L] += 1
        source_count_by_mask[mask] += 1
        src = {
            "row_index": int(idx),
            "key8": int(rec["key8"]),
            "dim8": int(rec["dim8"]),
            "L": L,
            "cap": int(cap),
            "restricted_size": int(pop),
            "full_size": int(int(rec["point_bitset"]).bit_count()),
            "full_point_bitset": int(rec["point_bitset"]),
        }
        if (mask not in constraints_by_mask) or cap < constraints_by_mask[mask]:
            constraints_by_mask[mask] = cap
            strongest_source_by_mask[mask] = src
            min_sources_by_mask[mask] = [src]
        elif cap == constraints_by_mask[mask] and len(min_sources_by_mask[mask]) < 8:
            min_sources_by_mask[mask].append(src)
    for idx, rec in enumerate(records):
        L = int(rec["L"])
        cap = 19 - L
        if cap >= 19:
            continue
        mask = restrict_mask_to_J(int(rec["point_bitset"]), full_to_local_bit, J_full_mask)
        if mask in constraints_by_mask and cap == constraints_by_mask[mask] and mask.bit_count() > cap:
            min_source_count_by_mask[mask] += 1
    constraints = [(mask, cap) for mask, cap in constraints_by_mask.items()]
    constraints.sort(key=lambda mc: (mc[1], mc[0].bit_count(), mc[0]))
    return records, complete_meta, lut_meta, constraints, strongest_source_by_mask, source_count_by_mask, min_source_count_by_mask, min_sources_by_mask, {
        "raw_relevant": int(raw_relevant),
        "zero_intersection": int(zero_intersection),
        "skipped_pop_le_cap": int(skipped_pop_le_cap),
        "raw_relevant_by_dim": {str(k): int(v) for k, v in sorted(raw_by_dim.items())},
        "raw_relevant_by_L": {str(k): int(v) for k, v in sorted(raw_by_L.items())},
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--target", type=Path, default=DEFAULT_TARGET)
    ap.add_argument("--run-index", type=int, default=1)
    ap.add_argument("--tol", type=float, default=1e-9)
    ap.add_argument("--name", type=str, default=None)
    ap.add_argument("--core", type=Path, default=None)
    ap.add_argument("--cnf", type=Path, default=None)
    ap.add_argument("--outdir", type=Path, default=OUTDIR)
    args = ap.parse_args()
    t0 = time.time()
    args.outdir.mkdir(parents=True, exist_ok=True)
    source, x, J, outside, label, source_meta = load_x_and_label(args.target, args.run_index, args.tol)
    name = args.name or f"{label}_J{len(J)}"
    if args.cnf is None:
        args.cnf = ROOT / "workspace/data/face_cnf" / f"{name}.cnf"
    if args.core is None:
        args.core = args.cnf.with_suffix(".input_core.cnf")
    core_counts, core_meta = parse_dimacs(args.core)
    core_total = sum(core_counts.values())
    records, complete_meta, lut_meta, constraints, strongest_source_by_mask, source_count_by_mask, min_source_count_by_mask, min_sources_by_mask, filter_counts = build_constraints(J)

    remaining = Counter(core_counts)
    top = len(J)
    generated_clause_count = 0
    matched_clause_count = 0
    exact19_core_clause_count = 0
    exact19_total_clause_count = 0
    row_clause_total = 0
    row_clause_core = 0
    exact19_aux = 0
    row_aux_total = 0
    used_by_constraint_index: dict[int, dict] = {}

    top, clauses, naux = gen_card(list(range(1, len(J) + 1)), "equals", 19, top)
    exact19_aux += naux
    exact19_total_clause_count += len(clauses)
    for cl in clauses:
        generated_clause_count += 1
        k = norm_clause(cl)
        if remaining.get(k, 0) > 0:
            remaining[k] -= 1
            matched_clause_count += 1
            exact19_core_clause_count += 1

    cap_hist = Counter()
    size_hist = Counter()
    for ci, (mask, cap) in enumerate(constraints):
        lits = []
        bs = int(mask)
        while bs:
            bit = bs & -bs
            lits.append(bit.bit_length())
            bs ^= bit
        old_top = top
        top, clauses, naux = gen_card(lits, "atmost", int(cap), top)
        cap_hist[int(cap)] += 1
        size_hist[len(lits)] += 1
        row_clause_total += len(clauses)
        row_aux_total += naux
        ccore = 0
        for cl in clauses:
            generated_clause_count += 1
            k = norm_clause(cl)
            if remaining.get(k, 0) > 0:
                remaining[k] -= 1
                matched_clause_count += 1
                row_clause_core += 1
                ccore += 1
        if ccore:
            src = strongest_source_by_mask[mask]
            used_by_constraint_index[ci] = {
                "constraint_index": int(ci),
                "core_clause_count": int(ccore),
                "total_clause_count": int(len(clauses)),
                "aux_vars": int(top - old_top),
                "cap": int(cap),
                "restricted_size": int(mask.bit_count()),
                "restricted_mask_hex": hex(int(mask)),
                "restricted_points_full_labels": local_points(mask, J),
                "source_count_same_restriction_all_caps": int(source_count_by_mask[mask]),
                "source_count_min_cap": int(min_source_count_by_mask[mask]),
                "representative_full_source": src,
                "representative_full_points": full_points(src["full_point_bitset"]),
                "min_source_examples": [
                    {k: v for k, v in src2.items() if k != "full_point_bitset"}
                    for src2 in min_sources_by_mask[mask]
                ],
            }
    unmatched = +remaining
    used_list = [used_by_constraint_index[i] for i in sorted(used_by_constraint_index)]
    full_row_ids = sorted({int(r["representative_full_source"]["row_index"]) for r in used_list})
    keyL_ids = sorted({(int(r["representative_full_source"]["key8"]), int(r["representative_full_source"]["L"])) for r in used_list})
    summary = {
        "schema": "face_input_core_clause_analysis_v1",
        "meaning": "Generated-clause/source mapping for a verified face proof. A used restricted constraint means at least one clause from its sequential at-most encoding appears in the drat-trim input core.",
        "target_file": str(args.target),
        "target_label": label,
        "source_meta": source_meta,
        "face_name": name,
        "tol": args.tol,
        "J_size": len(J),
        "J_points": J,
        "outside_size": len(outside),
        "target_mass_on_J": float(sum(x[p - 1] for p in J)),
        "target_total_mass": float(x.sum()),
        "core_cnf": core_meta,
        "original_cnf_path": str(args.cnf),
        "original_cnf_sha256": sha256(args.cnf),
        "complete_meta": complete_meta,
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "filter_counts_recomputed": filter_counts,
        "regenerated_encoding": {
            "final_top_variable": int(top),
            "generated_clause_count": int(generated_clause_count),
            "exact19_total_clause_count": int(exact19_total_clause_count),
            "exact19_aux_vars": int(exact19_aux),
            "row_clause_total": int(row_clause_total),
            "row_aux_total": int(row_aux_total),
            "unique_restricted_constraints": int(len(constraints)),
            "cap_hist_all_unique_restricted": {str(k): int(v) for k, v in sorted(cap_hist.items())},
            "restricted_size_hist_all_unique_restricted": {str(k): int(v) for k, v in sorted(size_hist.items())},
        },
        "matching": {
            "core_clause_total": int(core_total),
            "matched_clause_count": int(matched_clause_count),
            "unmatched_clause_count": int(sum(unmatched.values())),
            "unmatched_distinct_clause_count": int(len(unmatched)),
            "exact19_core_clause_count": int(exact19_core_clause_count),
            "row_core_clause_count": int(row_clause_core),
            "used_restricted_constraint_count": int(len(used_list)),
            "used_representative_full_row_count": int(len(full_row_ids)),
            "used_keyL_pair_count": int(len(keyL_ids)),
        },
        "used_constraint_histograms": {
            "by_cap": {str(k): int(v) for k, v in sorted(Counter(r["cap"] for r in used_list).items())},
            "by_restricted_size": {str(k): int(v) for k, v in sorted(Counter(r["restricted_size"] for r in used_list).items())},
            "by_full_dim8": {str(k): int(v) for k, v in sorted(Counter(r["representative_full_source"]["dim8"] for r in used_list).items())},
            "by_full_L": {str(k): int(v) for k, v in sorted(Counter(r["representative_full_source"]["L"] for r in used_list).items())},
        },
        "used_representative_full_row_ids_sha256": sha_payload(full_row_ids),
        "used_keyL_pairs_sha256": sha_payload(keyL_ids),
        "used_constraints_pickle": str(args.outdir / f"{name}_used_constraints.pkl"),
        "used_constraints_jsonl": str(args.outdir / f"{name}_used_constraints.jsonl"),
        "elapsed_sec": round(time.time() - t0, 3),
    }
    with (args.outdir / f"{name}_used_constraints.pkl").open("wb") as f:
        pickle.dump({"J": J, "outside": outside, "used_constraints": used_list, "summary": summary}, f, protocol=pickle.HIGHEST_PROTOCOL)
    with (args.outdir / f"{name}_used_constraints.jsonl").open("w") as f:
        for rec in used_list:
            slim = dict(rec)
            slim["representative_full_source"] = {k: v for k, v in slim["representative_full_source"].items() if k != "full_point_bitset"}
            f.write(json.dumps(slim, sort_keys=True) + "\n")
    out_summary = args.outdir / f"{name}_core_clause_analysis.json"
    out_summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "analysis": str(out_summary),
        "face_name": name,
        "J_size": len(J),
        "core_clauses": core_total,
        "matched": matched_clause_count,
        "unmatched": int(sum(unmatched.values())),
        "used_constraints": len(used_list),
        "used_hist_by_L": summary["used_constraint_histograms"]["by_full_L"],
        "used_hist_by_dim8": summary["used_constraint_histograms"]["by_full_dim8"],
        "elapsed_sec": summary["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
