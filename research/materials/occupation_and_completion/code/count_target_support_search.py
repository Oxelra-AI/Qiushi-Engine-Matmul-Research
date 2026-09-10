#!/usr/bin/env python3
"""analysis: point-level E11 complete-Wang support search in targeted count branches.

This complements the fixed-count moment tests.  A feasible moment witness is not a
support; this script asks the original 255 Boolean question under selected orbit
count vectors:

    choose 19 distinct nonzero projected A-directions in F_2^8
    satisfying all complete E11 Wang occupation rows.

The script can add already sound support-level cuts (transported face cuts,
overlap cuts) and contraction lower bounds.  CP-SAT statuses remain search
evidence, not proof artifacts; any found support is rescanned against the full
417,199-row table and then should go into fixed-A/B/C completion.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, List

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import (  # noqa: E402
    build_core_constraints,
    complete_core_wang_scan,
    saturation_domains,
    transversal_failures,
)
from candidate_source_qcut_scan import eval_candidate_sources  # noqa: E402
from quotient_rank_cuts import build_contractions, point_mask_for_q  # noqa: E402
from cert_trace_separator import full_violation_scan  # noqa: E402
from trace_dependency_family import dot8  # noqa: E402
from overlap_cut_separator import load_overlap_centers, support_bitset, overlap_summary  # noqa: E402
from transport_face_families_search import mask_from_points, points_from_mask  # noqa: E402
from rlt_pair_lift import build_stabilizer, compute_point_orbits  # noqa: E402

LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
FACE_FAMILY = ROOT / "workspace/data/transported_faces/transported_face_families.json"
OVERLAP_PATH = ROOT / "workspace/data/transported_overlap/transported_overlap_analysis.json"
OUT = ROOT / "workspace/data/count_target_support_search"

DEFAULT_COUNTS = [
    # Surviving fixed-count+block-total+PSD witnesses from analysis.
    [0, 0, 3, 5, 4, 7],
    [1, 0, 3, 6, 2, 7],
    [1, 0, 4, 5, 2, 7],
    # analysis closest complete-Wang near-support count (10 violations).
    [3, 0, 15, 1, 0, 0],
]


def pts_from_bitset(bs: int) -> List[int]:
    pts = []
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())
        bs ^= bit
    return pts


def parse_counts(text: str | None) -> list[list[int]]:
    if not text:
        return [list(c) for c in DEFAULT_COUNTS]
    out = []
    for block in text.split(";"):
        if not block.strip():
            continue
        vals = [int(x) for x in block.replace(",", " ").split()]
        if len(vals) != 6 or sum(vals) != 19:
            raise ValueError(f"bad count vector {block!r}: {vals}")
        out.append(vals)
    return out


def load_face_masks(max_cuts: int | None = None) -> list[int]:
    if not FACE_FAMILY.exists():
        return []
    d = json.loads(FACE_FAMILY.read_text())
    masks = []
    for rec in d.get("cuts", []):
        masks.append(mask_from_points(rec["points"]))
        if max_cuts is not None and len(masks) >= max_cuts:
            break
    return sorted(set(masks))


def load_layer_hints():
    path = ROOT / "workspace/data/global_layer_sweep/global_layer_sweep.json"
    hints = []
    if not path.exists():
        return hints
    d = json.loads(path.read_text())
    for rec in d.get("results", []):
        sol = rec.get("solution")
        if sol and sol.get("A_cols"):
            hints.append({"name": rec.get("name"), "points": [int(p) for p in sol["A_cols"]], "complete_violations": sol.get("complete_wang_violation_count")})
    return hints


def count_of_support(points: Iterable[int], pt_orb, K=6):
    c = [0] * K
    for p in points:
        c[int(pt_orb[int(p)])] += 1
    return c


def add_complete_wang_rows(model, x, records):
    row_count = 0; row_dim = Counter(); row_L = Counter(); row_cap = Counter(); skipped = 0
    for rec in records:
        L = int(rec["L"]); cap = 19 - L
        pts = pts_from_bitset(int(rec["point_bitset"]))
        if len(pts) <= cap:
            skipped += 1
            continue
        model.Add(sum(x[p] for p in pts) <= cap)
        row_count += 1
        row_dim[int(rec.get("dim8", -1))] += 1
        row_L[L] += 1
        row_cap[cap] += 1
    return {
        "rows_added": int(row_count),
        "skipped_trivial": int(skipped),
        "by_dim8": {str(k): int(v) for k, v in sorted(row_dim.items())},
        "by_L": {str(k): int(v) for k, v in sorted(row_L.items())},
        "by_cap": {str(k): int(v) for k, v in sorted(row_cap.items())},
    }


def solve_one(n_vec, records, pt_orb, point_orbits, face_masks, overlap_masks, contractions, masks_by_q, hints, args):
    from ortools.sat.python import cp_model
    t0 = time.time()
    model = cp_model.CpModel()
    points = list(range(1, 256))
    x = {p: model.NewBoolVar(f"x_{p}") for p in points}
    model.Add(sum(x[p] for p in points) == 19)
    for a, orb in enumerate(point_orbits):
        model.Add(sum(x[int(p)] for p in orb) == int(n_vec[a]))

    wang_summary = add_complete_wang_rows(model, x, records)

    face_count = 0
    for m in face_masks:
        model.Add(sum(x[p] for p in points_from_mask(m)) <= 18)
        face_count += 1

    overlap_count = 0
    for m in overlap_masks:
        model.Add(sum(x[p] for p in points_from_mask(m)) <= 15)
        overlap_count += 1

    contraction_count = 0; contraction_hist = Counter()
    if args.include_contractions:
        for q, c in contractions.items():
            rk = int(c["rank"])
            if rk > 0:
                qpts = [p for p in points if dot8(int(q), p)]
                model.Add(sum(x[p] for p in qpts) >= rk)
                contraction_count += 1
                contraction_hist[rk] += 1

    # Add hints matching this count if available; CP-SAT accepts multiple AddHint calls only per variable,
    # so choose the first matching hint.
    used_hint = None
    for h in hints:
        if count_of_support(h["points"], pt_orb, len(point_orbits)) == list(n_vec):
            hs = set(h["points"])
            for p in points:
                model.AddHint(x[p], 1 if p in hs else 0)
            used_hint = h
            break

    # Deterministic objective to steer to reproducible corners, while still searching feasibility.
    if args.objective == "random":
        seed = int(args.seed + sum((i + 1) * v for i, v in enumerate(n_vec)))
        model.Minimize(sum(((p * 1103515245 + seed) % 1009) * x[p] for p in points))
    elif args.objective == "lex":
        model.Minimize(sum(p * x[p] for p in points))
    elif args.objective == "none":
        pass
    else:
        raise ValueError(args.objective)

    build_sec = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = int(args.workers)
    solver.parameters.random_seed = int(args.seed)
    if args.log_search:
        solver.parameters.log_search_progress = True
    ts = time.time(); st = solver.Solve(model); solve_sec = time.time() - ts
    status = solver.StatusName(st)
    rec = {
        "n": list(map(int, n_vec)),
        "status": status,
        "build_sec": round(build_sec, 3),
        "solve_sec": round(solve_sec, 3),
        "constraints": {
            "complete_wang": wang_summary,
            "fixed_count_equalities": len(point_orbits),
            "transported_face_cuts": face_count,
            "overlap_cuts": overlap_count,
            "contraction_lower_bounds": contraction_count,
            "contraction_rank_hist": {str(k): int(v) for k, v in sorted(contraction_hist.items())},
        },
        "used_hint": used_hint,
    }
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A = [p for p in points if solver.Value(x[p])]
        scan = complete_core_wang_scan("count_target_solution", A, 19, records, max_head=40)
        fullscan = full_violation_scan(A, records, 19)
        sat = saturation_domains(np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2, A)
        trans = transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=10)
        qscan = eval_candidate_sources("count_target_solution", A, contractions, masks_by_q, max_source_size=2, max_store=20)
        face_overlaps = [(m & mask_from_points(A)).bit_count() for m in face_masks]
        overlap_summ = overlap_summary(A, overlap_masks) if overlap_masks else None
        rec["solution"] = {
            "A_cols": A,
            "counts_by_point_orbit": count_of_support(A, pt_orb, len(point_orbits)),
            "objective_value": None if args.objective == "none" else float(solver.ObjectiveValue()),
            "complete_wang_violation_count": int(scan["complete_violation_count"]),
            "complete_wang_scan_head": scan,
            "complete_wang_violation_count_with_points": int(fullscan["complete_violation_count"]),
            "first_violations_with_points": fullscan.get("violations", [])[:20],
            "max_transported_face_overlap": max(face_overlaps) if face_overlaps else None,
            "tight_transported_face_cuts": sum(1 for v in face_overlaps if v == 18),
            "overlap_summary": overlap_summ,
            "fixed_A_checks": {
                "zero_domain_terms": len(sat["summary"]["zero_domain_terms"]),
                "linear_membership_pass": sat["summary"]["linear_membership"]["necessary_linear_test_passed"],
                "affine_solution_dimension_if_consistent": sat["summary"]["linear_membership"].get("affine_solution_dimension_if_consistent"),
                "saturated_contraction_count": sat["summary"].get("saturated_contraction_count"),
                "transversal_failures_reported": trans["failure_count_reported"],
                "quotient_rank_violations_size2": qscan["violated_guarded_instances"],
            },
        }
    rec["elapsed_sec"] = round(time.time() - t0, 3)
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--counts", type=str, default=None, help="semicolon-separated count vectors, e.g. '0,0,3,5,4,7;3,0,15,1,0,0'")
    ap.add_argument("--solver-time", type=float, default=300.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=700070)
    ap.add_argument("--objective", choices=["random", "lex", "none"], default="random")
    ap.add_argument("--include-faces", action="store_true")
    ap.add_argument("--max-face-cuts", type=int, default=None)
    ap.add_argument("--include-overlap", action="store_true")
    ap.add_argument("--include-contractions", action="store_true")
    ap.add_argument("--log-search", action="store_true")
    ap.add_argument("--out", type=Path, default=OUT / "targeted_count_support_search.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    counts = parse_counts(args.counts)
    print("analysis: targeted point-level complete-Wang support search", flush=True)
    print(f"  counts={counts}", flush=True)

    perms = build_stabilizer()
    pt_orb, point_orbits = compute_point_orbits(perms)
    point_sizes = [len(o) for o in point_orbits]
    lut, lut_meta = load_lut(LUT_PATH)
    records, complete_meta = build_core_constraints(CoreQuotient(1), lut)
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    masks_by_q = {q: point_mask_for_q(q) for q in contractions}
    face_masks = load_face_masks(args.max_face_cuts) if args.include_faces else []
    overlap_masks = []
    overlap_meta = None
    if args.include_overlap:
        centers, overlap_meta = load_overlap_centers(OVERLAP_PATH, None)
        overlap_masks = [support_bitset(c) for c in centers]
    hints = load_layer_hints()
    print(f"  records={len(records)}, faces={len(face_masks)}, overlaps={len(overlap_masks)}, hints={len(hints)}", flush=True)

    results = []
    for i, n in enumerate(counts):
        print(f"  solve {i+1}/{len(counts)} n={n}", flush=True)
        rec = solve_one(n, records, pt_orb, point_orbits, face_masks, overlap_masks, contractions, masks_by_q, hints, args)
        results.append(rec)
        print(json.dumps({"n": n, "status": rec["status"], "solve_sec": rec["solve_sec"], "viol": rec.get("solution", {}).get("complete_wang_violation_count"), "fixedA": rec.get("solution", {}).get("fixed_A_checks")}, sort_keys=True)[:4000], flush=True)

    payload = {
        "schema": "count_target_support_search_v1",
        "meaning": "Point-level CP-SAT search for actual distinct 19-direction E11 A-supports under targeted orbit counts. Solver statuses are not mathematical proof unless separately certified; any found support is fully rescanned and locally checked.",
        "field": "F2",
        "core": "E11 quotient distinct projected-A branch",
        "parameters": {
            "counts": counts,
            "solver_time": args.solver_time,
            "workers": args.workers,
            "seed": args.seed,
            "objective": args.objective,
            "include_faces": bool(args.include_faces),
            "max_face_cuts": args.max_face_cuts,
            "include_overlap": bool(args.include_overlap),
            "include_contractions": bool(args.include_contractions),
        },
        "point_orbit_sizes": point_sizes,
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "complete_meta": complete_meta,
        "overlap_meta": overlap_meta,
        "status_counts": {str(k): int(v) for k, v in sorted(Counter(r["status"] for r in results).items())},
        "results": results,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(args.out),
        "status_counts": payload["status_counts"],
        "solutions": [r.get("solution", {}).get("complete_wang_violation_count") for r in results if "solution" in r],
        "elapsed_sec": payload["elapsed_sec"],
    }, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
