#!/usr/bin/env python3
"""analysis: cross-test face proof-core row sets on multiple face supports.

For the three DRAT-verified support faces (original J65 and two analysis faces),
load the representative complete-Wang rows that occurred in each extracted input
core.  Test whether one face's row set, pairwise intersections, the triple
intersection, or the union already exclude the other faces when restricted to
that face.  This asks whether the proofs share a reusable occupation mechanism
or are mostly face-specific.

CP-SAT statuses here are exploratory unless replayed as CNF/DRAT.  FEASIBLE
supports are rescanned against the complete table to show how far the subset is
from the full occupation problem.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints, complete_core_wang_scan  # noqa: E402
from cert_trace_separator import full_violation_scan  # noqa: E402

LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
OUTDIR = ROOT / "workspace/data/face_core"
INPUTS = {
    "J65_original": ROOT / "workspace/data/jface_core/J65_core_used_constraints.pkl",
    "transJ65_random630631": ROOT / "workspace/data/face_core/transJ65_random630631_used_constraints.pkl",
    "transJ65_random630632": ROOT / "workspace/data/face_core/transJ65_random630632_used_constraints.pkl",
}


def row_points(rec):
    pts = []
    bs = int(rec["point_bitset"])
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())
        bs ^= bit
    return pts


def load_face_data():
    faces = {}
    for name, path in INPUTS.items():
        with path.open("rb") as f:
            d = pickle.load(f)
        rows = set(int(r["representative_full_source"]["row_index"]) for r in d["used_constraints"])
        faces[name] = {"J": set(map(int, d["J"])), "rows": rows, "path": str(path)}
    return faces


def solve_subset_on_face(records, row_ids, J, solver_time, workers, seed, label):
    from ortools.sat.python import cp_model
    t0 = time.time()
    J = sorted(set(map(int, J)))
    Jset = set(J)
    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in J}
    model.Add(sum(x.values()) == 19)
    added = 0
    skipped = 0
    by_dim = Counter()
    by_L = Counter()
    inter_hist = Counter()
    for rid in sorted(row_ids):
        rec = records[int(rid)]
        cap = 19 - int(rec["L"])
        pts = [p for p in row_points(rec) if p in Jset]
        if len(pts) <= cap:
            skipped += 1
            continue
        model.Add(sum(x[p] for p in pts) <= cap)
        added += 1
        by_dim[int(rec["dim8"])] += 1
        by_L[int(rec["L"])] += 1
        inter_hist[len(pts)] += 1
    build_sec = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(solver_time)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = int(seed)
    ts = time.time()
    st = solver.Solve(model)
    solve_sec = time.time() - ts
    status = solver.StatusName(st)
    out = {
        "label": label,
        "J_size": len(J),
        "row_ids_available": len(row_ids),
        "constraints_added_after_face_restriction": added,
        "rows_skipped_pop_le_cap_on_face": skipped,
        "added_by_dim8": {str(k): int(v) for k, v in sorted(by_dim.items())},
        "added_by_L": {str(k): int(v) for k, v in sorted(by_L.items())},
        "restricted_size_hist": {str(k): int(v) for k, v in sorted(inter_hist.items())},
        "build_sec": round(build_sec, 3),
        "status": status,
        "solve_sec": round(solve_sec, 3),
    }
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        support = [p for p in J if solver.Value(x[p])]
        scan = complete_core_wang_scan(label + "_subset_solution", support, 19, records, max_head=10)
        fullscan = full_violation_scan(support, records, 19)
        out["solution"] = {
            "A_cols": support,
            "complete_wang_violation_count": int(scan["complete_violation_count"]),
            "violations_by_dim8": scan.get("violations_by_dim8"),
            "violations_by_L": scan.get("violations_by_L"),
            "complete_wang_violation_count_with_points": int(fullscan["complete_violation_count"]),
            "first_violations": fullscan.get("violations", [])[:5],
        }
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--solver-time", type=float, default=30.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=640164)
    args = ap.parse_args()
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    faces = load_face_data()
    lut, lut_meta = load_lut(LUT_PATH)
    records, complete_meta = build_core_constraints(CoreQuotient(1), lut)
    names = list(faces)
    row_sets = {}
    for name in names:
        row_sets[f"core_of_{name}"] = set(faces[name]["rows"])
    row_sets["intersection_all_three"] = set.intersection(*(faces[n]["rows"] for n in names))
    row_sets["recurring_at_least_two"] = set(r for r in set.union(*(faces[n]["rows"] for n in names)) if sum(r in faces[n]["rows"] for n in names) >= 2)
    row_sets["union_all_three"] = set.union(*(faces[n]["rows"] for n in names))
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            row_sets[f"intersection_{names[i]}__{names[j]}"] = faces[names[i]]["rows"] & faces[names[j]]["rows"]
    # Test a focused set of combinations.  Union is included to check whether simply merging proof-core rows is strong.
    tests = []
    for rs_name in [
        "intersection_all_three",
        "recurring_at_least_two",
        "union_all_three",
        *[f"core_of_{n}" for n in names],
        *[f"intersection_{names[i]}__{names[j]}" for i in range(len(names)) for j in range(i + 1, len(names))],
    ]:
        for face_name in names:
            label = f"{rs_name}_on_{face_name}"
            print("test", label, "rows", len(row_sets[rs_name]), "J", len(faces[face_name]["J"]), flush=True)
            tests.append(solve_subset_on_face(records, row_sets[rs_name], faces[face_name]["J"], args.solver_time, args.workers, args.seed, label))
    payload = {
        "schema": "core_row_cross_tests_v1",
        "meaning": "CP-SAT cross-tests of proof-core row sets across the three verified support faces. The tests probe recurrence of an occupation mechanism; only statuses replayed through CNF/DRAT would be theorem-level.",
        "parameters": {"solver_time": args.solver_time, "workers": args.workers, "seed": args.seed},
        "face_info": {name: {"J_size": len(d["J"]), "row_count": len(d["rows"]), "source": d["path"]} for name, d in faces.items()},
        "row_set_sizes": {name: len(rows) for name, rows in row_sets.items()},
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "complete_meta": complete_meta,
        "tests": tests,
        "status_matrix": {t["label"]: t["status"] for t in tests},
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = OUTDIR / "core_row_cross_tests.json"
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    status_counts = Counter(t["status"] for t in tests)
    print(json.dumps({
        "out": str(out),
        "row_set_sizes": payload["row_set_sizes"],
        "status_counts": {str(k): int(v) for k, v in sorted(status_counts.items())},
        "infeasible_labels": [t["label"] for t in tests if t["status"] == "INFEASIBLE"],
        "feasible_labels_head": [t["label"] for t in tests if t["status"] in ("FEASIBLE", "OPTIMAL")][:10],
        "elapsed_sec": payload["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
