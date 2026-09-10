#!/usr/bin/env python3
"""analysis: test whether one (or k) outside-J point suffices to escape J65.

The analysis proof gives no complete-Wang support with all 19 points in J.  A
stronger and more structural question is whether a support can have at most k
points outside J.  If complete-Wang occupation plus distinctness is infeasible
with sum_{p outside J} x_p <= k, then every complete-Wang support satisfies

    sum_{p outside J} x_p >= k+1,

or equivalently sum_{p in J} x_p <= 18-k.  This CP-SAT script is not a proof;
it searches for a support or supplies a target for a future replayable CNF/DRAT
certificate.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints, complete_core_wang_scan, saturation_domains, transversal_failures  # noqa: E402
from candidate_source_qcut_scan import eval_candidate_sources  # noqa: E402
from quotient_rank_cuts import build_contractions, point_mask_for_q  # noqa: E402
from cert_trace_separator import full_violation_scan  # noqa: E402
from trace_dependency_family import dot8, eval_support_local_dependency, trace_mask_correct  # noqa: E402
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from fixed_A_saturation import contraction_matrix, mat_rank_f2  # noqa: E402

GLOBAL_PATH = ROOT / "workspace/data/local_hull/global_fractional_solution.json"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
OUTDIR = ROOT / "workspace/data/j_escape"


def load_J(tol: float):
    d = json.loads(GLOBAL_PATH.read_text())
    x = np.array(d["global_lp"]["x_full"], dtype=float)
    J = [p for p in range(1, 256) if x[p - 1] > tol]
    outside = [p for p in range(1, 256) if x[p - 1] <= tol]
    return x, J, outside, d


def points_from_bitset(bs: int):
    pts = []
    bs = int(bs)
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())
        bs ^= bit
    return pts


def build_phi(T_core: np.ndarray):
    phi = {}
    for q in range(1, 1 << 8):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) == 9:
            inv = gf2_mat_inv(M)
            if inv is None:
                raise RuntimeError(q)
            phi[int(q)] = trace_mask_correct(inv)
    return phi


def main():
    from ortools.sat.python import cp_model

    ap = argparse.ArgumentParser()
    ap.add_argument("--max-outside", type=int, default=1)
    ap.add_argument("--solver-time", type=float, default=300.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=630701)
    ap.add_argument("--tol", type=float, default=1e-10)
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    if args.out is None:
        args.out = OUTDIR / f"complete_wang_max_outside_{args.max_outside}_300s.json"
    args.out.parent.mkdir(parents=True, exist_ok=True)
    s = 19
    xfrac, J, outside, global_data = load_J(args.tol)
    Jset = set(J)
    outside_set = set(outside)
    points = list(range(1, 256))
    lut, lut_meta = load_lut(LUT_PATH)
    records, complete_meta = build_core_constraints(CoreQuotient(1), lut)
    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in points}
    model.Add(sum(x[p] for p in points) == s)
    model.Add(sum(x[p] for p in outside) <= int(args.max_outside))
    row_count = 0
    row_by_dim = Counter()
    row_by_L = Counter()
    trivial_size_le_cap = 0
    for rec in records:
        L = int(rec["L"])
        cap = s - L
        pts = points_from_bitset(int(rec["point_bitset"]))
        if len(pts) <= cap:
            trivial_size_le_cap += 1
            continue
        model.Add(sum(x[p] for p in pts) <= cap)
        row_count += 1
        row_by_dim[int(rec["dim8"])] += 1
        row_by_L[L] += 1
    build_sec = time.time() - t0
    print(json.dumps({
        "J_size": len(J), "outside_size": len(outside), "max_outside": args.max_outside,
        "wang_rows_added": row_count,
        "row_by_dim": {str(k): int(v) for k, v in sorted(row_by_dim.items())},
        "row_by_L": {str(k): int(v) for k, v in sorted(row_by_L.items())},
        "build_sec": round(build_sec, 3),
    }, indent=2)[:5000], flush=True)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = int(args.workers)
    solver.parameters.random_seed = int(args.seed)
    ts = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - ts
    status_name = solver.StatusName(status)
    result = {
        "schema": "j_escape_cpsat_v1",
        "meaning": "CP-SAT support search for complete E11 Wang distinct 19-supports with at most k points outside the analysis J face. INFEASIBLE is not proof until replayed; FEASIBLE gives an A-support candidate for fixed-A tests.",
        "field": "F2",
        "core": "E11 quotient core",
        "rank_s": s,
        "global_fractional_solution_file": str(GLOBAL_PATH),
        "J_size": len(J),
        "J_points": J,
        "outside_size": len(outside),
        "outside_points": outside,
        "parameters": {"max_outside": args.max_outside, "solver_time": args.solver_time, "workers": args.workers, "seed": args.seed, "tol": args.tol},
        "fractional_mass_on_J": float(sum(xfrac[p - 1] for p in J)),
        "fractional_outside_mass": float(sum(xfrac[p - 1] for p in outside)),
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "complete_meta": complete_meta,
        "constraint_summary": {
            "wang_rows_added": row_count,
            "trivial_size_le_cap_rows": trivial_size_le_cap,
            "wang_rows_by_dim": {str(k): int(v) for k, v in sorted(row_by_dim.items())},
            "wang_rows_by_L": {str(k): int(v) for k, v in sorted(row_by_L.items())},
        },
        "build_sec": round(build_sec, 3),
        "status": status_name,
        "solve_sec": round(solve_sec, 3),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A = [p for p in points if solver.Value(x[p])]
        outside_selected = [p for p in A if p in outside_set]
        T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
        contractions = build_contractions(T_core)
        masks = {q: point_mask_for_q(q) for q in contractions}
        scan = complete_core_wang_scan(f"j_escape_k{args.max_outside}_solution", A, s, records, max_head=40)
        scan_with_points = full_violation_scan(A, records, s)
        sat = saturation_domains(T_core, A)
        trans = transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=20)
        qscan = eval_candidate_sources(f"j_escape_k{args.max_outside}_solution", A, contractions, masks, max_source_size=2, max_store=20)
        phi = build_phi(T_core)
        trace_dep = eval_support_local_dependency(A, sorted(phi), phi, {p: None for p in points})
        result["solution"] = {
            "A_cols": A,
            "outside_selected": outside_selected,
            "outside_selected_count": len(outside_selected),
            "complete_wang_scan": scan,
            "complete_wang_violation_count_with_points": scan_with_points["complete_violation_count"],
            "zero_domain_terms": len(sat["summary"]["zero_domain_terms"]),
            "linear_pass": sat["summary"]["linear_membership"]["necessary_linear_test_passed"],
            "affine_dim": sat["summary"]["linear_membership"].get("affine_solution_dimension_if_consistent"),
            "saturated_contractions": sat["summary"].get("saturated_contraction_count"),
            "transversal_failures": trans["failure_count_reported"],
            "quotient_rank_violations_size2": qscan["violated_guarded_instances"],
            "trace_local_dependency": trace_dep,
        }
    result["elapsed_sec"] = round(time.time() - t0, 3)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(args.out),
        "status": status_name,
        "solve_sec": result["solve_sec"],
        "solution": result.get("solution", {}).get("A_cols"),
        "outside_selected": result.get("solution", {}).get("outside_selected"),
        "complete_violations": result.get("solution", {}).get("complete_wang_scan", {}).get("complete_violation_count"),
        "linear_pass": result.get("solution", {}).get("linear_pass"),
        "trace_bad": result.get("solution", {}).get("trace_local_dependency", {}).get("exact_local_inconsistent_terms"),
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
