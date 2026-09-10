#!/usr/bin/env python3
"""analysis: CP-SAT test of a support face from any saved fractional LP run.

Given a JSON file with `runs[*].nonzero_coordinates` or a direct x-vector, let J
be the positive support of the chosen fractional point.  The model asks whether a
binary distinct 19-point E11 A-support contained in J satisfies the complete
417,199-row Wang occupation table.  A feasible support is immediately rescanned
against the full table and passed through the existing fixed-A necessary tests.
An infeasible CP-SAT status is useful search evidence; a mathematical cut still
requires a replayable CNF/DRAT proof.
"""
from __future__ import annotations

import argparse
import json
import pickle
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
from trace_dependency_family import eval_support_local_dependency, trace_mask_correct  # noqa: E402
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from fixed_A_saturation import contraction_matrix, mat_rank_f2  # noqa: E402

OUTDIR = ROOT / "workspace/data/face_loop"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
DEFAULT_TARGET = ROOT / "workspace/data/j65_transport/lp_with_transported_J65_cuts.json"


def load_target(path: Path, run_index: int, tol: float):
    d = json.loads(path.read_text())
    if "runs" in d:
        run = d["runs"][run_index]
        coords = run.get("nonzero_coordinates")
        if coords is None:
            x = np.array(run["x_full"], dtype=float)
        else:
            x = np.zeros(255, dtype=float)
            for p, v in coords:
                x[int(p) - 1] = float(v)
        label = f"{path.stem}_run{run_index}_{run.get('objective_kind','unknown')}_{run.get('seed','noseed')}"
    elif "global_lp" in d and "x_full" in d["global_lp"]:
        x = np.array(d["global_lp"]["x_full"], dtype=float)
        label = f"{path.stem}_global_lp"
    elif "x_full" in d:
        x = np.array(d["x_full"], dtype=float)
        label = f"{path.stem}_xfull"
    else:
        raise ValueError(f"Unsupported target format: {path}")
    J = [p for p in range(1, 256) if x[p - 1] > tol]
    return d, x, J, label


def points_from_bitset_intersect(bs: int, allowed: set[int]):
    pts = []
    bs = int(bs)
    while bs:
        bit = bs & -bs
        p = bit.bit_length()
        if p in allowed:
            pts.append(p)
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
    ap.add_argument("--target", type=Path, default=DEFAULT_TARGET)
    ap.add_argument("--run-index", type=int, default=1)
    ap.add_argument("--tol", type=float, default=1e-9)
    ap.add_argument("--solver-time", type=float, default=180.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=630901)
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    source, xfrac, J, label = load_target(args.target, args.run_index, args.tol)
    if args.out is None:
        args.out = OUTDIR / f"face_cpsat_{label}_tol{args.tol:g}.json"
    args.out.parent.mkdir(parents=True, exist_ok=True)
    Jset = set(J)
    s = 19
    lut, lut_meta = load_lut(LUT_PATH)
    records, complete_meta = build_core_constraints(CoreQuotient(1), lut)
    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in J}
    model.Add(sum(x[p] for p in J) == s)
    row_count = 0
    row_by_dim = Counter()
    row_by_L = Counter()
    trivial_pop_le_cap = 0
    empty_intersection = 0
    impossible_empty = 0
    for rec in records:
        L = int(rec["L"])
        cap = s - L
        pts = points_from_bitset_intersect(int(rec["point_bitset"]), Jset)
        if not pts:
            if cap < 0:
                impossible_empty += 1
                model.AddBoolOr([])
            else:
                empty_intersection += 1
            continue
        if len(pts) <= cap:
            trivial_pop_le_cap += 1
            continue
        model.Add(sum(x[p] for p in pts) <= cap)
        row_count += 1
        row_by_dim[int(rec["dim8"])] += 1
        row_by_L[L] += 1
    build_sec = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = int(args.workers)
    solver.parameters.random_seed = int(args.seed)
    ts = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - ts
    status_name = solver.StatusName(status)
    result = {
        "schema": "general_face_cpsat_v1",
        "meaning": "Complete-Wang binary support-face test for a saved fractional LP support J. Feasible gives an A-support candidate for fixed-A tests; INFEASIBLE is not a theorem until encoded with replayable proof.",
        "target_file": str(args.target),
        "target_run_index": args.run_index,
        "target_label": label,
        "tol": args.tol,
        "J_size": len(J),
        "J_points": J,
        "fractional_sum": float(xfrac.sum()),
        "fractional_mass_on_J": float(sum(xfrac[p - 1] for p in J)),
        "parameters": {"solver_time": args.solver_time, "workers": args.workers, "seed": args.seed},
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "complete_meta": complete_meta,
        "constraint_summary": {
            "wang_rows_added": row_count,
            "wang_rows_by_dim": {str(k): int(v) for k, v in sorted(row_by_dim.items())},
            "wang_rows_by_L": {str(k): int(v) for k, v in sorted(row_by_L.items())},
            "empty_intersection_rows": empty_intersection,
            "trivial_pop_le_cap_rows": trivial_pop_le_cap,
            "impossible_empty_rows": impossible_empty,
        },
        "build_sec": round(build_sec, 3),
        "status": status_name,
        "solve_sec": round(solve_sec, 3),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A = [p for p in J if solver.Value(x[p])]
        T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
        contractions = build_contractions(T_core)
        masks = {q: point_mask_for_q(q) for q in contractions}
        scan = complete_core_wang_scan(label + "_solution", A, s, records, max_head=40)
        scan_with_points = full_violation_scan(A, records, s)
        sat = saturation_domains(T_core, A)
        trans = transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=20)
        qscan = eval_candidate_sources(label + "_solution", A, contractions, masks, max_source_size=2, max_store=20)
        phi = build_phi(T_core)
        trace_dep = eval_support_local_dependency(A, sorted(phi), phi, {p: None for p in range(1, 256)})
        result["solution"] = {
            "A_cols": A,
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
        "J_size": len(J),
        "rows_added": row_count,
        "status": status_name,
        "solve_sec": result["solve_sec"],
        "solution": result.get("solution", {}).get("A_cols"),
        "complete_violations": result.get("solution", {}).get("complete_wang_scan", {}).get("complete_violation_count"),
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
