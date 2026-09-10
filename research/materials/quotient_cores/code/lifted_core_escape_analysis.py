#!/usr/bin/env python3
"""analysis: how can supports escape the lifted J65 proof-core rows?

The lifted proof-core row set (9,469 full Wang rows) plus exact cardinality and
all outside-J zero units is DRAT-verified UNSAT.  This script removes those unit
assumptions and asks CP-SAT how many outside-J points are needed to satisfy the
same lifted row set.  The result is exploratory unless later converted to a
replayable proof for a chosen bound.
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

from complete_core_and_transversal import ROOT, complete_core_wang_scan, saturation_domains, transversal_failures, build_core_constraints  # noqa: E402
from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from candidate_source_qcut_scan import eval_candidate_sources  # noqa: E402
from quotient_rank_cuts import build_contractions, point_mask_for_q  # noqa: E402
from cert_trace_separator import full_violation_scan  # noqa: E402
from trace_dependency_family import eval_support_local_dependency, trace_mask_correct  # noqa: E402
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from fixed_A_saturation import contraction_matrix, mat_rank_f2  # noqa: E402

import numpy as np

USED_PKL = ROOT / "workspace/data/jface_core/J65_core_used_constraints.pkl"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
OUTDIR = ROOT / "workspace/data/lifted_jcore"


def full_points_from_bitset(bs: int) -> list[int]:
    pts = []
    bs = int(bs)
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())
        bs ^= bit
    return pts


def load_row_list():
    with USED_PKL.open("rb") as f:
        payload = pickle.load(f)
    J = [int(p) for p in payload["J"]]
    outside = [int(p) for p in payload["outside"]]
    full_rows = {}
    for rec in payload["used_constraints"]:
        src = rec["representative_full_source"]
        bs = int(src["full_point_bitset"])
        cap = int(src["cap"])
        key = (bs, cap)
        if key not in full_rows:
            full_rows[key] = {
                "full_point_bitset": bs,
                "cap": cap,
                "row_index": int(src["row_index"]),
                "key8": int(src["key8"]),
                "dim8": int(src["dim8"]),
                "L": int(src["L"]),
            }
    rows = sorted(full_rows.values(), key=lambda r: (r["cap"], r["full_point_bitset"].bit_count(), r["full_point_bitset"]))
    return J, outside, rows


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


def solve_model(rows, J, outside, mode: str, max_outside: int | None, fixed_allowed: set[int] | None, time_limit: float, seed: int, workers: int):
    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    points = list(range(1, 256))
    x = {p: model.NewBoolVar(f"x_{p}") for p in points}
    model.Add(sum(x[p] for p in points) == 19)
    outside_set = set(outside)
    if mode == "minimize_outside":
        model.Minimize(sum(x[p] for p in outside))
    elif mode == "max_outside":
        if max_outside is None:
            raise ValueError("max_outside required")
        model.Add(sum(x[p] for p in outside) <= int(max_outside))
    elif mode == "face_allowed":
        if fixed_allowed is None:
            raise ValueError("fixed_allowed required")
        allowed = set(J).union(fixed_allowed)
        for p in points:
            if p not in allowed:
                model.Add(x[p] == 0)
    else:
        raise ValueError(mode)
    row_count = 0
    by_cap = Counter()
    by_dim = Counter()
    for r in rows:
        pts = full_points_from_bitset(r["full_point_bitset"])
        if len(pts) <= int(r["cap"]):
            continue
        model.Add(sum(x[p] for p in pts) <= int(r["cap"]))
        row_count += 1
        by_cap[int(r["cap"])] += 1
        by_dim[int(r["dim8"])] += 1
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.random_seed = int(seed)
    solver.parameters.num_search_workers = int(workers)
    t0 = time.time()
    status = solver.Solve(model)
    elapsed = time.time() - t0
    out = {"status": solver.StatusName(status), "solve_sec": round(elapsed, 3), "row_count": row_count, "row_by_cap": {str(k): int(v) for k, v in sorted(by_cap.items())}, "row_by_dim": {str(k): int(v) for k, v in sorted(by_dim.items())}}
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A = [p for p in points if solver.Value(x[p])]
        out.update({
            "A_cols": A,
            "outside_selected": [p for p in A if p in outside_set],
            "outside_selected_count": sum(1 for p in A if p in outside_set),
            "objective_value": None if mode != "minimize_outside" else float(solver.ObjectiveValue()),
        })
    return out


def run_fixed_A_checks(A, label: str):
    lut, _ = load_lut(LUT_PATH)
    records, _ = build_core_constraints(CoreQuotient(1), lut)
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}
    scan = complete_core_wang_scan(label, A, 19, records, max_head=30)
    scan_with_points = full_violation_scan(A, records, 19)
    sat = saturation_domains(T_core, A)
    trans = transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=20)
    qscan = eval_candidate_sources(label, A, contractions, masks, max_source_size=2, max_store=20)
    phi = build_phi(T_core)
    trace_dep = eval_support_local_dependency(A, sorted(phi), phi, {p: None for p in range(1, 256)})
    return {
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--time", type=float, default=120.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=630771)
    ap.add_argument("--singleton-limit", type=int, default=0, help="optionally test first N outside singletons J union {q}")
    args = ap.parse_args()
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    J, outside, rows = load_row_list()
    minres = solve_model(rows, J, outside, "minimize_outside", None, None, args.time, args.seed, args.workers)
    print(json.dumps({"minimize_outside": {k: minres.get(k) for k in ["status", "objective_value", "outside_selected_count", "outside_selected", "solve_sec"]}}, indent=2), flush=True)
    if minres.get("A_cols"):
        minres["fixed_A_checks"] = run_fixed_A_checks(minres["A_cols"], "lifted_core_min_outside_solution")
    max0 = solve_model(rows, J, outside, "max_outside", 0, None, args.time, args.seed + 1, args.workers)
    max1 = solve_model(rows, J, outside, "max_outside", 1, None, args.time, args.seed + 2, args.workers)
    singleton_results = []
    for i, q in enumerate(outside[: max(0, args.singleton_limit)]):
        r = solve_model(rows, J, outside, "face_allowed", None, {q}, min(30.0, args.time), args.seed + 1000 + i, args.workers)
        singleton_results.append({"q": int(q), **{k: r.get(k) for k in ["status", "solve_sec", "outside_selected", "outside_selected_count", "A_cols"]}})
        print("singleton", q, r.get("status"), r.get("outside_selected"), flush=True)
    result = {
        "schema": "lifted_core_escape_analysis_v1",
        "meaning": "CP-SAT exploration of the 9,469 lifted Wang rows that appear in the J65 proof input core, after removing outside-zero assumptions. This shows whether those rows alone force more than one outside-J point or which outside directions can escape. Not proof unless separately encoded and DRAT-verified.",
        "J_size": len(J),
        "outside_size": len(outside),
        "row_count": len(rows),
        "parameters": {"time": args.time, "workers": args.workers, "seed": args.seed, "singleton_limit": args.singleton_limit},
        "minimize_outside": minres,
        "max_outside_0": max0,
        "max_outside_1": max1,
        "singleton_results": singleton_results,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = OUTDIR / "lifted_core_escape_analysis.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "min_status": minres.get("status"),
        "min_outside": minres.get("outside_selected_count"),
        "min_outside_points": minres.get("outside_selected"),
        "max0_status": max0.get("status"),
        "max1_status": max1.get("status"),
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
