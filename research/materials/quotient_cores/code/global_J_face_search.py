#!/usr/bin/env python3
"""analysis: global J-face support search for the saved fractional Wang-LP point.

The analysis LP point x has support J of 65 nonzero coordinates.  If x were a
convex combination of global binary Wang-admissible 19-supports, every support in
that combination would be contained in J, because x_p=0 outside J and mixture
weights are nonnegative.  This script therefore tests the *global* J face: is
there any distinct 19-point support contained in J satisfying the E11 core Wang
rows, optionally together with known necessary B/C compatibility cuts?

A found support is an actual Wang A-support candidate and is immediately rescanned
against the complete table and fixed-A necessary tests.  An INFEASIBLE CP-SAT
status is useful evidence but not a proof unless converted to a replayable SAT/PB
certificate.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import List, Sequence

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import ROOT, build_core_constraints, complete_core_wang_scan, saturation_domains, transversal_failures
from candidate_source_qcut_scan import eval_candidate_sources
from quotient_rank_cuts import build_contractions, point_mask_for_q
from cert_trace_separator import add_certificate_cuts, full_violation_scan
from distinct_trace_cut_cpsat import load_trace_cuts
from trace_dependency_family import dot8, eval_support_local_dependency, trace_mask_correct
from dual_basis_instrument import gf2_mat_inv
from fixed_A_saturation import contraction_matrix, mat_rank_f2
from overlap_cut_separator import load_overlap_centers, support_bitset, overlap_summary

OUTDIR = ROOT / "workspace/data/global_J_face"
GLOBAL_PATH = ROOT / "workspace/data/local_hull/global_fractional_solution.json"
REDUCED_PATH = ROOT / "workspace/data/reduced_wang/primitive_reduced_rows.pkl"
TRACE_CUT_JSON = ROOT / "workspace/data/trace_dependency_cuts/trace_dependency_cuts.json"
TRACE_SIZE5_PKL = ROOT / "workspace/data/trace_dependency_cuts/trace_dependency_size5_cuts.pkl"
CERT_CUT_PATH = ROOT / "workspace/data/trace_dependency_cuts/trace_certificate_family_cuts_augmented.json"
OVERLAP_PATH = ROOT / "workspace/data/transported_overlap/transported_overlap_analysis.json"


def load_J(tol: float = 1e-10):
    d = json.loads(GLOBAL_PATH.read_text())
    x = np.array(d["global_lp"]["x_full"], dtype=float)
    J = [p for p in range(1, 256) if x[p - 1] > tol]
    return x, J, d


def points_from_bitset_intersect(bs: int, allowed: set) -> List[int]:
    pts = []
    while bs:
        bit = bs & -bs
        p = bit.bit_length()
        if p in allowed:
            pts.append(p)
        bs ^= bit
    return pts


def load_reduced_keys():
    with REDUCED_PATH.open("rb") as f:
        red = pickle.load(f)
    return set(int(k) for k in red["kept_key8"]), red


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
    ap.add_argument("--solver-time", type=float, default=300.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=62065)
    ap.add_argument("--row-set", choices=["complete", "reduced"], default="complete")
    ap.add_argument("--contraction-lb", action="store_true")
    ap.add_argument("--use-overlap", action="store_true")
    ap.add_argument("--overlap-max", type=int, default=15)
    ap.add_argument("--trace-cuts", choices=["none", "minimal", "size5"], default="none")
    ap.add_argument("--max-size5-cuts", type=int, default=None)
    ap.add_argument("--cert-cuts", action="store_true")
    ap.add_argument("--max-certs", type=int, default=None)
    ap.add_argument("--out", type=Path, default=OUTDIR / "global_J_face_complete_wang.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    s = 19
    xfrac, J, global_data = load_J()
    Jset = set(J)
    points = list(range(1, 256))
    lut, lut_meta = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    records, complete_meta = build_core_constraints(CoreQuotient(1), lut)
    kept = None
    red = None
    if args.row_set == "reduced":
        kept, red = load_reduced_keys()
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}

    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in J}
    model.Add(sum(x[p] for p in J) == s)

    row_count = 0
    row_by_dim = Counter()
    row_by_L = Counter()
    immediate_empty = 0
    skipped_reduced = 0
    for rec in records:
        key = int(rec["key8"])
        if kept is not None and key not in kept:
            skipped_reduced += 1
            continue
        L = int(rec["L"])
        cap = s - L
        if cap >= s:
            continue
        pts = points_from_bitset_intersect(int(rec["point_bitset"]), Jset)
        # If no allowed points lie in the row, the inequality is trivial.
        if not pts:
            immediate_empty += 1
            continue
        model.Add(sum(x[p] for p in pts) <= cap)
        row_count += 1
        row_by_dim[int(rec["dim8"])] += 1
        row_by_L[L] += 1

    w = {}
    contraction_lb_count = 0
    contraction_rank_hist = Counter()
    if args.contraction_lb or args.trace_cuts != "none" or args.cert_cuts:
        for q, c in contractions.items():
            q = int(q)
            var = model.NewIntVar(0, s, f"w_{q}")
            w[q] = var
            model.Add(var == sum(x[p] for p in J if dot8(q, p)))
            rk = int(c["rank"])
            contraction_rank_hist[rk] += 1
            if args.contraction_lb and rk > 0:
                model.Add(var >= rk)
                contraction_lb_count += 1

    centers = []
    center_bits = []
    overlap_meta = {}
    overlap_count = 0
    if args.use_overlap:
        centers, overlap_meta = load_overlap_centers(OVERLAP_PATH, None)
        center_bits = [support_bitset(c) for c in centers]
        for c in centers:
            pts = [p for p in c if p in Jset]
            if pts:
                model.Add(sum(x[p] for p in pts) <= int(args.overlap_max))
                overlap_count += 1

    trace_cuts = load_trace_cuts(args.trace_cuts, TRACE_CUT_JSON, TRACE_SIZE5_PKL, args.max_size5_cuts)
    trace_hist = Counter()
    for cut in trace_cuts:
        p = int(cut["p"])
        H = [int(q) for q in cut["H"]]
        # If p outside J, x[p]=0, still the condition sum(w-9)>=0 is nontrivial: it forbids all H saturated.
        rhs_extra = x[p] if p in x else 0
        model.Add(sum(w[q] for q in H) >= 9 * len(H) + rhs_extra)
        trace_hist[len(H)] += 1

    cert_summary = None
    if args.cert_cuts:
        # Need a 255-key map for add_certificate_cuts.  Outside variables are fixed zero via constants.
        x_all = {p: (x[p] if p in x else 0) for p in points}
        cert_summary = add_certificate_cuts(model, x_all, w, contractions, args.max_certs, CERT_CUT_PATH)

    build_sec = time.time() - t0
    print(json.dumps({
        "J_size": len(J), "row_set": args.row_set, "row_count": row_count,
        "row_by_dim": {str(k): int(v) for k, v in sorted(row_by_dim.items())},
        "row_by_L": {str(k): int(v) for k, v in sorted(row_by_L.items())},
        "contraction_lb_count": contraction_lb_count,
        "overlap_count": overlap_count,
        "trace_cuts": len(trace_cuts),
        "cert_summary": cert_summary,
        "build_sec": round(build_sec, 3),
    }, indent=2)[:5000])

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = int(args.workers)
    solver.parameters.random_seed = int(args.seed)
    ts = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - ts
    status_name = solver.StatusName(status)
    print(f"status={status_name} solve_sec={solve_sec:.3f}")

    result = {
        "schema": "global_J_face_search_v1",
        "meaning": "Search for a complete-Wang distinct 19-support contained in J=support of the saved fractional LP point. If none exists with a replayable certificate, the cut sum_{p notin J} x_p >= 1 separates that fractional point; CP-SAT status alone is not proof.",
        "field": "F2",
        "core": "E11 quotient core",
        "rank_s": s,
        "global_solution_file": str(GLOBAL_PATH),
        "J_size": len(J),
        "J_points": J,
        "parameters": {
            "solver_time": args.solver_time,
            "workers": args.workers,
            "seed": args.seed,
            "row_set": args.row_set,
            "contraction_lb": bool(args.contraction_lb),
            "use_overlap": bool(args.use_overlap),
            "overlap_max": args.overlap_max,
            "trace_cuts": args.trace_cuts,
            "max_size5_cuts": args.max_size5_cuts,
            "cert_cuts": bool(args.cert_cuts),
            "max_certs": args.max_certs,
        },
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "complete_meta": complete_meta,
        "reduced_counts": None if red is None else {"kept": len(red["kept_key8"]), "dropped": len(red["dropped_key8"]), "kept_hash": red.get("kept_key8_sha256")},
        "constraint_summary": {
            "wang_rows_added": row_count,
            "wang_rows_immediate_empty_on_J": immediate_empty,
            "wang_rows_skipped_by_reduced": skipped_reduced,
            "wang_rows_by_dim": {str(k): int(v) for k, v in sorted(row_by_dim.items())},
            "wang_rows_by_L": {str(k): int(v) for k, v in sorted(row_by_L.items())},
            "contraction_lower_bounds": contraction_lb_count,
            "contraction_rank_hist": {str(k): int(v) for k, v in sorted(contraction_rank_hist.items())},
            "overlap_cuts": overlap_count,
            "overlap_meta": overlap_meta,
            "trace_dependency_cuts": len(trace_cuts),
            "trace_dependency_cut_size_hist": {str(k): int(v) for k, v in sorted(trace_hist.items())},
            "certificate_cut_summary": cert_summary,
        },
        "build_sec": round(build_sec, 3),
        "status": status_name,
        "solve_sec": round(solve_sec, 3),
    }

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A = [p for p in J if solver.Value(x[p])]
        scan = complete_core_wang_scan("global_J_face_solution", A, s, records, max_head=40)
        scan_with_points = full_violation_scan(A, records, s)
        sat = saturation_domains(T_core, A)
        trans = transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=10)
        qscan = eval_candidate_sources("global_J_face_solution", A, contractions, masks, max_source_size=2, max_store=20)
        phi = build_phi(T_core)
        trace_dep = eval_support_local_dependency(A, sorted(phi), phi, {p: None for p in points})
        ov = overlap_summary(A, center_bits) if center_bits else None
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
            "overlap_summary": ov,
        }
        print("A", A)
        print(json.dumps({
            "complete_wang_violations": scan["complete_violation_count"],
            "zero_domain_terms": result["solution"]["zero_domain_terms"],
            "linear_pass": result["solution"]["linear_pass"],
            "transversal_failures": result["solution"]["transversal_failures"],
            "qrank2": result["solution"]["quotient_rank_violations_size2"],
            "trace_bad": trace_dep.get("exact_local_inconsistent_terms"),
            "overlap_max": None if ov is None else ov["max_transported_overlap"],
        }, indent=2))

    result["elapsed_sec"] = round(time.time() - t0, 3)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("saved", args.out)


if __name__ == "__main__":
    main()
