#!/usr/bin/env python3
"""analysis: cumulative support search for the distinct E11 core branch.

This is a point-level CP-SAT experiment, not a proof.  It combines the currently
sound support-level necessary conditions in a materially changed formulation:
  * the analysis primitive-retained Wang rows (with any candidate rescanned
    against the complete 417,199-row table);
  * contraction lower bounds for all 255 nonzero contractions;
  * the 1,152 transported radius-3 overlap cuts from the verified analysis
    local Wang proof;
  * optional sound trace-dependency cuts (minimal or size-5 family);
  * optional corrected trace-certificate cuts.

A FEASIBLE support is only an A-support candidate and immediately receives the
existing complete-Wang and fixed-A necessary-condition checks.  UNKNOWN or
solver-only INFEASIBLE is not a mathematical result.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, List, Sequence

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import (
    ROOT,
    build_core_constraints,
    complete_core_wang_scan,
    saturation_domains,
    transversal_failures,
)
from candidate_source_qcut_scan import eval_candidate_sources
from quotient_rank_cuts import build_contractions, point_mask_for_q
from cert_trace_separator import add_certificate_cuts, full_violation_scan
from distinct_trace_cut_cpsat import load_hint, load_trace_cuts
from trace_dependency_family import dot8, eval_support_local_dependency, trace_mask_correct
from dual_basis_instrument import gf2_mat_inv
from fixed_A_saturation import contraction_matrix, mat_rank_f2
from overlap_cut_separator import load_overlap_centers, support_bitset, overlap_summary

OUTDIR = ROOT / "workspace/data/cumulative_search"
REDUCED_PATH = ROOT / "workspace/data/reduced_wang/primitive_reduced_rows.pkl"
OVERLAP_PATH = ROOT / "workspace/data/transported_overlap/transported_overlap_analysis.json"
TRACE_CUT_JSON = ROOT / "workspace/data/trace_dependency_cuts/trace_dependency_cuts.json"
TRACE_SIZE5_PKL = ROOT / "workspace/data/trace_dependency_cuts/trace_dependency_size5_cuts.pkl"
CERT_CUT_PATH = ROOT / "workspace/data/trace_dependency_cuts/trace_certificate_family_cuts_augmented.json"


def points_from_bitset(bs: int) -> List[int]:
    pts = []
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())  # bit index + 1, because x_p stored at bit p-1
        bs ^= bit
    return pts


def load_reduced(path: Path):
    with path.open("rb") as f:
        return pickle.load(f)


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


def add_retained_wang_rows(model, x, records: Sequence[dict], kept_keys: set):
    count = 0
    by_dim = Counter()
    by_L = Counter()
    skipped_not_kept = 0
    for rec in records:
        key = int(rec["key8"])
        if key not in kept_keys:
            skipped_not_kept += 1
            continue
        L = int(rec["L"])
        cap = 19 - L
        if cap >= 19:
            continue
        pts = points_from_bitset(int(rec["point_bitset"]))
        if not pts:
            continue
        model.Add(sum(x[p] for p in pts) <= cap)
        count += 1
        by_dim[int(rec["dim8"])] += 1
        by_L[L] += 1
    return {
        "added": count,
        "skipped_not_kept": skipped_not_kept,
        "by_dim": {str(k): int(v) for k, v in sorted(by_dim.items())},
        "by_L": {str(k): int(v) for k, v in sorted(by_L.items())},
    }


def main():
    from ortools.sat.python import cp_model

    ap = argparse.ArgumentParser()
    ap.add_argument("--solver-time", type=float, default=300.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=6262)
    ap.add_argument("--max-rounds", type=int, default=1)
    ap.add_argument("--trace-cuts", choices=["none", "minimal", "size5"], default="minimal")
    ap.add_argument("--max-size5-cuts", type=int, default=None)
    ap.add_argument("--cert-cuts", action="store_true")
    ap.add_argument("--max-certs", type=int, default=None)
    ap.add_argument("--use-overlap", action="store_true")
    ap.add_argument("--overlap-max", type=int, default=15)
    ap.add_argument("--hint-source", type=Path, default=ROOT / "workspace/data/reduced_wang/reduced_wang_cpsat_overlap_300s.json")
    ap.add_argument("--out", type=Path, default=OUTDIR / "cumulative_reduced_search.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    s = 19
    points = list(range(1, 256))
    lut, lut_meta = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    records, complete_meta = build_core_constraints(CoreQuotient(1), lut)
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}
    red = load_reduced(REDUCED_PATH)
    kept = set(int(k) for k in red["kept_key8"])

    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in points}
    model.Add(sum(x[p] for p in points) == s)

    wang_summary = add_retained_wang_rows(model, x, records, kept)

    w = {}
    contraction_lb = 0
    contraction_rank_hist = Counter()
    for q, c in contractions.items():
        q = int(q)
        var = model.NewIntVar(0, s, f"w_{q}")
        w[q] = var
        model.Add(var == sum(x[p] for p in points if dot8(q, p)))
        rk = int(c["rank"])
        contraction_rank_hist[rk] += 1
        if rk > 0:
            model.Add(var >= rk)
            contraction_lb += 1

    centers = []
    center_bits = []
    overlap_meta = {}
    overlap_cut_count = 0
    if args.use_overlap:
        centers, overlap_meta = load_overlap_centers(OVERLAP_PATH, None)
        center_bits = [support_bitset(c) for c in centers]
        for c in centers:
            model.Add(sum(x[p] for p in c) <= int(args.overlap_max))
            overlap_cut_count += 1

    trace_cuts = load_trace_cuts(args.trace_cuts, TRACE_CUT_JSON, TRACE_SIZE5_PKL, args.max_size5_cuts)
    trace_hist = Counter()
    for cut in trace_cuts:
        p = int(cut["p"])
        H = [int(q) for q in cut["H"]]
        model.Add(sum(w[q] for q in H) >= 9 * len(H) + x[p])
        trace_hist[len(H)] += 1

    cert_summary = None
    if args.cert_cuts:
        cert_summary = add_certificate_cuts(model, x, w, contractions, args.max_certs, CERT_CUT_PATH)

    hint = load_hint(args.hint_source, None)
    hint_added = False
    if hint:
        hs = set(int(p) for p in hint)
        for p in points:
            model.AddHint(x[p], 1 if p in hs else 0)
        hint_added = True

    build_sec = time.time() - t0
    print(json.dumps({
        "build_sec": round(build_sec, 3),
        "retained_wang_rows": wang_summary["added"],
        "contraction_lbs": contraction_lb,
        "overlap_cuts": overlap_cut_count,
        "trace_cuts": len(trace_cuts),
        "trace_hist": {str(k): int(v) for k, v in sorted(trace_hist.items())},
        "cert_summary": cert_summary,
        "hint_added": hint_added,
    }, indent=2)[:5000])

    rounds = []
    included_extra = set()
    phi = None
    for r in range(int(args.max_rounds)):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(args.solver_time)
        solver.parameters.num_search_workers = int(args.workers)
        solver.parameters.random_seed = int(args.seed + r)
        ts = time.time()
        status = solver.Solve(model)
        solve_sec = time.time() - ts
        status_name = solver.StatusName(status)
        print(f"round {r}: status={status_name} solve_sec={solve_sec:.3f}")
        rec = {"round": r, "status": status_name, "solve_sec": round(solve_sec, 3)}
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rounds.append(rec)
            break
        A = [p for p in points if solver.Value(x[p])]
        scan = complete_core_wang_scan(f"cumulative_round_{r}", A, s, records, max_head=40)
        # full_violation_scan includes point lists for adding rows if reduction misses a dropped row.
        scan_with_points = full_violation_scan(A, records, s)
        new_rows = []
        for v in scan_with_points["violations"]:
            key = int(v["key8"])
            if key not in kept and key not in included_extra:
                new_rows.append(v)
                included_extra.add(key)
        for v in new_rows:
            model.Add(sum(x[p] for p in v["points"]) <= int(v["cap"]))
        sat = saturation_domains(T_core, A)
        trans = transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=10)
        qscan = eval_candidate_sources(f"cumulative_round_{r}", A, contractions, masks, max_source_size=2, max_store=20)
        if phi is None:
            phi = build_phi(T_core)
        trace_dep = eval_support_local_dependency(A, sorted(phi), phi, {p: None for p in points})
        weights = {q: solver.Value(w[q]) for q in sorted(w)}
        rec.update({
            "A_cols": A,
            "complete_wang_scan": scan,
            "new_complete_rows_added_from_dropped_or_missing": len(new_rows),
            "new_rows_head": [{k: vv for k, vv in v.items() if k != "points"} for v in new_rows[:20]],
            "zero_domain_terms": len(sat["summary"]["zero_domain_terms"]),
            "linear_pass": sat["summary"]["linear_membership"]["necessary_linear_test_passed"],
            "affine_dim": sat["summary"]["linear_membership"].get("affine_solution_dimension_if_consistent"),
            "saturated_contractions": sat["summary"].get("saturated_contraction_count"),
            "transversal_failures": trans["failure_count_reported"],
            "quotient_rank_violations_size2": qscan["violated_guarded_instances"],
            "trace_local_dependency": trace_dep,
            "overlap_summary": overlap_summary(A, center_bits) if center_bits else None,
            "rank9_weight_hist": {str(k): int(v) for k, v in sorted(Counter(weights[q] for q in weights if int(contractions[q]["rank"]) == 9).items())},
        })
        print("  A", A)
        print("  checks", json.dumps({
            "wang_viol": scan["complete_violation_count"],
            "new_rows": len(new_rows),
            "zero_domain_terms": rec["zero_domain_terms"],
            "linear_pass": rec["linear_pass"],
            "transversal_failures": rec["transversal_failures"],
            "qrank2": rec["quotient_rank_violations_size2"],
            "trace_bad": trace_dep.get("exact_local_inconsistent_terms"),
            "overlap_max": None if rec["overlap_summary"] is None else rec["overlap_summary"]["max_transported_overlap"],
        }, sort_keys=True))
        rounds.append(rec)
        if scan["complete_violation_count"] == 0:
            break
        if not new_rows:
            model.Add(sum(x[p] for p in A) <= 18)

    result = {
        "schema": "cumulative_reduced_support_search_v1",
        "meaning": "CP-SAT search combining retained Wang rows, contraction lower bounds, transported overlap cuts, and independent-verification-record cuts. FEASIBLE is only an A-support candidate with checks; UNKNOWN or solver-only INFEASIBLE is not proof.",
        "field": "F2",
        "core": "E11 quotient core",
        "rank_s": s,
        "parameters": {
            "solver_time": args.solver_time,
            "workers": args.workers,
            "seed": args.seed,
            "max_rounds": args.max_rounds,
            "trace_cuts": args.trace_cuts,
            "max_size5_cuts": args.max_size5_cuts,
            "cert_cuts": bool(args.cert_cuts),
            "max_certs": args.max_certs,
            "use_overlap": bool(args.use_overlap),
            "overlap_max": args.overlap_max,
            "hint_source": str(args.hint_source) if args.hint_source else None,
        },
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "complete_meta": complete_meta,
        "reduced_counts": {"kept": len(red["kept_key8"]), "dropped": len(red["dropped_key8"]), "kept_hash": red.get("kept_key8_sha256")},
        "constraint_summary": {
            "retained_wang": wang_summary,
            "contraction_lower_bounds": contraction_lb,
            "contraction_rank_hist": {str(k): int(v) for k, v in sorted(contraction_rank_hist.items())},
            "overlap_cuts": overlap_cut_count,
            "overlap_meta": overlap_meta,
            "trace_dependency_cuts": len(trace_cuts),
            "trace_dependency_cut_size_hist": {str(k): int(v) for k, v in sorted(trace_hist.items())},
            "certificate_cut_summary": cert_summary,
            "hint_added": hint_added,
        },
        "build_sec": round(build_sec, 3),
        "rounds": rounds,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(args.out), "rounds": len(rounds), "last": rounds[-1] if rounds else None, "elapsed_sec": result["elapsed_sec"]}, indent=2, sort_keys=True)[:5000])


if __name__ == "__main__":
    main()
