#!/usr/bin/env python3
r"""analysis: global distinct-support separator with transported local-proof cuts.

Input: analysis gave a DRAT-verified radius-3 pure-Wang local exclusion around
base support S.  In the global complete-Wang distinct E11 support problem this
is the valid derived inequality

    sum_{p in gS} x_p <= 15

for every whole-support image gS under the induced E11 stabilizer.  These cuts
exclude certified local neighborhoods without collapsing point variables or
using point-orbit counts.

This script reuses the analysis adaptive Wang-row separator, adds these
transported overlap cuts, and reports whether the next candidates are genuinely
outside the already certified basin.  A zero-Wang support would be a real
A-support candidate and still requires B/C completion; solver UNKNOWN is not a
lower bound.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402
from complete_core_and_transversal import (  # noqa: E402
    ROOT,
    build_core_constraints,
    saturation_domains,
    transversal_failures,
)
from candidate_source_qcut_scan import eval_candidate_sources  # noqa: E402
from quotient_rank_cuts import build_contractions, point_mask_for_q  # noqa: E402
from cert_trace_separator import add_certificate_cuts, build_phi, full_violation_scan, points_for_rec  # noqa: E402
from distinct_trace_cut_cpsat import load_hint, load_trace_cuts  # noqa: E402
from trace_dependency_family import dot8, eval_support_local_dependency, trace_mask_correct  # noqa: E402
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from fixed_A_saturation import contraction_matrix, mat_rank_f2  # noqa: E402

OUTDIR = ROOT / "workspace/data/transported_overlap"
DEFAULT_OVERLAP_ANALYSIS = OUTDIR / "transported_overlap_analysis.json"
DEFAULT_CERTCUT_PATH = ROOT / "workspace/data/trace_dependency_cuts/trace_certificate_family_cuts_augmented.json"
DEFAULT_BASE_SUPPORT = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]


def load_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}, payload.get("meta", {})


def support_bitset(A: Iterable[int]) -> int:
    b = 0
    for p in A:
        b |= 1 << (int(p) - 1)
    return b


def load_overlap_centers(path: Path, max_centers: int | None = None) -> Tuple[List[List[int]], dict]:
    data = json.loads(path.read_text())
    centers = [[int(p) for p in c] for c in data.get("centers", [])]
    if max_centers is not None:
        centers = centers[: max(0, int(max_centers))]
    meta = {
        "source": str(path),
        "center_count_in_file": len(data.get("centers", [])),
        "center_count_used": len(centers),
        "certified_overlap_cut": data.get("certified_overlap_cut"),
        "group": data.get("group"),
        "base_support": data.get("base_support"),
    }
    return centers, meta


def overlap_summary(A: Sequence[int], center_bits: Sequence[int]) -> dict:
    Ab = support_bitset(A)
    vals = [int((Ab & cb).bit_count()) for cb in center_bits]
    hist = Counter(vals)
    mx = max(vals) if vals else 0
    return {
        "max_transported_overlap": mx,
        "exchange_distance_to_base_orbit": 19 - mx,
        "violates_transported_radius3_cut": bool(mx >= 16),
        "overlap_histogram": {str(k): int(v) for k, v in sorted(hist.items())},
        "num_centers_at_max": int(hist[mx]) if vals else 0,
    }


def main() -> None:
    from ortools.sat.python import cp_model

    ap = argparse.ArgumentParser()
    ap.add_argument("--threshold-L", type=int, default=15)
    ap.add_argument("--solver-time", type=float, default=240.0)
    ap.add_argument("--max-rounds", type=int, default=4)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=5501)
    ap.add_argument("--overlap-analysis", type=Path, default=DEFAULT_OVERLAP_ANALYSIS)
    ap.add_argument("--max-overlap-centers", type=int, default=None)
    ap.add_argument("--overlap-max", type=int, default=15)
    ap.add_argument("--disable-overlap-cuts", action="store_true")
    ap.add_argument("--cert-cuts", action="store_true")
    ap.add_argument("--cert-cut-path", type=Path, default=DEFAULT_CERTCUT_PATH)
    ap.add_argument("--max-certs", type=int, default=None)
    ap.add_argument("--trace-cuts", choices=["none", "minimal", "size5"], default="none")
    ap.add_argument("--max-size5-cuts", type=int, default=None)
    ap.add_argument("--hint-source", type=Path, default=ROOT / "workspace/data/trace_dependency_cuts/separator_L15_augcertcuts_4r_240s.json")
    ap.add_argument("--out", type=Path, default=OUTDIR / "overlap_cut_separator.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    s = 19
    points = list(range(1, 256))
    core = CoreQuotient(1)
    lut, _meta_lut = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    records, meta = build_core_constraints(core, lut)
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}

    centers, overlap_meta = load_overlap_centers(args.overlap_analysis, args.max_overlap_centers)
    center_bits = [support_bitset(c) for c in centers]

    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in points}
    model.Add(sum(x[p] for p in points) == s)

    w = {}
    contraction_lb = 0
    for q, c in contractions.items():
        w[int(q)] = model.NewIntVar(0, s, f"w_{q}")
        model.Add(w[int(q)] == sum(x[p] for p in points if dot8(q, p)))
        if int(c["rank"]) > 0:
            model.Add(w[int(q)] >= int(c["rank"]))
            contraction_lb += 1

    wang_count = 0
    initial_by_L = Counter()
    included = set()
    for rec in records:
        L = int(rec["L"])
        if L < args.threshold_L:
            continue
        cap = s - L
        if cap >= s:
            continue
        pts = points_for_rec(rec)
        if not pts:
            continue
        model.Add(sum(x[p] for p in pts) <= cap)
        included.add(int(rec["key8"]))
        wang_count += 1
        initial_by_L[L] += 1

    overlap_cut_count = 0
    if not args.disable_overlap_cuts:
        for c in centers:
            model.Add(sum(x[p] for p in c) <= int(args.overlap_max))
            overlap_cut_count += 1

    local_cuts = load_trace_cuts(args.trace_cuts, ROOT / "workspace/data/trace_dependency_cuts/trace_dependency_cuts.json", ROOT / "workspace/data/trace_dependency_cuts/trace_dependency_size5_cuts.pkl", args.max_size5_cuts)
    local_hist = Counter()
    for cut in local_cuts:
        p = int(cut["p"])
        H = [int(q) for q in cut["H"]]
        model.Add(sum(w[q] for q in H) >= 9 * len(H) + x[p])
        local_hist[len(H)] += 1

    cert_summary = None
    if args.cert_cuts:
        cert_summary = add_certificate_cuts(model, x, w, contractions, args.max_certs, args.cert_cut_path)

    hint = load_hint(args.hint_source, None)
    hint_added = False
    if hint:
        hs = set(int(p) for p in hint)
        for p in points:
            model.AddHint(x[p], 1 if p in hs else 0)
        hint_added = True

    build_sec = time.time() - t0
    rounds = []
    phi = None
    for r in range(args.max_rounds):
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
        scan = full_violation_scan(A, records, s)
        sat = saturation_domains(T_core, A)
        trans = transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=10)
        qscan = eval_candidate_sources(f"overlap_separator_round_{r}", A, contractions, masks, max_source_size=2, max_store=20)
        if phi is None:
            phi = build_phi(T_core)
        local_dep = eval_support_local_dependency(A, sorted(phi), phi, {p: None for p in points})
        ov = overlap_summary(A, center_bits)
        new_rows = []
        for v in scan["violations"]:
            key = int(v["key8"])
            if key not in included:
                new_rows.append(v)
                included.add(key)
        for v in new_rows:
            model.Add(sum(x[p] for p in v["points"]) <= int(v["cap"]))
        rec.update({
            "A_cols": A,
            "complete_wang_violations": scan["complete_violation_count"],
            "complete_wang_max_excess": scan["max_excess"],
            "violations_by_L": scan["violations_by_L"],
            "violations_by_dim8": scan["violations_by_dim8"],
            "violations_head": scan["violations_head"],
            "new_rows_added": len(new_rows),
            "total_rows_included_after_round": len(included),
            "overlap_to_certified_base_orbit": ov,
            "zero_domain_terms": len(sat["summary"]["zero_domain_terms"]),
            "linear_pass": sat["summary"]["linear_membership"]["necessary_linear_test_passed"],
            "affine_dim": sat["summary"]["linear_membership"].get("affine_solution_dimension_if_consistent"),
            "saturated_contractions": sat["summary"].get("saturated_contraction_count"),
            "transversal_failures": trans["failure_count_reported"],
            "quotient_rank_violations_size2": qscan["violated_guarded_instances"],
            "trace_local_dependency": local_dep,
        })
        print(f"  A={A}")
        print(f"  viol={scan['complete_violation_count']} byL={scan['violations_by_L']} new={len(new_rows)} maxov={ov['max_transported_overlap']} sat={rec['saturated_contractions']} trace_bad={local_dep['exact_local_inconsistent_terms']}")
        rounds.append(rec)
        if scan["complete_violation_count"] == 0:
            break
        if len(new_rows) == 0:
            model.Add(sum(x[p] for p in A) <= 18)

    result = {
        "schema": "overlap_cut_separator_v1",
        "field": "F2",
        "core": "E11 quotient core",
        "rank_s": s,
        "meaning": "Adaptive exact Wang-row separation with transported radius-3 local-proof overlap cuts. The overlap cuts are valid only as consequences for complete-Wang-admissible distinct supports and preserve 255 point variables.",
        "parameters": {
            "threshold_L": args.threshold_L,
            "solver_time": args.solver_time,
            "max_rounds": args.max_rounds,
            "workers": args.workers,
            "seed": args.seed,
            "overlap_analysis": str(args.overlap_analysis),
            "overlap_max": args.overlap_max,
            "disable_overlap_cuts": bool(args.disable_overlap_cuts),
            "max_overlap_centers": args.max_overlap_centers,
            "cert_cuts": bool(args.cert_cuts),
            "cert_cut_path": str(args.cert_cut_path),
            "max_certs": args.max_certs,
            "trace_cuts": args.trace_cuts,
            "max_size5_cuts": args.max_size5_cuts,
            "hint_source": str(args.hint_source) if args.hint_source else None,
        },
        "build_sec": round(build_sec, 3),
        "complete_core_table_meta": meta,
        "initial_rows": wang_count,
        "initial_rows_by_L": {str(k): int(v) for k, v in sorted(initial_by_L.items())},
        "contraction_lower_bounds": contraction_lb,
        "overlap_cut_summary": overlap_meta | {"overlap_cuts_used": overlap_cut_count, "overlap_max_used": int(args.overlap_max)},
        "local_trace_cuts": len(local_cuts),
        "local_trace_cut_size_hist": {str(k): int(v) for k, v in sorted(local_hist.items())},
        "certificate_cut_summary": cert_summary,
        "hint_added": hint_added,
        "rounds": rounds,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(args.out),
        "rounds": len(rounds),
        "last": rounds[-1] if rounds else None,
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True)[:5000])


if __name__ == "__main__":
    main()
