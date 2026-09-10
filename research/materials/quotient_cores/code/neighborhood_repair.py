#!/usr/bin/env python3
r"""analysis: exact bounded exchange-neighborhood repair for the E11 distinct support.

Given a 19-point distinct E11-core A-support S with a small number of complete
Wang occupation violations, test whether there is a Wang-admissible support S'
within exchange radius d:

    |S cap S'| >= 19-d,  |S'| = 19.

For any Wang row U with capacity cap=19-L(U), occupancy in a d-neighborhood can
increase by at most d.  Therefore if slack_S(U)=cap-|S cap U| >= d, U is
automatically satisfied by every S' in the neighborhood.  The model keeps exactly
those complete-table rows with slack<d, so feasibility of the filtered model is
feasibility for the full Wang table inside the exchange neighborhood.  It remains
only an A-support/necessary-conditions model, not a B/C completion.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
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
from fixed_A_saturation import contraction_matrix, mat_rank_f2  # noqa: E402
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from cert_trace_separator import add_certificate_cuts  # noqa: E402
from distinct_trace_cut_cpsat import load_trace_cuts  # noqa: E402
from trace_dependency_family import dot8, eval_support_local_dependency, trace_mask_correct  # noqa: E402
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis  # noqa: E402

DEFAULT_SUPPORT = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]
OUTDIR = ROOT / "workspace/data/neighborhood_repair"
CERTCUT_PATH = ROOT / "workspace/data/trace_dependency_cuts/trace_certificate_family_cuts_augmented.json"
SIZE5_PATH = ROOT / "workspace/data/trace_dependency_cuts/trace_dependency_size5_cuts.pkl"
MINCUT_PATH = ROOT / "workspace/data/trace_dependency_cuts/trace_dependency_cuts.json"


def load_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}, payload.get("meta", {})


def row_points(rec: dict) -> List[int]:
    if "point_bitset" in rec:
        b = int(rec["point_bitset"])
        return [i + 1 for i in range(255) if (b >> i) & 1]
    return subspace_points_from_basis(unpack_basis(int(rec["key8"])))


def points_bitset(pts: Iterable[int]) -> int:
    b = 0
    for p in pts:
        b |= 1 << (int(p) - 1)
    return b


def augment_records_with_bitsets(records: Sequence[dict]) -> List[dict]:
    out = []
    for rec in records:
        pts = row_points(rec)
        r = dict(rec)
        r["points"] = pts
        r["point_bitset_local"] = points_bitset(pts)
        out.append(r)
    return out


def slack_profile(records: Sequence[dict], S: Sequence[int], s: int = 19, max_d: int = 4) -> dict:
    Sbit = points_bitset(S)
    counts_lt_d = {str(d): 0 for d in range(1, max_d + 1)}
    by_slack = Counter()
    by_slack_dim = Counter()
    by_slack_L = Counter()
    violations = []
    examples = defaultdict(list)
    for rec in records:
        L = int(rec["L"])
        cap = s - L
        if cap >= s:
            continue
        occ = (int(rec["point_bitset_local"]) & Sbit).bit_count()
        slack = cap - occ
        by_slack[slack] += 1
        by_slack_dim[(slack, int(rec["dim8"]))] += 1
        by_slack_L[(slack, L)] += 1
        if len(examples[slack]) < 8:
            examples[slack].append({
                "key8": int(rec["key8"]), "dim8": int(rec["dim8"]), "L": L,
                "cap": cap, "occupancy": occ, "slack": slack,
                "point_count": len(rec["points"]),
            })
        if slack < 0:
            violations.append({
                "key8": int(rec["key8"]), "dim8": int(rec["dim8"]), "L": L,
                "cap": cap, "occupancy": occ, "excess": -slack,
                "point_count": len(rec["points"]), "points": rec["points"],
            })
        for d in range(1, max_d + 1):
            if slack < d:
                counts_lt_d[str(d)] += 1
    return {
        "support": list(map(int, S)),
        "max_d_profiled": max_d,
        "rows_with_slack_lt_d": counts_lt_d,
        "slack_histogram": {str(k): int(v) for k, v in sorted(by_slack.items())},
        "slack_dim_histogram_head": {f"slack={k[0]},dim={k[1]}": int(v) for k, v in sorted(by_slack_dim.items())[:80]},
        "slack_L_histogram_head": {f"slack={k[0]},L={k[1]}": int(v) for k, v in sorted(by_slack_L.items())[:120]},
        "violation_count": len(violations),
        "violations_by_L": {str(k): int(v) for k, v in sorted(Counter(v["L"] for v in violations).items())},
        "violations_by_dim8": {str(k): int(v) for k, v in sorted(Counter(v["dim8"] for v in violations).items())},
        "violations_head": [{kk: vv for kk, vv in v.items() if kk != "points"} for v in violations[:30]],
        "examples_by_slack": {str(k): v for k, v in sorted(examples.items()) if k <= max_d},
    }


def filtered_rows(records: Sequence[dict], S: Sequence[int], d: int, s: int = 19) -> Tuple[List[dict], dict]:
    Sbit = points_bitset(S)
    rows = []
    by_slack = Counter()
    by_L = Counter()
    by_dim = Counter()
    for rec in records:
        L = int(rec["L"])
        cap = s - L
        if cap >= s:
            continue
        occ = (int(rec["point_bitset_local"]) & Sbit).bit_count()
        slack = cap - occ
        if slack < d:
            r = dict(rec)
            r["cap"] = cap
            r["base_occupancy"] = occ
            r["base_slack"] = slack
            rows.append(r)
            by_slack[slack] += 1
            by_L[L] += 1
            by_dim[int(rec["dim8"])] += 1
    summary = {
        "d": int(d),
        "row_count": len(rows),
        "rows_by_base_slack": {str(k): int(v) for k, v in sorted(by_slack.items())},
        "rows_by_L": {str(k): int(v) for k, v in sorted(by_L.items())},
        "rows_by_dim8": {str(k): int(v) for k, v in sorted(by_dim.items())},
        "exactness_reason": "Rows with base slack >= d cannot be violated by a support with at most d exchanges, because occupancy can increase by at most d.",
    }
    return rows, summary


def full_violation_scan(A: Sequence[int], records: Sequence[dict], s: int = 19) -> dict:
    Abit = points_bitset(A)
    violations = []
    by_L = Counter()
    by_dim = Counter()
    max_excess = 0
    for rec in records:
        L = int(rec["L"])
        cap = s - L
        if cap >= s:
            continue
        occ = (int(rec["point_bitset_local"]) & Abit).bit_count()
        if occ > cap:
            excess = occ - cap
            max_excess = max(max_excess, excess)
            by_L[L] += 1
            by_dim[int(rec["dim8"])] += 1
            violations.append({
                "key8": int(rec["key8"]), "L": L, "dim8": int(rec["dim8"]),
                "cap": cap, "occupancy": occ, "excess": excess,
                "point_count": len(rec["points"]),
                "basis8": list(map(int, rec.get("basis8", []))) if "basis8" in rec else None,
            })
    return {
        "complete_violation_count": len(violations),
        "max_excess": max_excess,
        "violations_by_L": {str(k): int(v) for k, v in sorted(by_L.items())},
        "violations_by_dim8": {str(k): int(v) for k, v in sorted(by_dim.items())},
        "violations_head": violations[:30],
    }


def build_phi(T_core: np.ndarray) -> Dict[int, int]:
    phi = {}
    for q in range(1, 1 << 8):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) == 9:
            inv = gf2_mat_inv(M)
            if inv is None:
                raise RuntimeError(q)
            phi[int(q)] = trace_mask_correct(inv)
    return phi


def parse_support_arg(text: str | None) -> List[int]:
    if not text:
        return list(DEFAULT_SUPPORT)
    stripped = text.strip()
    if stripped.startswith("["):
        arr = json.loads(stripped)
    else:
        arr = [int(z) for z in stripped.replace(",", " ").split()]
    if len(arr) != 19 or len(set(arr)) != 19:
        raise ValueError("support must have 19 distinct points")
    if any(int(p) < 1 or int(p) > 255 for p in arr):
        raise ValueError("points must be in 1..255")
    return sorted(map(int, arr))


def solve_neighborhood(args, records, T_core, contractions, base_support: List[int], rows: List[dict], row_summary: dict) -> dict:
    from ortools.sat.python import cp_model
    s = 19
    points = list(range(1, 256))
    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in points}
    model.Add(sum(x[p] for p in points) == s)
    model.Add(sum(x[p] for p in base_support) >= s - args.d)

    # Keep contraction weights for optional independent-verification-record cuts.  Contraction-rank
    # lower bounds can be disabled to isolate pure Wang occupation repairability.
    w = {}
    contraction_lb = 0
    for q, c in contractions.items():
        q = int(q)
        w[q] = model.NewIntVar(0, s, f"w_{q}")
        model.Add(w[q] == sum(x[p] for p in points if dot8(q, p)))
        if (not args.no_contraction_lb) and int(c["rank"]) > 0:
            model.Add(w[q] >= int(c["rank"]))
            contraction_lb += 1

    for rec in rows:
        model.Add(sum(x[p] for p in rec["points"]) <= int(rec["cap"]))

    local_cuts = []
    local_hist = Counter()
    if args.trace_cuts != "none":
        local_cuts = load_trace_cuts(args.trace_cuts, MINCUT_PATH, SIZE5_PATH, args.max_size5_cuts)
        for cut in local_cuts:
            p = int(cut["p"])
            H = [int(q) for q in cut["H"]]
            model.Add(sum(w[q] for q in H) >= 9 * len(H) + x[p])
            local_hist[len(H)] += 1

    cert_summary = None
    if args.cert_cuts:
        cert_summary = add_certificate_cuts(model, x, w, contractions, args.max_certs, args.cert_cut_path)

    if args.hint_base:
        B = set(base_support)
        for p in points:
            model.AddHint(x[p], 1 if p in B else 0)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = int(args.workers)
    solver.parameters.random_seed = int(args.seed)
    tsolve = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - tsolve
    status_name = solver.StatusName(status)
    out = {
        "status": status_name,
        "solve_sec": round(solve_sec, 3),
        "d": int(args.d),
        "row_summary": row_summary,
        "contraction_lower_bounds": contraction_lb,
        "trace_cuts": args.trace_cuts,
        "local_trace_cuts": len(local_cuts),
        "local_trace_cut_size_hist": {str(k): int(v) for k, v in sorted(local_hist.items())},
        "cert_cuts": bool(args.cert_cuts),
        "certificate_cut_summary": cert_summary,
        "model_variables_reported_by_solver": solver.NumBooleans(),
        "model_conflicts": solver.NumConflicts(),
        "model_branches": solver.NumBranches(),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A = [p for p in points if solver.Value(x[p])]
        base_set = set(base_support)
        A_set = set(A)
        scan = full_violation_scan(A, records, s)
        sat = saturation_domains(T_core, A)
        trans = transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=20)
        masks = {q: point_mask_for_q(q) for q in contractions}
        qscan = eval_candidate_sources("local_repair", A, contractions, masks, max_source_size=2, max_store=20)
        phi = build_phi(T_core)
        local_dep = eval_support_local_dependency(A, sorted(phi), phi, {p: None for p in points})
        out.update({
            "A_cols": A,
            "removed_from_base": sorted(base_set - A_set),
            "added_to_base": sorted(A_set - base_set),
            "intersection_with_base": len(base_set & A_set),
            "complete_wang_scan": scan,
            "zero_domain_terms": len(sat["summary"]["zero_domain_terms"]),
            "linear_pass": sat["summary"]["linear_membership"]["necessary_linear_test_passed"],
            "affine_dim": sat["summary"]["linear_membership"].get("affine_solution_dimension_if_consistent"),
            "saturated_contractions": sat["summary"].get("saturated_contraction_count"),
            "transversal_failures": trans["failure_count_reported"],
            "transversal_failure_examples": trans.get("failures", [])[:5],
            "quotient_rank_violations_size2": qscan["violated_guarded_instances"],
            "quotient_rank_violation_examples": qscan.get("violations", [])[:5],
            "trace_local_dependency": local_dep,
            "exact_neighborhood_full_wang_confirmed": scan["complete_violation_count"] == 0,
        })
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--support", type=str, default=None, help="JSON list or comma/space separated 19 support points; default is analysis current 9-violation support")
    ap.add_argument("--d", type=int, default=1)
    ap.add_argument("--profile-max-d", type=int, default=4)
    ap.add_argument("--profile-only", action="store_true")
    ap.add_argument("--solver-time", type=float, default=120.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=5401)
    ap.add_argument("--hint-base", action="store_true")
    ap.add_argument("--no-contraction-lb", action="store_true", help="omit contraction-rank lower-bound inequalities; useful to isolate pure Wang occupation repairability")
    ap.add_argument("--trace-cuts", choices=["none", "minimal", "size5"], default="none")
    ap.add_argument("--max-size5-cuts", type=int, default=None)
    ap.add_argument("--cert-cuts", action="store_true")
    ap.add_argument("--cert-cut-path", type=Path, default=CERTCUT_PATH)
    ap.add_argument("--max-certs", type=int, default=None)
    ap.add_argument("--out", type=Path, default=OUTDIR / "neighborhood_repair.json")
    args = ap.parse_args()
    if args.d < 0 or args.d > 19:
        raise ValueError("d must be between 0 and 19")
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    base_support = parse_support_arg(args.support)
    core = CoreQuotient(1)
    lut, lut_meta = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    records_raw, meta = build_core_constraints(core, lut)
    records = augment_records_with_bitsets(records_raw)
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)

    profile = slack_profile(records, base_support, s=19, max_d=args.profile_max_d)
    rows, row_summary = filtered_rows(records, base_support, d=args.d, s=19)
    result = {
        "schema": "exact_exchange_neighborhood_repair_v1",
        "field": "F2",
        "core": "E11 quotient core",
        "rank_s": 19,
        "base_support_source": "analysis augmented certificate separator trace-consistent 9-Wang-violation support unless --support is supplied",
        "base_support": base_support,
        "meaning": "Exact complete-Wang exchange-neighborhood model: rows with base slack >= d are omitted only because they cannot become violated within d exchanges. Feasibility is only an A-support/necessary-condition result, not a tensor decomposition.",
        "parameters": {
            "d": args.d,
            "profile_max_d": args.profile_max_d,
            "profile_only": bool(args.profile_only),
            "solver_time": args.solver_time,
            "workers": args.workers,
            "seed": args.seed,
            "trace_cuts": args.trace_cuts,
            "no_contraction_lb": bool(args.no_contraction_lb),
            "cert_cuts": bool(args.cert_cuts),
            "max_certs": args.max_certs,
            "max_size5_cuts": args.max_size5_cuts,
        },
        "complete_core_table_meta": meta,
        "base_slack_profile": profile,
        "selected_neighborhood_row_summary": row_summary,
    }
    if not args.profile_only:
        result["solve"] = solve_neighborhood(args, records, T_core, contractions, base_support, rows, row_summary)
    result["elapsed_sec"] = round(time.time() - t0, 3)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    summary = {
        "out": str(args.out),
        "d": args.d,
        "profile_rows_lt_d": profile["rows_with_slack_lt_d"],
        "base_violations": profile["violation_count"],
        "row_count_d": row_summary["row_count"],
        "status": result.get("solve", {}).get("status"),
        "complete_wang_after": result.get("solve", {}).get("complete_wang_scan", {}).get("complete_violation_count"),
        "elapsed_sec": result["elapsed_sec"],
    }
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
