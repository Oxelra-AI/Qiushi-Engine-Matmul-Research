#!/usr/bin/env python3
r"""analysisg: CP-SAT support search with direct mixed-source cuts.

This model uses the small-coefficient inequalities
    sum_p c_p x_p >= K, c_p in {0,1,2}
exported by mixed_source_cuts.py.  The goal is to test propagation and
candidate generation relative to the auxiliary eB/eC formulation; UNKNOWN remains
only computational information.
"""
from __future__ import annotations

import argparse
import collections
import json
import sys
import time
from pathlib import Path

SCRIPTS = Path("scripts")
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import contraction_weight_excess_search as base  # noqa:E402
import mixed_source_cuts as cutsmod  # noqa:E402

OUTDIR = Path("data/mixed_source_cuts")


def load_cut_records(path: Path, max_cuts: int, min_gap: int, min_K: int):
    with path.open() as f:
        payload = json.load(f)
    out = []
    for rec in payload["cuts"]:
        if int(rec["gap_K_minus_LD"]) < min_gap or int(rec["K"]) < min_K:
            continue
        out.append(rec)
        if max_cuts and len(out) >= max_cuts:
            break
    return out, {k: payload.get(k) for k in ("raw_nondominated_triples", "unique_patterns", "truncated", "gap_hist_unique", "K_hist_unique", "dual_dim_hist_unique")}


def solve(args) -> dict:
    from ortools.sat.python import cp_model
    t0 = time.time()
    records, rec_meta = base.load_complete_records()
    cut_records, cut_meta = load_cut_records(Path(args.cuts_path), args.max_cuts, args.min_gap, args.min_K)
    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in base.POINTS}
    model.Add(sum(x.values()) == args.rank)
    wang_summary = base.add_wang_constraints(model, x, records, args.wang, args.rank)
    scalar_by_rank = collections.Counter()
    for lam, sp in base.SPACES.items():
        if args.scalar:
            model.Add(sum(x[p] for p in base.POINTS if base.dot8(lam, p)) >= sp.r)
            scalar_by_rank[sp.rank_lam] += 1
    added = 0
    by_gap = collections.Counter(); by_K = collections.Counter(); by_dim = collections.Counter()
    for rec in cut_records:
        bs1 = int(rec["coeff1_bitset"]); bs2 = int(rec["coeff2_bitset"]); K = int(rec["K"])
        terms = []
        for p in base.POINTS:
            if (bs2 >> (p-1)) & 1:
                terms.append(2 * x[p])
            elif (bs1 >> (p-1)) & 1:
                terms.append(x[p])
        model.Add(sum(terms) >= K)
        added += 1
        by_gap[int(rec["gap_K_minus_LD"])] += 1
        by_K[K] += 1
        by_dim[int(rec["dual_dim"])] += 1
    total_weight = model.NewIntVar(0, args.rank * 8, "total_A_weight")
    model.Add(total_weight == sum(int(p).bit_count() * x[p] for p in base.POINTS))
    if args.minimize_weight:
        model.Minimize(total_weight)
    build_sec = round(time.time() - t0, 3)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = int(args.workers)
    solver.parameters.random_seed = int(args.seed)
    if args.log_search:
        solver.parameters.log_search_progress = True
    ts = time.time()
    status = solver.Solve(model)
    solve_sec = round(time.time() - ts, 3)
    status_name = solver.StatusName(status)
    candidate = None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A = [p for p in base.POINTS if solver.Value(x[p])]
        scan = base.complete_core_wang_scan("direct_mixed_candidate", A, args.rank, records, max_head=10)
        # Evaluate all analysis unconditional eB/eC constraints as a cross-check.
        weights = base.support_weights(A)
        uncond_eval = None
        try:
            import unconditional_leakage as s11
            # compare_tight_vs_unconditional gives violation counts for final support.
            uncond_eval = s11.compare_tight_vs_unconditional(A)
        except Exception as exc:
            uncond_eval = {"error": repr(exc)}
        candidate = {
            "A_support": A,
            "total_A_weight": int(solver.Value(total_weight)),
            "complete_wang_violations": int(scan["complete_violation_count"]),
            "wang_scan_head": scan["violations_head"],
            "unconditional_compare": uncond_eval,
        }
    return {
        "schema": "s0908_direct_mixed_cut_cpsat_v1",
        "purpose": "Search distinct 19-point E11 supports using canonical Wang rows plus direct mixed-source small-coefficient support cuts.",
        "params": {"wang": args.wang, "rank": args.rank, "cuts_path": args.cuts_path, "max_cuts": args.max_cuts, "min_gap": args.min_gap, "min_K": args.min_K, "scalar": bool(args.scalar)},
        "build_sec": build_sec,
        "constraint_summary": {
            "wang": wang_summary,
            "scalar_by_rank": {str(k): int(v) for k, v in sorted(scalar_by_rank.items())},
            "direct_mixed_cuts": {"added": added, "by_gap": {str(k): int(v) for k, v in sorted(by_gap.items())}, "by_K": {str(k): int(v) for k, v in sorted(by_K.items())}, "by_dual_dim": {str(k): int(v) for k, v in sorted(by_dim.items())}, "source_meta": cut_meta},
        },
        "solver": {"status": status_name, "solve_sec": solve_sec, "time_limit": float(args.solver_time), "workers": int(args.workers)},
        "candidate": candidate,
        "elapsed_sec": round(time.time() - t0, 3),
        "out": args.out,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--wang", choices=["none", "reduced", "complete"], default="complete")
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--cuts-path", default=str(OUTDIR / "unique_nondominated_cuts_top50k.json"))
    ap.add_argument("--max-cuts", type=int, default=50000)
    ap.add_argument("--min-gap", type=int, default=3)
    ap.add_argument("--min-K", type=int, default=12)
    ap.add_argument("--scalar", action="store_true")
    ap.add_argument("--solver-time", type=float, default=120)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=6012)
    ap.add_argument("--minimize-weight", action="store_true")
    ap.add_argument("--log-search", action="store_true")
    ap.add_argument("--out", default=str(OUTDIR / "direct_mixed_cut_cpsat.json"))
    args = ap.parse_args()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    res = solve(args)
    with Path(args.out).open("w") as f:
        json.dump(res, f, indent=2, sort_keys=True)
    print(json.dumps(res, indent=2, sort_keys=True)[:12000])


if __name__ == "__main__":
    main()
