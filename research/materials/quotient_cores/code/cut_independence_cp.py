#!/usr/bin/env python3
r"""analysisc: test mixed-source cuts against the complete Wang occupation model.

For selected mixed-source support inequalities, minimize their left side over all
19-point distinct E11 supports satisfying every canonical Wang occupation row.
If the solver returns a concrete support with lhs<K, the cut is not implied by the
complete Wang table (the witness is independently rescanned).  If the solver only
returns UNKNOWN, no mathematical implication is established.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

SCRIPTS = Path("scripts")
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import contraction_weight_excess_search as base  # noqa:E402
import mixed_source_cuts as cuts  # noqa:E402

OUTDIR = Path("data/mixed_source_cuts")


def solve_one(mu: int, lam: int, nu: int, time_limit: float = 120.0, workers: int = 8, seed: int = 123) -> dict:
    from ortools.sat.python import cp_model
    t0 = time.time()
    records, rec_meta = base.load_complete_records()
    cp = cuts.cut_params(mu, lam, nu)
    bs1 = int(cp["coeff1_bitset"])
    bs2 = int(cp["coeff2_bitset"])
    K = int(cp["K"])

    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in base.POINTS}
    model.Add(sum(x.values()) == 19)
    wang_summary = base.add_wang_constraints(model, x, records, "complete", 19)
    # Redundant scalar lower bounds often help propagation.
    m_vars = {}
    for a, sp in base.SPACES.items():
        v = model.NewIntVar(0, 19, f"m_{a}")
        model.Add(v == sum(x[p] for p in base.POINTS if base.dot8(a, p)))
        model.Add(v >= sp.r)
        m_vars[a] = v
    lhs_expr = sum((2 if ((bs2 >> (p-1)) & 1) else (1 if ((bs1 >> (p-1)) & 1) else 0)) * x[p] for p in base.POINTS)
    model.Minimize(lhs_expr)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = int(seed)
    ts = time.time()
    status = solver.Solve(model)
    solve_sec = round(time.time() - ts, 3)
    status_name = solver.StatusName(status)

    sol = None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A = [p for p in base.POINTS if solver.Value(x[p])]
        lhs = sum((2 if ((bs2 >> (p-1)) & 1) else (1 if ((bs1 >> (p-1)) & 1) else 0)) for p in A)
        scan = base.complete_core_wang_scan(f"cut_{mu}_{lam}_{nu}", A, 19, records, max_head=5)
        lhs_check = cuts.cut_lhs_for_support(mu, lam, nu, A)
        sol = {
            "A_support": A,
            "lhs": int(lhs),
            "lhs_check": lhs_check,
            "violates_cut": bool(lhs < K),
            "complete_wang_violations": int(scan["complete_violation_count"]),
            "wang_scan_head": scan["violations_head"],
            "total_A_weight": int(sum(int(p).bit_count() for p in A)),
            "objective_bound": None if status != cp_model.FEASIBLE else solver.BestObjectiveBound(),
        }
    return {
        "schema": "s0908_cut_independence_cp_v1",
        "purpose": "Minimize one mixed cut over all complete-Wang-admissible distinct 19-point supports; a concrete violating support proves the cut is not implied by Wang occupation alone.",
        "triple": {k: v for k, v in cp.items() if k not in ("coeff1_bitset", "coeff2_bitset", "positive_bitset")},
        "solver": {"status": status_name, "solve_sec": solve_sec, "time_limit": float(time_limit), "workers": int(workers)},
        "wang_summary": wang_summary,
        "solution": sol,
        "elapsed_sec": round(time.time() - t0, 3),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--triple", nargs=3, action="append", metavar=("MU", "LAM", "NU"), help="Analyze one triple. Can be repeated.")
    ap.add_argument("--preset", choices=["analysis", "topgap"], default="analysis")
    ap.add_argument("--time", type=float, default=120.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--out", default=str(OUTDIR / "cut_independence_cp.json"))
    args = ap.parse_args()
    triples = []
    if args.triple:
        triples.extend([(int(a), int(b), int(c)) for a, b, c in args.triple])
    elif args.preset == "analysis":
        triples = [
            (18, 5, 34),   # L15 best non-single-dominated
            (27, 5, 35),   # L15 second best non-single-dominated
            (27, 6, 131),  # analysis best non-single-dominated
        ]
    elif args.preset == "topgap":
        triples = [(1, 48, 48), (1, 50, 50), (1, 52, 52)]
    out = {"schema": "s0908_cut_independence_batch_v1", "triples": []}
    for i, (mu, lam, nu) in enumerate(triples):
        rec = solve_one(mu, lam, nu, time_limit=args.time, workers=args.workers, seed=123+i)
        out["triples"].append(rec)
        print(json.dumps({
            "triple": [mu, lam, nu],
            "K": rec["triple"]["K"],
            "L_D": rec["triple"]["single_wang"]["L_D"],
            "status": rec["solver"]["status"],
            "solve_sec": rec["solver"]["solve_sec"],
            "lhs": None if rec["solution"] is None else rec["solution"]["lhs"],
            "violates_cut": None if rec["solution"] is None else rec["solution"]["violates_cut"],
            "wang_violations": None if rec["solution"] is None else rec["solution"]["complete_wang_violations"],
        }, sort_keys=True))
    out["elapsed_sec"] = round(sum(r["elapsed_sec"] for r in out["triples"]), 3)
    outpath = Path(args.out)
    outpath.parent.mkdir(parents=True, exist_ok=True)
    with outpath.open("w") as f:
        json.dump(out, f, indent=2, sort_keys=True)


if __name__ == "__main__":
    main()
