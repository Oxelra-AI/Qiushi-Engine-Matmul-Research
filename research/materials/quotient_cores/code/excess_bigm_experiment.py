#!/usr/bin/env python3
r"""analysisb: big-M version of the contraction-weight excess support model.

The analysis main script encodes the guarded leakage inequalities with a Boolean
`tight_lambda` for each source.  This script uses the equivalent necessary
big-M relaxation

  2 e_B(mu) >= r_lam + m_mu - m_{lam+mu} - 2 dim(U_lam cap U_mu)
                - K_{lam,mu,B}(m_lam-r_lam)

where K is chosen so the inequality is vacuous whenever m_lam >= r_lam+1.
The guard remains the final equality m_lam=r_lam; this is just a different
CP-SAT representation intended to test propagation in the actual support model.
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
import contraction_weight_excess_search as base  # type: ignore  # noqa:E402

OUTDIR = Path("data/contraction_weight_excess")


def bigm_solve(args) -> dict:
    from ortools.sat.python import cp_model

    t0 = time.time()
    records, rec_meta = base.load_complete_records()
    source_ranks = base.parse_rank_set(args.source_ranks)
    target_ranks = base.parse_rank_set(args.target_ranks)
    scalar_ranks = base.parse_rank_set(args.scalar_ranks)
    s_rank = int(args.rank)

    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in base.POINTS}
    model.Add(sum(x.values()) == s_rank)

    m = {}
    for lam in range(1, 256):
        var = model.NewIntVar(0, s_rank, f"m_{lam}")
        model.Add(var == sum(x[p] for p in base.POINTS if base.dot8(lam, p)))
        m[lam] = var

    def m_expr(nu: int):
        return s_rank if int(nu) == 0 else m[int(nu)]

    scalar_by_rank = collections.Counter()
    for lam, sp in base.SPACES.items():
        if sp.rank_lam in scalar_ranks:
            model.Add(m[lam] >= sp.r)
            scalar_by_rank[sp.rank_lam] += 1

    wang_summary = base.add_wang_constraints(model, x, records, args.wang, s_rank)

    eB = {}
    eC = {}
    target_lams = [lam for lam, sp in base.SPACES.items() if sp.rank_lam in target_ranks]
    for mu in target_lams:
        sp = base.SPACES[mu]
        max_side = base.N9 - sp.r
        eB[mu] = model.NewIntVar(0, max_side, f"eB_{mu}")
        eC[mu] = model.NewIntVar(0, max_side, f"eC_{mu}")
        model.Add(eB[mu] + eC[mu] <= m[mu] - sp.r)

    source_lams = [lam for lam, sp in base.SPACES.items() if sp.rank_lam in source_ranks]
    ineq_added_B = 0
    ineq_added_C = 0
    bigM_hist = collections.Counter()
    pair_hist = collections.Counter()
    # We use scalar lower bounds on m_{lam+mu} when present to minimize M.  If
    # lambda+mu has a rank outside the chosen scalar baseline, the lower bound is 0.
    for lam in source_lams:
        sp_lam = base.SPACES[lam]
        for mu in target_lams:
            if lam == mu:
                continue
            sp_mu = base.SPACES[mu]
            nu = lam ^ mu
            mnu_lb = 0 if nu == 0 else (base.SPACES[nu].r if base.SPACES[nu].rank_lam in scalar_ranks else 0)
            for side, evar, inter in [
                ("B", eB[mu], base.intersection_dim(sp_lam.U, sp_mu.U)),
                ("C", eC[mu], base.intersection_dim(sp_lam.V, sp_mu.V)),
            ]:
                rhsmax = sp_lam.r + s_rank - mnu_lb - 2 * inter
                if rhsmax <= 0:
                    continue
                K = int(rhsmax)
                # If m_lam=r_lam this is exactly the leakage lower bound.  If
                # m_lam>=r_lam+1, RHS is <=0 by construction, so the inequality is vacuous.
                # CP-SAT's Python linear-expression overloads are fragile for chained
                # subtraction of affine expressions, so encode the equivalent form
                #   2e + K m_lam - m_mu + m_{lam+mu} >= r_lam + K r_lam - 2 inter.
                rhs = sp_lam.r + K * sp_lam.r - 2 * inter
                if nu == 0:
                    model.Add(2 * evar + K * m[lam] - m[mu] >= rhs - s_rank)
                else:
                    model.Add(2 * evar + K * m[lam] - m[mu] + m[int(nu)] >= rhs)
                if side == "B":
                    ineq_added_B += 1
                else:
                    ineq_added_C += 1
                bigM_hist[K] += 1
                pair_hist[(sp_lam.rank_lam, sp_mu.rank_lam)] += 1

    total_weight = model.NewIntVar(0, base.NS * s_rank, "total_A_weight")
    model.Add(total_weight == sum(int(p).bit_count() * x[p] for p in base.POINTS))
    if args.target_weight is not None:
        model.Add(total_weight == int(args.target_weight))
    if args.min_weight is not None:
        model.Add(total_weight >= int(args.min_weight))
    if args.max_weight is not None:
        model.Add(total_weight <= int(args.max_weight))
    if args.minimize_weight:
        model.Minimize(total_weight)

    build_sec = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = int(args.workers)
    solver.parameters.random_seed = int(args.seed)
    ts = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - ts
    status_name = solver.StatusName(status)

    round_rec = {"status": status_name, "solve_sec": round(solve_sec, 3), "response_stats": solver.ResponseStats()}
    candidate = None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A = [p for p in base.POINTS if solver.Value(x[p])]
        weights = {lam: int(solver.Value(m[lam])) for lam in range(1, 256)}
        ex_eval = base.check_excess_from_weights(weights, total_terms=s_rank, source_ranks=source_ranks,
                                                  target_ranks=target_ranks, scalar_ranks=scalar_ranks, head_limit=12)
        scan = base.complete_core_wang_scan("bigm", A, s_rank, records, max_head=12)
        round_rec.update({
            "A_support": A,
            "total_A_weight": int(solver.Value(total_weight)),
            "excess_eval": ex_eval,
            "complete_wang_scan": {k: scan[k] for k in ["complete_violation_count", "max_excess", "violations_by_dim8", "violations_by_full_lut_L", "violations_by_excess", "violations_head"]},
        })
        if scan["complete_violation_count"] == 0 and ex_eval["feasible_excess_assignment"]:
            candidate = {"A_support": A, "total_A_weight": int(solver.Value(total_weight)), "meaning": "A-level necessary-condition candidate; not a B/C completion."}

    result = {
        "schema": "s0908_excess_bigm_experiment_v1",
        "purpose": "Compare big-M contraction-weight excess propagation with the indicator encoding in the actual E11 support occupation model.",
        "parameters": vars(args) | {"out": str(args.out)},
        "complete_records_meta": rec_meta,
        "constraint_summary": {
            "rank": s_rank,
            "wang": wang_summary,
            "scalar_bounds": {"count": sum(scalar_by_rank.values()), "by_rank": {str(k): int(v) for k, v in sorted(scalar_by_rank.items())}},
            "excess_encoding": "bigM_final_tightness_guard",
            "source_ranks": list(source_ranks),
            "target_ranks": list(target_ranks),
            "excess_variables": 2 * len(target_lams),
            "leakage_inequalities_B": ineq_added_B,
            "leakage_inequalities_C": ineq_added_C,
            "bigM_hist_head": {str(k): int(v) for k, v in sorted(bigM_hist.items())[:50]},
            "ineq_by_source_target_rank": {str(k): int(v) for k, v in sorted(pair_hist.items(), key=lambda kv: str(kv[0]))},
            "weight_bounds": {"target": args.target_weight, "min": args.min_weight, "max": args.max_weight, "minimize": args.minimize_weight},
        },
        "model_stats": model.ModelStats(),
        "build_sec": round(build_sec, 3),
        "round": round_rec,
        "candidate_found": candidate,
        "elapsed_sec": round(time.time() - t0, 3),
        "interpretation": "Feasible/UNKNOWN/UNSAT statuses are experimental unless accompanied by an independently checked proof certificate; feasible supports still need shadow and exact B/C completion.",
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=OUTDIR / "bigm_result.json")
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--wang", choices=["none", "reduced", "complete"], default="reduced")
    ap.add_argument("--source-ranks", default="123")
    ap.add_argument("--target-ranks", default="12")
    ap.add_argument("--scalar-ranks", default="123")
    ap.add_argument("--solver-time", type=float, default=60.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=1040)
    ap.add_argument("--target-weight", type=int, default=None)
    ap.add_argument("--min-weight", type=int, default=None)
    ap.add_argument("--max-weight", type=int, default=None)
    ap.add_argument("--minimize-weight", action="store_true")
    args = ap.parse_args()
    result = bigm_solve(args)
    r = result["round"]
    brief = {k: r.get(k) for k in ["status", "solve_sec", "total_A_weight"]}
    if "complete_wang_scan" in r:
        brief["complete_wang_viol"] = r["complete_wang_scan"]["complete_violation_count"]
    if "excess_eval" in r:
        brief["excess_feasible"] = r["excess_eval"]["feasible_excess_assignment"]
        brief["scalar_viol"] = r["excess_eval"]["scalar_violation_count"]
        brief["leak_viol"] = r["excess_eval"]["leakage_violation_count"]
    print(json.dumps({
        "out": str(args.out),
        "build_sec": result["build_sec"],
        "constraint_summary": result["constraint_summary"],
        "model_stats": result["model_stats"],
        "round": brief,
        "candidate_found": result["candidate_found"],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True)[:12000])


if __name__ == "__main__":
    main()
