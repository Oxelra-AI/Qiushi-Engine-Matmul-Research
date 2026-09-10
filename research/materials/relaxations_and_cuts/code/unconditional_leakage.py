#!/usr/bin/env python3
r"""analysis: unconditional leakage inequality — no tightness guards.

Mathematical basis (projection argument):
For any source lambda and target mu with actual B/C factors,
project B-space modulo U_mu (prescribed col space of M_mu).
The projected M_lambda has rank r_lambda - d_B where d_B = dim(U_lam cap U_mu).
Shared terms (in I_lam cap I_mu) have B-factors in span(B_mu), which projects
to a space of dimension e_B(mu).  Non-shared terms contribute at most m_lam - h
projected dimensions.  Therefore:
    r_lam - d_B  <=  e_B(mu) + (m_lam - h)
    e_B(mu)  >=  h - d_B - (m_lam - r_lam)

Using h = (m_lam + m_mu - m_{lam+mu})/2:
    2 e_B(mu)  >=  2 r_lam - m_lam + m_mu - m_{lam+mu} - 2 d_B(lam,mu)

This holds for ALL sources lambda, not only tight ones.
At source tightness m_lam = r_lam, it reproduces the old bound.
Away from tightness, it weakens by m_lam - r_lam but remains active.

Part 1: Verify on rank-21 pool with actual B/C factors.
Part 2: Build CP-SAT model with unconditional constraints — no Boolean guards.
Part 3: Compare propagation with the old indicator/big-M models.
"""
from __future__ import annotations

import argparse
import collections
import json
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

import numpy as np

# Reuse analysis infrastructure
SCRIPTS = Path("scripts")
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import contraction_weight_excess_search as base  # noqa:E402

OUTDIR = Path("data/unconditional_leakage")
POOL_PATH = base.POOL_PATH

# ──────────────────────────────────────────────────────────────────
# Part 1: Verify the unconditional inequality on rank-21 pool
# ──────────────────────────────────────────────────────────────────

def _precompute_intersections():
    """Precompute dim(U_lam ∩ U_mu) and dim(V_lam ∩ V_mu) for all pairs once."""
    dB = {}
    dC = {}
    for lam in range(1, 256):
        sp_lam = base.SPACES[lam]
        for mu in range(1, 256):
            if lam == mu:
                dB[(lam, mu)] = sp_lam.r
                dC[(lam, mu)] = sp_lam.r
                continue
            sp_mu = base.SPACES[mu]
            dB[(lam, mu)] = base.intersection_dim(sp_lam.U, sp_mu.U)
            dC[(lam, mu)] = base.intersection_dim(sp_lam.V, sp_mu.V)
    return dB, dC


_DB_CACHE, _DC_CACHE = None, None


def get_intersection_dims():
    global _DB_CACHE, _DC_CACHE
    if _DB_CACHE is None:
        _DB_CACHE, _DC_CACHE = _precompute_intersections()
    return _DB_CACHE, _DC_CACHE


def verify_on_pool(max_rows: int = 0) -> dict:
    """Check the unconditional leakage inequality on actual decompositions."""
    pool = np.load(POOL_PATH)
    if max_rows > 0:
        pool = pool[:max_rows]

    dB_tbl, dC_tbl = get_intersection_dims()

    total_violations = 0
    total_checked = 0
    non_tight_active = 0
    non_tight_binding = 0
    tight_active = 0
    example_head = []

    targets = [mu for mu, sp in base.SPACES.items() if sp.rank_lam <= 2]
    sources = list(base.SPACES.keys())

    for idx, row in enumerate(pool):
        terms = base.row_to_terms(row)
        us = [u for u, _v, _w in terms]
        weights = base.support_weights(us)
        n_terms = len(terms)

        # Precompute actual B/C excess for all targets
        actual_excess = {}
        for mu in targets:
            sp_mu = base.SPACES[mu]
            m_mu = weights[mu]
            if m_mu < sp_mu.r:
                continue
            active_inds = [t for t in range(n_terms) if base.dot8(mu, us[t])]
            if not active_inds:
                continue
            b_cols = [int(terms[t][1]) for t in active_inds]
            c_rows = [int(terms[t][2]) for t in active_inds]
            actual_excess[mu] = (base.gf2_rank(b_cols) - sp_mu.r,
                                 base.gf2_rank(c_rows) - sp_mu.r)

        for mu in targets:
            if mu not in actual_excess:
                continue
            sp_mu = base.SPACES[mu]
            m_mu = weights[mu]
            actual_eB, actual_eC = actual_excess[mu]

            for lam in sources:
                if lam == mu:
                    continue
                sp_lam = base.SPACES[lam]
                m_lam = weights[lam]
                nu = lam ^ mu
                m_nu = base.m_from_weights(weights, nu, n_terms)
                is_tight = (m_lam == sp_lam.r)

                rhs_B = 2 * sp_lam.r - m_lam + m_mu - m_nu - 2 * dB_tbl[(lam, mu)]
                rhs_C = 2 * sp_lam.r - m_lam + m_mu - m_nu - 2 * dC_tbl[(lam, mu)]

                for side, rhs, actual_e in [("B", rhs_B, actual_eB), ("C", rhs_C, actual_eC)]:
                    total_checked += 1
                    if rhs > 0:
                        lb = (rhs + 1) // 2
                        if is_tight:
                            tight_active += 1
                        else:
                            non_tight_active += 1
                            if actual_e == lb:
                                non_tight_binding += 1
                        if 2 * actual_e < rhs:
                            total_violations += 1
                            if len(example_head) < 20:
                                example_head.append({
                                    "pool_row": idx, "source": lam, "target": mu,
                                    "side": side, "rhs_twice": rhs, "actual_excess": actual_e,
                                    "m_lam": m_lam, "r_lam": sp_lam.r, "m_mu": m_mu,
                                    "is_tight": is_tight,
                                })

    return {
        "pool_rows": int(pool.shape[0]),
        "total_pairs_checked": total_checked,
        "total_violations": total_violations,
        "tight_active_constraints": tight_active,
        "non_tight_active_constraints": non_tight_active,
        "non_tight_binding_constraints": non_tight_binding,
        "all_pass": total_violations == 0,
        "violation_examples": example_head,
    }


# ──────────────────────────────────────────────────────────────────
# Part 2: Precompute geometric constants
# ──────────────────────────────────────────────────────────────────

def precompute_intersection_dims() -> Tuple[Dict, Dict]:
    """Precompute dim(U_lam ∩ U_mu) and dim(V_lam ∩ V_mu) for all pairs."""
    dB = {}
    dC = {}
    for lam in range(1, 256):
        sp_lam = base.SPACES[lam]
        for mu in range(1, 256):
            if lam == mu:
                continue
            sp_mu = base.SPACES[mu]
            dB[(lam, mu)] = base.intersection_dim(sp_lam.U, sp_mu.U)
            dC[(lam, mu)] = base.intersection_dim(sp_lam.V, sp_mu.V)
    return dB, dC


# ──────────────────────────────────────────────────────────────────
# Part 3: Unconditional CP-SAT model
# ──────────────────────────────────────────────────────────────────

def unconditional_solve(args) -> dict:
    from ortools.sat.python import cp_model

    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    records, rec_meta = base.load_complete_records()
    source_ranks = base.parse_rank_set(args.source_ranks)
    target_ranks = base.parse_rank_set(args.target_ranks)
    scalar_ranks = base.parse_rank_set(args.scalar_ranks)
    s_rank = int(args.rank)

    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in base.POINTS}
    model.Add(sum(x.values()) == s_rank)

    # Contraction weights
    m = {}
    for lam in range(1, 256):
        var = model.NewIntVar(0, s_rank, f"m_{lam}")
        model.Add(var == sum(x[p] for p in base.POINTS if base.dot8(lam, p)))
        m[lam] = var

    def m_expr(nu: int):
        return s_rank if int(nu) == 0 else m[int(nu)]

    # Scalar bounds m_lam >= r_lam
    scalar_by_rank = collections.Counter()
    for lam, sp in base.SPACES.items():
        if sp.rank_lam in scalar_ranks:
            model.Add(m[lam] >= sp.r)
            scalar_by_rank[sp.rank_lam] += 1

    # Wang occupation
    wang_summary = base.add_wang_constraints(model, x, records, args.wang, s_rank)

    # Excess variables for targets (rank-1 and rank-2)
    target_lams = [lam for lam, sp in base.SPACES.items() if sp.rank_lam in target_ranks]
    eB = {}
    eC = {}
    for mu in target_lams:
        sp = base.SPACES[mu]
        max_side = base.N9 - sp.r
        eB[mu] = model.NewIntVar(0, max_side, f"eB_{mu}")
        eC[mu] = model.NewIntVar(0, max_side, f"eC_{mu}")
        # Sylvester budget
        model.Add(eB[mu] + eC[mu] <= m[mu] - sp.r)

    # Unconditional leakage inequalities — no tightness booleans
    # For every source lam and target mu:
    #   2 eB(mu) + m_lam >= 2 r_lam + m_mu - m_{lam+mu} - 2 dB(lam,mu)
    # equivalently:
    #   2 eB(mu) + m_lam - m_mu + m_{lam+mu} >= 2 r_lam - 2 dB(lam,mu)
    source_lams = [lam for lam, sp in base.SPACES.items() if sp.rank_lam in source_ranks]
    ineq_B = 0
    ineq_C = 0
    skip_B = 0
    skip_C = 0
    ineq_by_src_rank = collections.Counter()
    ineq_by_pair_rank = collections.Counter()

    for lam in source_lams:
        sp_lam = base.SPACES[lam]
        for mu in target_lams:
            if lam == mu:
                continue
            sp_mu = base.SPACES[mu]
            nu = lam ^ mu

            dU = base.intersection_dim(sp_lam.U, sp_mu.U)
            dV = base.intersection_dim(sp_lam.V, sp_mu.V)

            # Constant RHS: 2 r_lam - 2 d_B/d_C
            rhs_const_B = 2 * sp_lam.r - 2 * dU
            rhs_const_C = 2 * sp_lam.r - 2 * dV

            # Maximum possible RHS of 2*eB >= ... is achieved when
            # m_lam is minimal (= r_lam), m_mu maximal (=s_rank), m_nu minimal
            # We can skip if even then RHS <= 0
            mnu_lb = 0 if nu == 0 else (base.SPACES[nu].r if base.SPACES[nu].rank_lam in scalar_ranks else 0)
            maxrhs_B = rhs_const_B - sp_lam.r + s_rank - mnu_lb  # = r_lam + s_rank - mnu_lb - 2dU
            maxrhs_C = rhs_const_C - sp_lam.r + s_rank - mnu_lb

            # B side: 2*eB[mu] + m[lam] - m[mu] + m_expr(nu) >= rhs_const_B
            if maxrhs_B > 0 and rhs_const_B > -(s_rank + s_rank):
                # The constraint: 2*eB[mu] + m[lam] - m[mu] + m_expr(nu) >= rhs_const_B
                if nu == 0:
                    # m_expr(nu) = s_rank (constant)
                    model.Add(2 * eB[mu] + m[lam] - m[mu] >= rhs_const_B - s_rank)
                else:
                    model.Add(2 * eB[mu] + m[lam] - m[mu] + m[int(nu)] >= rhs_const_B)
                ineq_B += 1
            else:
                skip_B += 1

            # C side: 2*eC[mu] + m[lam] - m[mu] + m_expr(nu) >= rhs_const_C
            if maxrhs_C > 0 and rhs_const_C > -(s_rank + s_rank):
                if nu == 0:
                    model.Add(2 * eC[mu] + m[lam] - m[mu] >= rhs_const_C - s_rank)
                else:
                    model.Add(2 * eC[mu] + m[lam] - m[mu] + m[int(nu)] >= rhs_const_C)
                ineq_C += 1
            else:
                skip_C += 1

            if maxrhs_B > 0 or maxrhs_C > 0:
                ineq_by_src_rank[sp_lam.rank_lam] += int(maxrhs_B > 0) + int(maxrhs_C > 0)
                ineq_by_pair_rank[(sp_lam.rank_lam, sp_mu.rank_lam)] += int(maxrhs_B > 0) + int(maxrhs_C > 0)

    excess_summary = {
        "enabled": True,
        "mode": "unconditional",
        "source_ranks": list(source_ranks),
        "target_ranks": list(target_ranks),
        "target_count": len(target_lams),
        "source_count": len(source_lams),
        "excess_variables": 2 * len(target_lams),
        "tight_booleans": 0,  # NO tightness booleans
        "leakage_inequalities_B": ineq_B,
        "leakage_inequalities_C": ineq_C,
        "skipped_trivial_B": skip_B,
        "skipped_trivial_C": skip_C,
        "ineq_by_source_rank": {str(k): int(v) for k, v in sorted(ineq_by_src_rank.items())},
        "ineq_by_source_target_rank": {str(k): int(v) for k, v in sorted(ineq_by_pair_rank.items(), key=lambda kv: str(kv[0]))},
    }

    # Weight variables
    total_weight = model.NewIntVar(0, base.NS * s_rank, "total_A_weight")
    model.Add(total_weight == sum(int(p).bit_count() * x[p] for p in base.POINTS))
    if args.min_weight is not None:
        model.Add(total_weight >= int(args.min_weight))
    if args.max_weight is not None:
        model.Add(total_weight <= int(args.max_weight))
    if getattr(args, 'minimize_weight', False):
        model.Minimize(total_weight)
    if getattr(args, 'maximize_weight', False):
        model.Maximize(total_weight)

    build_sec = round(time.time() - t0, 3)

    # Solve loop
    rounds = []
    candidate_found = None
    already_extra: set = set()
    from contraction_weight_excess_search import complete_core_wang_scan  # type: ignore
    for rnd in range(int(args.max_rounds)):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(args.solver_time)
        solver.parameters.num_search_workers = int(args.workers)
        solver.parameters.random_seed = int(args.seed + rnd)
        if getattr(args, 'log_search', False):
            solver.parameters.log_search_progress = True
        ts = time.time()
        status = solver.Solve(model)
        solve_sec = round(time.time() - ts, 3)
        status_name = solver.StatusName(status)
        rec = {"round": rnd, "status": status_name, "solve_sec": solve_sec}
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rounds.append(rec)
            break
        A = [p for p in base.POINTS if solver.Value(x[p])]
        tw = int(solver.Value(total_weight))
        weights = {lam: int(solver.Value(m[lam])) for lam in range(1, 256)}
        ex_eval = base.check_excess_from_weights(weights, total_terms=s_rank,
                                                  source_ranks=source_ranks,
                                                  target_ranks=target_ranks,
                                                  scalar_ranks=scalar_ranks, head_limit=10)
        scan = complete_core_wang_scan(f"uncond_round_{rnd}", A, s_rank, records, max_head=12)
        rec.update({
            "A_support": A,
            "total_A_weight": tw,
            "distinct_A": len(set(A)),
            "excess_eval_feasible": ex_eval["feasible_excess_assignment"],
            "complete_wang_violations": scan["complete_violation_count"],
        })
        rounds.append(rec)
        if scan["complete_violation_count"] == 0 and ex_eval["feasible_excess_assignment"]:
            candidate_found = {"round": rnd, "A_support": A, "total_A_weight": tw}
            break
        model.Add(sum(x[p] for p in A) <= s_rank - 1)

    result = {
        "schema": "s0908_unconditional_leakage_v1",
        "purpose": "CP-SAT support search with UNCONDITIONAL leakage inequalities — no tightness guards, no big-M.",
        "build_sec": build_sec,
        "constraint_summary": {
            "rank": s_rank,
            "distinct_points": len(base.POINTS),
            "scalar_bounds": {"count": sum(scalar_by_rank.values()), "by_rank": {str(k): int(v) for k, v in sorted(scalar_by_rank.items())}},
            "wang": wang_summary,
            "excess": excess_summary,
        },
        "candidate_found": candidate_found,
        "last": {
            "round": rounds[-1]["round"] if rounds else None,
            "status": rounds[-1]["status"] if rounds else None,
            "solve_sec": rounds[-1]["solve_sec"] if rounds else None,
        },
        "elapsed_sec": round(time.time() - t0, 3),
        "out": str(args.out),
    }
    return result


# ──────────────────────────────────────────────────────────────────
# Part 4: Comparison with tight-only filter
# ──────────────────────────────────────────────────────────────────

def compare_tight_vs_unconditional(us: Sequence[int]) -> dict:
    """For a given A-list, compare tight-only vs unconditional leakage bounds."""
    dB_tbl, dC_tbl = get_intersection_dims()
    weights = base.support_weights(us)
    n = len(us)

    tight_violations = []
    uncond_violations = []
    uncond_extra = []  # constraints that give info only in unconditional mode

    for mu, sp_mu in base.SPACES.items():
        if sp_mu.rank_lam > 2:
            continue
        m_mu = weights[mu]
        if m_mu < sp_mu.r:
            continue
        budget = m_mu - sp_mu.r

        tight_eB_lb = 0
        tight_eC_lb = 0
        uncond_eB_lb = 0
        uncond_eC_lb = 0

        for lam, sp_lam in base.SPACES.items():
            if lam == mu:
                continue
            m_lam = weights[lam]
            nu = lam ^ mu
            m_nu = base.m_from_weights(weights, nu, n)
            is_tight = (m_lam == sp_lam.r)

            dU = dB_tbl[(lam, mu)]
            dV = dC_tbl[(lam, mu)]

            # Unconditional bound (always active)
            rhs_B = 2 * sp_lam.r - m_lam + m_mu - m_nu - 2 * dU
            rhs_C = 2 * sp_lam.r - m_lam + m_mu - m_nu - 2 * dV
            lb_B = max(0, (rhs_B + 1) // 2) if rhs_B > 0 else 0
            lb_C = max(0, (rhs_C + 1) // 2) if rhs_C > 0 else 0
            if lb_B > uncond_eB_lb:
                uncond_eB_lb = lb_B
            if lb_C > uncond_eC_lb:
                uncond_eC_lb = lb_C

            if is_tight:
                # At tightness, m_lam = r_lam, so rhs becomes r_lam + m_mu - m_nu - 2d
                # This is the old bound
                t_rhs_B = sp_lam.r + m_mu - m_nu - 2 * dU  # same as unconditional at tightness
                t_rhs_C = sp_lam.r + m_mu - m_nu - 2 * dV
                t_lb_B = max(0, (t_rhs_B + 1) // 2) if t_rhs_B > 0 else 0
                t_lb_C = max(0, (t_rhs_C + 1) // 2) if t_rhs_C > 0 else 0
                if t_lb_B > tight_eB_lb:
                    tight_eB_lb = t_lb_B
                if t_lb_C > tight_eC_lb:
                    tight_eC_lb = t_lb_C
            elif lb_B > 0 or lb_C > 0:
                uncond_extra.append({
                    "source": lam, "target": mu, "m_lam": m_lam, "r_lam": sp_lam.r,
                    "lb_B": lb_B, "lb_C": lb_C, "slack": m_lam - sp_lam.r,
                })

        tight_total = tight_eB_lb + tight_eC_lb
        uncond_total = uncond_eB_lb + uncond_eC_lb

        if tight_total > budget:
            tight_violations.append({"target": mu, "eB_lb": tight_eB_lb, "eC_lb": tight_eC_lb, "budget": budget})
        if uncond_total > budget:
            uncond_violations.append({"target": mu, "eB_lb": uncond_eB_lb, "eC_lb": uncond_eC_lb, "budget": budget})

    return {
        "tight_violations": len(tight_violations),
        "uncond_violations": len(uncond_violations),
        "uncond_extra_active_pairs": len(uncond_extra),
        "uncond_extra_head": uncond_extra[:10] if uncond_extra else [],
    }


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd")

    # Verify on pool
    p_ver = sub.add_parser("verify", help="Verify unconditional inequality on rank-21 pool")
    p_ver.add_argument("--max-rows", type=int, default=0)
    p_ver.add_argument("--out", default=str(OUTDIR / "pool_verification.json"))

    # Solve
    p_sol = sub.add_parser("solve", help="CP-SAT support search with unconditional leakage")
    p_sol.add_argument("--wang", default="complete", choices=["reduced", "complete", "none"])
    p_sol.add_argument("--solver-time", type=float, default=90)
    p_sol.add_argument("--max-rounds", type=int, default=3)
    p_sol.add_argument("--workers", type=int, default=8)
    p_sol.add_argument("--seed", type=int, default=42)
    p_sol.add_argument("--rank", type=int, default=19)
    p_sol.add_argument("--source-ranks", default="all")
    p_sol.add_argument("--target-ranks", default="1,2")
    p_sol.add_argument("--scalar-ranks", default="all")
    p_sol.add_argument("--min-weight", type=int, default=None)
    p_sol.add_argument("--max-weight", type=int, default=None)
    p_sol.add_argument("--minimize-weight", action="store_true")
    p_sol.add_argument("--maximize-weight", action="store_true")
    p_sol.add_argument("--log-search", action="store_true")
    p_sol.add_argument("--out", default=str(OUTDIR / "unconditional_solve.json"))

    # Compare
    p_cmp = sub.add_parser("compare", help="Compare tight-only vs unconditional on same-W family")
    p_cmp.add_argument("--max-samew", type=int, default=200)
    p_cmp.add_argument("--out", default=str(OUTDIR / "tight_vs_unconditional.json"))

    args = ap.parse_args()
    OUTDIR.mkdir(parents=True, exist_ok=True)

    if args.cmd == "verify":
        result = verify_on_pool(max_rows=args.max_rows)
        outpath = Path(args.out)
        outpath.parent.mkdir(parents=True, exist_ok=True)
        with open(outpath, "w") as f:
            json.dump(result, f, indent=2, sort_keys=True)
        print(json.dumps({k: v for k, v in result.items() if k != "violation_examples"}, indent=2, sort_keys=True))

    elif args.cmd == "solve":
        result = unconditional_solve(args)
        outpath = Path(args.out)
        outpath.parent.mkdir(parents=True, exist_ok=True)
        with open(outpath, "w") as f:
            json.dump(result, f, indent=2, sort_keys=True)
        print(json.dumps(result, indent=2, sort_keys=True))

    elif args.cmd == "compare":
        t0 = time.time()
        # Load same-W deletion lists and test on shadow+purity survivors
        samew = base.same_w_deletion_lists()[:args.max_samew]
        records = []
        for i, rec in enumerate(samew):
            us = [int(u) for u in rec["u_masks"]]
            sh = base.shadow_consistent(us)
            cp = base.coord_purity_pass(us)
            if not (sh is True and cp is True):
                continue
            comp = compare_tight_vs_unconditional(us)
            records.append({"index": i, "us_head": us[:5], **comp})

        # Also test L15 and analysis
        known = {
            "L15": [1, 2, 3, 4, 8, 20, 24, 31, 32, 64, 73, 109, 127, 128, 141, 160, 182, 192, 219],
            "analysis": [1, 2, 3, 4, 8, 20, 24, 31, 32, 36, 64, 73, 127, 128, 141, 160, 182, 192, 219],
        }
        known_results = {name: compare_tight_vs_unconditional(us) for name, us in known.items()}

        result = {
            "elapsed_sec": round(time.time() - t0, 3),
            "samew_shadow_purity_tested": len(records),
            "known": known_results,
            "samew_head": records[:20],
            "summary": {
                "tight_only_rejects": sum(1 for r in records if r["tight_violations"] > 0),
                "uncond_rejects": sum(1 for r in records if r["uncond_violations"] > 0),
                "uncond_improves_tight": sum(1 for r in records if r["uncond_violations"] > r["tight_violations"]),
            },
        }
        outpath = Path(args.out)
        outpath.parent.mkdir(parents=True, exist_ok=True)
        with open(outpath, "w") as f:
            json.dump(result, f, indent=2, sort_keys=True)
        print(json.dumps({k: v for k, v in result.items() if k not in ("samew_head",)}, indent=2, sort_keys=True))

    else:
        ap.print_help()


if __name__ == "__main__":
    main()
