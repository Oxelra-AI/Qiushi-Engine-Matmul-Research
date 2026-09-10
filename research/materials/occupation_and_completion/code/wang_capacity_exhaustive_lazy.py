#!/usr/bin/env python3
"""Exhaustive-cut lazy solver for Wang T-level occupation capacity.

Unlike the subset-span checker, this script scans every subspace in the expanded
Wang LUT for each candidate support and adds the actual violated raw LUT cuts.
This avoids relying on the recorded table already being monotone-closed under
inclusion.  Feasibility is trusted only after a full 8,283,458-subspace scan
finds no violation.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import (  # noqa: E402
    unpack_basis,
    subspace_points_from_basis,
    in_rowspace,
    matrix_rank_of_mask,
)

CANON_BY_RANK = {1: 1, 2: 1 | 16, 3: 1 | 16 | 256}


def load_lut(path: Path) -> Tuple[Dict[int, int], dict]:
    with path.open("rb") as f:
        payload = pickle.load(f)
    return payload["lut"], payload.get("meta", {})


def exhaustive_violations(lut: Dict[int, int], sol: Dict[int, int], s: int, max_add: int = 0) -> Tuple[List[dict], dict]:
    t0 = time.time()
    support = list(sol.items())
    violations = []
    by_dim_seen = Counter()
    by_dim_viol = Counter()
    by_lb_viol = Counter()
    checked = 0
    for key, lb in lut.items():
        basis = unpack_basis(key)
        occ = 0
        for p, mult in support:
            if in_rowspace(p, basis, n=9):
                occ += mult
        cap = s - lb
        if occ > cap:
            v = {"key": key, "dim": key & 0xF, "lb": lb, "cap": cap, "occupancy": occ, "excess": occ - cap, "basis": list(basis)}
            violations.append(v)
            by_dim_viol[v["dim"]] += 1
            by_lb_viol[lb] += 1
        by_dim_seen[key & 0xF] += 1
        checked += 1
    violations.sort(key=lambda v: (v["excess"], v["lb"], v["occupancy"], -v["dim"]), reverse=True)
    selected = violations[:max_add] if max_add and len(violations) > max_add else violations
    stats = {
        "checked_subspaces": checked,
        "elapsed_sec": time.time() - t0,
        "violation_count": len(violations),
        "selected_violation_count": len(selected),
        "violations_by_dim": dict(by_dim_viol),
        "violations_by_lb": dict(by_lb_viol),
        "seen_by_dim": dict(by_dim_seen),
        "max_excess": max((v["excess"] for v in violations), default=0),
    }
    return selected, stats


def solve(lut: Dict[int, int], s: int, outdir: Path, label: str, init_max_dim: int,
          max_iters: int, solver_time: float, max_add: int, branch_rank: int) -> dict:
    from ortools.sat.python import cp_model

    model = cp_model.CpModel()
    points = list(range(1, 512))
    x = {p: model.NewIntVar(0, s, f"x_{p}") for p in points}
    model.Add(sum(x[p] for p in points) == s)

    if branch_rank:
        canon = CANON_BY_RANK[branch_rank]
        model.Add(x[canon] >= 1)
        if branch_rank >= 2:
            for p in points:
                if matrix_rank_of_mask(p) < branch_rank:
                    model.Add(x[p] == 0)
        print(f"Branch rank={branch_rank}: fixed canonical rank-{branch_rank} point {canon}; excluded lower-rank points for rank>=2 branches")

    added = set()
    cuts = []

    def add_cut(v, reason: str) -> bool:
        key = v["key"] if isinstance(v, dict) else int(v)
        if key in added:
            return False
        lb = lut[key]
        cap = s - lb
        pts = subspace_points_from_basis(unpack_basis(key))
        model.Add(sum(x[p] for p in pts) <= cap)
        added.add(key)
        cuts.append({"key": key, "dim": key & 0xF, "lb": lb, "cap": cap, "point_count": len(pts), "reason": reason})
        return True

    t0 = time.time()
    for key in sorted(lut):
        d = key & 0xF
        if 1 <= d <= init_max_dim:
            add_cut(key, f"all_dim_le_{init_max_dim}_initial")
    print(f"Initial raw cuts dim<= {init_max_dim}: {len(added):,} in {time.time()-t0:.2f}s; by dim {dict(Counter(c['dim'] for c in cuts))}")

    history = []
    final_status = None
    final_solution = None
    for it in range(1, max_iters + 1):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = solver_time
        solver.parameters.num_search_workers = 8
        solver.parameters.random_seed = 9000 + it
        t_solve = time.time()
        status = solver.Solve(model)
        solve_elapsed = time.time() - t_solve
        status_name = {
            cp_model.OPTIMAL: "OPTIMAL",
            cp_model.FEASIBLE: "FEASIBLE",
            cp_model.INFEASIBLE: "INFEASIBLE",
            cp_model.MODEL_INVALID: "MODEL_INVALID",
            cp_model.UNKNOWN: "UNKNOWN",
        }.get(status, str(status))
        entry = {"iteration": it, "solver_status": status_name, "cut_count": len(added), "solve_elapsed_sec": solve_elapsed}
        print(f"[{label}] iter {it}: status={status_name}, cuts={len(added):,}, solve={solve_elapsed:.2f}s")
        if status in (cp_model.INFEASIBLE, cp_model.MODEL_INVALID):
            final_status = status_name
            history.append(entry)
            break
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            final_status = status_name
            history.append(entry)
            break
        sol = {p: solver.Value(var) for p, var in x.items() if solver.Value(var)}
        entry["solution"] = {str(k): v for k, v in sorted(sol.items())}
        entry["support_size"] = len(sol)
        entry["max_mult"] = max(sol.values()) if sol else 0
        entry["rank_count"] = dict(Counter(matrix_rank_of_mask(p) for p in sol for _ in range(sol[p])))
        violations, stats = exhaustive_violations(lut, sol, s, max_add=max_add)
        entry["exhaustive_check_stats"] = stats
        entry["violations_head"] = violations[:50]
        print(f"  support={len(sol)} maxmult={entry['max_mult']} ranks={entry['rank_count']} raw violations={stats['violation_count']:,} selected={len(violations):,} max_excess={stats['max_excess']} check={stats['elapsed_sec']:.2f}s")
        if stats["violation_count"] == 0:
            final_status = "CAPACITY_FEASIBLE_FULL_EXHAUSTIVE_CHECK"
            final_solution = sol
            history.append(entry)
            break
        nadd = 0
        for v in violations:
            if add_cut(v, f"exhaustive_lazy_iter_{it}"):
                nadd += 1
        entry["lazy_cuts_added"] = nadd
        print(f"  added {nadd:,} raw violated cuts")
        history.append(entry)
        if nadd == 0:
            final_status = "STALLED_NO_NEW_RAW_CUTS"
            final_solution = sol
            break

    result = {
        "problem": "T-level Wang occupation capacity exhaustive raw-cut lazy solve",
        "field": "F2",
        "rank_s": s,
        "label": label,
        "init_max_dim": init_max_dim,
        "max_add_per_iter": max_add,
        "branch_rank": branch_rank,
        "final_status": final_status,
        "final_solution": {str(k): v for k, v in sorted(final_solution.items())} if final_solution else None,
        "iterations": history,
        "cut_count": len(added),
        "cuts_by_dim": dict(Counter(c["dim"] for c in cuts)),
        "cuts_by_lb": dict(Counter(c["lb"] for c in cuts)),
        "cut_records_head": cuts[:100],
        "cut_records_tail": cuts[-100:],
    }
    outdir.mkdir(parents=True, exist_ok=True)
    outpath = outdir / f"exhaustive_{label}.json"
    outpath.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Saved {outpath}")
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--outdir", type=Path, default=Path("data/wang_capacity_exhaustive"))
    ap.add_argument("--rank", type=int, default=20)
    ap.add_argument("--label", default="s20_exhaustive")
    ap.add_argument("--init-max-dim", type=int, default=2)
    ap.add_argument("--max-iters", type=int, default=20)
    ap.add_argument("--solver-time", type=float, default=300.0)
    ap.add_argument("--max-add-per-iter", type=int, default=0, help="0 means add all raw violations")
    ap.add_argument("--branch-rank", type=int, choices=[0, 1, 2, 3], default=0)
    args = ap.parse_args()
    lut, meta = load_lut(args.lut)
    print(f"Loaded LUT {len(lut):,}; coverage_ok={meta.get('coverage_ok')}; conflicts={meta.get('conflict_count')}")
    solve(lut, args.rank, args.outdir, args.label, args.init_max_dim, args.max_iters, args.solver_time, args.max_add_per_iter, args.branch_rank)


if __name__ == "__main__":
    main()
