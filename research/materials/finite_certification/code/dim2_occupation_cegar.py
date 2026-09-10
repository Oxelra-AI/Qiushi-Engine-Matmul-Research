#!/usr/bin/env python3
"""Enumerate occupation-admissible dim-2 quotient supports and test B/C filters.

For one of the analysis orbit representatives W (481,482,483 by default), build
all inherited Wang occupation rows for a length-18 quotient support in F2^7,
solve the resulting finite support problem with CP-SAT, and after each support
is found run the dim2 quotient tight-trace linear test.  For distinct-support
systems, a found support is blocked by sum_{q in S} x_q <= 17 and the search
continues.

This is an execution probe for whether the remaining three quotient-rank
statements are enumerable.  Infeasibility after blocked trace-rejected supports
would be a coverage result for occupation + trace; otherwise the output records
trace-passing supports or the scale of the support family.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Sequence

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception as e:  # pragma: no cover
    cp_model = None

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))

from node_local_occupation_closure import LUT_PATH, node_constraints  # type: ignore
from dim2_quotient_det import orbit_basis, trace_analyze  # type: ignore


def popcount(x: int) -> int:
    return int(x).bit_count()


def load_lut():
    with LUT_PATH.open("rb") as f:
        d = pickle.load(f)
    return d["lut"] if isinstance(d, dict) and "lut" in d else d


def build_rows(orbit_index: int, target: int):
    W = orbit_basis(orbit_index)
    lut = load_lut()
    rows, meta = node_constraints(W, lut, target)
    # Remove tautological rows and convert to point lists 1..127.
    usable = []
    singleton_caps = {}
    for mask, cap in rows:
        pts = [i + 1 for i in range((1 << 7) - 1) if (mask >> i) & 1]
        if len(pts) == 1:
            singleton_caps[pts[0]] = min(singleton_caps.get(pts[0], 10**9), int(cap))
        if int(cap) < 0:
            usable.append((pts, int(cap), int(mask)))
        elif int(cap) < min(target, len(pts)):
            usable.append((pts, int(cap), int(mask)))
    distinct_forced = (len(singleton_caps) == 127 and max(singleton_caps.values()) <= 1)
    meta2 = dict(meta)
    meta2.update({
        "usable_rows": len(usable),
        "singleton_caps_count": len(singleton_caps),
        "singleton_cap_min": int(min(singleton_caps.values())) if singleton_caps else None,
        "singleton_cap_max": int(max(singleton_caps.values())) if singleton_caps else None,
        "singleton_cap_hist": dict(sorted((int(k), int(v)) for k, v in Counter(singleton_caps.values()).items())),
        "distinct_forced_by_singletons": bool(distinct_forced),
    })
    return W, usable, meta2


def solve_once(usable_rows, target: int, blocks: list[list[int]], time_limit: float, workers: int):
    if cp_model is None:
        return {"status": "NO_OR_TOOLS", "solution": None, "elapsed_sec": 0.0}
    model = cp_model.CpModel()
    xs = {q: model.NewBoolVar(f"x_{q}") for q in range(1, 128)}
    model.Add(sum(xs.values()) == target)
    for pts, cap, _mask in usable_rows:
        if cap < 0:
            model.Add(0 <= -1)
        else:
            model.Add(sum(xs[q] for q in pts) <= cap)
    for block in blocks:
        model.Add(sum(xs[q] for q in block) <= target - 1)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = 25025 + len(blocks)
    t0 = time.time()
    st = solver.Solve(model)
    elapsed = time.time() - t0
    name = solver.StatusName(st)
    sol = None
    if st in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        sol = [q for q in range(1, 128) if solver.Value(xs[q])]
    return {
        "status": name,
        "solution": sol,
        "elapsed_sec": elapsed,
        "conflicts": int(solver.NumConflicts()),
        "branches": int(solver.NumBranches()),
        "objective": None,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--orbit-index", type=int, required=True)
    ap.add_argument("--target", type=int, default=18)
    ap.add_argument("--max-solutions", type=int, default=100)
    ap.add_argument("--time-limit-per-round", type=float, default=30.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    t0 = time.time()
    W, rows, meta = build_rows(args.orbit_index, args.target)
    if not meta["distinct_forced_by_singletons"]:
        raise SystemExit("This enumerator currently assumes all multiplicities are forced <=1 by singleton rows; use an integer-vector enumerator otherwise.")
    rounds = []
    blocks: list[list[int]] = []
    trace_pass = []
    trace_reject = 0
    final_status = None
    for i in range(args.max_solutions):
        res = solve_once(rows, args.target, blocks, args.time_limit_per_round, args.workers)
        final_status = res["status"]
        rec = {"round": i, "solve": {k: v for k, v in res.items() if k != "solution"}}
        sol = res.get("solution")
        if not sol:
            rounds.append(rec)
            break
        tr = trace_analyze(W, sol)
        tr_summary = {
            "support": sol,
            "tight_lambda_count": tr["tight_lambda_count"],
            "tight_rank_hist": tr["tight_rank_hist"],
            "tensor_consistent": tr["tensor_consistent"],
            "full_trace_consistent": tr["full_trace_consistent"],
            "full_rank_aug": tr["full_rank_aug"],
            "elapsed_sec": tr["elapsed_sec"],
        }
        rec["trace"] = tr_summary
        rounds.append(rec)
        if tr["full_trace_consistent"]:
            trace_pass.append(sol)
            # Stop early: a trace-passing support is the next object for SAT.
            break
        trace_reject += 1
        blocks.append(sol)
    status_meaning = "trace_pass_found" if trace_pass else ("occupation_exhausted" if final_status == "INFEASIBLE" else final_status)
    out = {
        "schema": "dim2_occupation_cegar_v1",
        "orbit_index": int(args.orbit_index),
        "W_basis": [int(x) for x in W],
        "target": int(args.target),
        "row_meta": meta,
        "max_solutions": int(args.max_solutions),
        "rounds_completed": len(rounds),
        "blocked_trace_rejected_supports": int(trace_reject),
        "trace_pass_supports": trace_pass,
        "final_status": final_status,
        "status_meaning": status_meaning,
        "rounds": rounds,
        "elapsed_sec": time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(args.out),
        "orbit_index": args.orbit_index,
        "row_meta": meta,
        "rounds_completed": len(rounds),
        "blocked_trace_rejected_supports": trace_reject,
        "trace_pass_count": len(trace_pass),
        "final_status": final_status,
        "status_meaning": status_meaning,
        "elapsed_sec": out["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
