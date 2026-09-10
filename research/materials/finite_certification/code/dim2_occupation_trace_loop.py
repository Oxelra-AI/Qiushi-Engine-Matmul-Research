#!/usr/bin/env python3
"""CP-SAT loop over dim-2 quotient occupation multisets with trace testing.

Unlike dim2_occupation_cegar.py, this uses integer multiplicities x_q rather
than assuming distinct quotient directions.  It blocks exact integer vectors
with AddForbiddenAssignments and therefore can enumerate a bounded sequence of
occupation-admissible length-18 multisets for the three analysis terminal orbits.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:  # pragma: no cover
    cp_model = None

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))

from node_local_occupation_closure import LUT_PATH, node_constraints  # type: ignore
from dim2_quotient_det import orbit_basis, trace_analyze  # type: ignore


def load_lut():
    with LUT_PATH.open("rb") as f:
        d = pickle.load(f)
    return d["lut"] if isinstance(d, dict) and "lut" in d else d


def rows_for_orbit(orbit_index: int, target: int):
    W = orbit_basis(orbit_index)
    lut = load_lut()
    rows, meta = node_constraints(W, lut, target)
    usable = []
    singleton_caps = {}
    for mask, cap in rows:
        pts = [i + 1 for i in range((1 << 7) - 1) if (int(mask) >> i) & 1]
        if len(pts) == 1:
            singleton_caps[pts[0]] = min(singleton_caps.get(pts[0], target), int(cap))
        # For integer multiplicities, singleton cap=1 is not tautological; keep all cap<target.
        if int(cap) < target:
            usable.append((pts, int(cap), int(mask)))
    meta = dict(meta)
    meta.update({
        "usable_rows_integer": len(usable),
        "singleton_caps_count": len(singleton_caps),
        "singleton_cap_min": int(min(singleton_caps.values())) if singleton_caps else None,
        "singleton_cap_max": int(max(singleton_caps.values())) if singleton_caps else None,
        "singleton_cap_hist": dict(sorted((int(k), int(v)) for k, v in Counter(singleton_caps.values()).items())),
    })
    return W, usable, meta


def solve_round(rows, target: int, forbidden: list[list[int]], time_limit: float, workers: int, seed: int):
    if cp_model is None:
        return {"status": "NO_OR_TOOLS", "solution_vec": None, "elapsed_sec": 0.0}
    model = cp_model.CpModel()
    xs = [model.NewIntVar(0, target, f"x_{q}") for q in range(1, 128)]
    model.Add(sum(xs) == target)
    for pts, cap, _mask in rows:
        if cap < 0:
            model.Add(0 <= -1)
        else:
            model.Add(sum(xs[q - 1] for q in pts) <= cap)
    for vec in forbidden:
        # Exclude one exact multiplicity vector.  With 127 variables and a single tuple
        # this is compact enough for the bounded enumeration performed here.
        model.AddForbiddenAssignments(xs, [tuple(int(v) for v in vec)])
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = int(seed)
    t0 = time.time()
    st = solver.Solve(model)
    elapsed = time.time() - t0
    name = solver.StatusName(st)
    sol = None
    if st in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        sol = [int(solver.Value(x)) for x in xs]
    return {
        "status": name,
        "solution_vec": sol,
        "elapsed_sec": elapsed,
        "conflicts": int(solver.NumConflicts()),
        "branches": int(solver.NumBranches()),
    }


def vec_to_multiset(vec: list[int]) -> list[int]:
    out = []
    for i, m in enumerate(vec, start=1):
        out.extend([i] * int(m))
    return out


def support_summary(vec: list[int]) -> dict:
    nz = [(i + 1, int(v)) for i, v in enumerate(vec) if v]
    return {
        "support_nonzero_count": len(nz),
        "max_multiplicity": max((v for _i, v in nz), default=0),
        "solution_head": nz[:80],
        "solution_weight_check": sum(v for _i, v in nz),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--orbit-index", type=int, required=True)
    ap.add_argument("--target", type=int, default=18)
    ap.add_argument("--max-solutions", type=int, default=50)
    ap.add_argument("--time-limit-per-round", type=float, default=30.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--stop-on-trace-pass", action="store_true")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    t0 = time.time()
    W, rows, meta = rows_for_orbit(args.orbit_index, args.target)
    forbidden: list[list[int]] = []
    rounds = []
    trace_reject = 0
    trace_pass = []
    final_status = None
    for r in range(args.max_solutions):
        sol = solve_round(rows, args.target, forbidden, args.time_limit_per_round, args.workers, 25000 + 17 * r + args.orbit_index)
        final_status = sol["status"]
        rec = {"round": r, "solve": {k: v for k, v in sol.items() if k != "solution_vec"}}
        vec = sol.get("solution_vec")
        if vec is None:
            rounds.append(rec)
            break
        multiset = vec_to_multiset(vec)
        rec["support"] = support_summary(vec)
        tr = trace_analyze(W, multiset)
        rec["trace"] = {
            "full_trace_consistent": bool(tr["full_trace_consistent"]),
            "tensor_consistent": bool(tr["tensor_consistent"]),
            "full_rank_aug": tr["full_rank_aug"],
            "tight_lambda_count": tr["tight_lambda_count"],
            "tight_rank_hist": tr["tight_rank_hist"],
            "elapsed_sec": tr["elapsed_sec"],
        }
        if tr["full_trace_consistent"]:
            trace_pass.append(multiset)
            rec["trace_pass_multiset"] = multiset
            rounds.append(rec)
            if args.stop_on_trace_pass:
                break
        else:
            trace_reject += 1
            rounds.append(rec)
        forbidden.append(vec)
    meaning = "trace_pass_found" if trace_pass else ("occupation_exhausted" if final_status == "INFEASIBLE" else final_status)
    out = {
        "schema": "dim2_occupation_trace_loop_v1",
        "orbit_index": int(args.orbit_index),
        "W_basis": [int(x) for x in W],
        "target": int(args.target),
        "row_meta": meta,
        "rounds_completed": len(rounds),
        "blocked_vectors": len(forbidden),
        "trace_rejected_count": int(trace_reject),
        "trace_pass_count": len(trace_pass),
        "trace_pass_multisets": trace_pass,
        "final_status": final_status,
        "status_meaning": meaning,
        "rounds": rounds,
        "elapsed_sec": time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(args.out),
        "orbit_index": args.orbit_index,
        "rounds_completed": len(rounds),
        "blocked_vectors": len(forbidden),
        "trace_rejected_count": trace_reject,
        "trace_pass_count": len(trace_pass),
        "final_status": final_status,
        "status_meaning": meaning,
        "row_meta": meta,
        "elapsed_sec": out["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
