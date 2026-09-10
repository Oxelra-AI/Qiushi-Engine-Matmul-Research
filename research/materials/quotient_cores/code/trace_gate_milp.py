#!/usr/bin/env python3
r"""
analysis MILP completion for the trace-saturation gate.

This script loads the complete Wang occupation cache produced by
trace_saturation_gate.py and asks exact integer support questions with
all 417,199 Wang inequalities at once, using scipy/HiGHS MILP:

  * max sum_s nu(a_s) under Wang + contraction-rank lower bounds;
  * feasibility of avoiding all saturated invertible contractions, i.e.
    |I_q| >= 10 for every rank-9 contraction q;
  * min sum_s nu(a_s) under Wang alone as a calibration.

The objective is support-level route control.  Feasible supports are not tensor
CPDs; infeasibility would be a support-level theorem only after preserving the
full linear model and solver status.
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

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import csr_matrix, vstack

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/trace_saturation_gate"
SCRIPTS_A02 = ROOT / "workspace/scripts"
SCRIPTS_A01 = Path("scripts")
for P in (SCRIPTS_A02, SCRIPTS_A01):
    if str(P) not in sys.path:
        sys.path.insert(0, str(P))

from trace_saturation_gate import (  # noqa: E402
    CORES,
    bit_dot,
    build_or_load_core_cache,
    contraction_ranks,
    core_raw_summary,
    load_lut,
    mask_to_points,
    point_caps_from_cache,
    support_stats,
)


def wang_sparse(cache: dict, n: int = 255) -> tuple[csr_matrix, np.ndarray]:
    indptr = [0]
    indices = []
    data = []
    b = []
    for m, cap in zip(cache["masks"], cache["caps"]):
        pts = mask_to_points(int(m))
        indices.extend([p - 1 for p in pts])
        data.extend([1.0] * len(pts))
        indptr.append(len(indices))
        b.append(float(cap))
    A = csr_matrix((np.array(data, dtype=np.float64), np.array(indices, dtype=np.int32), np.array(indptr, dtype=np.int64)), shape=(len(b), n))
    return A, np.array(b, dtype=np.float64)


def hit_sparse(rows: Sequence[tuple[int, int]], n: int = 255) -> tuple[csr_matrix, np.ndarray]:
    # rows are (q, lower_bound); produce -hit <= -lb.
    indptr = [0]
    indices = []
    data = []
    b = []
    for q, lb in rows:
        pts = [p for p in range(1, n + 1) if bit_dot(p, int(q))]
        indices.extend([p - 1 for p in pts])
        data.extend([-1.0] * len(pts))
        indptr.append(len(indices))
        b.append(-float(lb))
    A = csr_matrix((np.array(data, dtype=np.float64), np.array(indices, dtype=np.int32), np.array(indptr, dtype=np.int64)), shape=(len(b), n))
    return A, np.array(b, dtype=np.float64)


def solve_milp(name: str, cache: dict, c_ranks: dict[int, int], inv_qs: Sequence[int], nu: dict[int, int], mode: str, time_limit: float) -> dict:
    n = 255
    pcaps = point_caps_from_cache(cache, int(cache["rank_s"]))
    lbounds = np.zeros(n, dtype=np.float64)
    ubounds = np.array([float(pcaps[p]) for p in range(1, n + 1)], dtype=np.float64)
    integrality = np.ones(n, dtype=np.int8)
    c = np.zeros(n, dtype=np.float64)
    if mode == "max_sum_nu":
        c = -np.array([float(nu[p]) for p in range(1, n + 1)], dtype=np.float64)
    elif mode == "min_sum_nu_wang_only":
        c = np.array([float(nu[p]) for p in range(1, n + 1)], dtype=np.float64)

    Aw, bw = wang_sparse(cache, n)
    lower_rows = []
    if mode in ("max_sum_nu", "no_saturation"):
        for q, rk in sorted(c_ranks.items()):
            if int(rk) <= 0:
                continue
            lb = 10 if (mode == "no_saturation" and q in inv_qs) else int(rk)
            lower_rows.append((int(q), int(lb)))
    Ah, bh = hit_sparse(lower_rows, n) if lower_rows else (csr_matrix((0, n), dtype=np.float64), np.zeros(0))
    Atotal = vstack([Aw, Ah], format="csr") if lower_rows else Aw
    btotal = np.concatenate([bw, bh]) if lower_rows else bw
    ineq = LinearConstraint(Atotal, -np.inf * np.ones_like(btotal), btotal)
    Aeq = csr_matrix(np.ones((1, n), dtype=np.float64))
    eq = LinearConstraint(Aeq, np.array([float(cache["rank_s"])]), np.array([float(cache["rank_s"])]))
    t0 = time.time()
    res = milp(
        c=c,
        integrality=integrality,
        bounds=Bounds(lbounds, ubounds),
        constraints=[ineq, eq],
        options={"time_limit": float(time_limit), "mip_rel_gap": 0.0, "disp": False},
    )
    elapsed = time.time() - t0
    status_map = {0: "OPTIMAL", 1: "TIME_LIMIT_OR_ITERATION_LIMIT", 2: "INFEASIBLE", 3: "UNBOUNDED", 4: "OTHER"}
    out = {
        "mode": mode,
        "core_name": name,
        "status_code": int(res.status),
        "status": status_map.get(int(res.status), str(res.status)),
        "success": bool(res.success),
        "message": str(res.message),
        "fun": None if res.fun is None else float(res.fun),
        "elapsed_sec": round(elapsed, 3),
        "nvars": n,
        "wang_constraint_count": int(Aw.shape[0]),
        "direct_hit_constraint_count": int(Ah.shape[0]),
        "nnz": int(Atotal.nnz),
        "time_limit_sec": float(time_limit),
    }
    if res.x is not None:
        xr = np.rint(res.x).astype(int)
        sol = {p: int(xr[p - 1]) for p in range(1, n + 1) if int(xr[p - 1]) != 0}
        st = support_stats(sol, c_ranks, inv_qs, nu)
        # Verify all Wang inequalities exactly on the rounded integer solution.
        viol = 0
        max_exc = 0
        for m, cap in zip(cache["masks"], cache["caps"]):
            occ = sum(sol.get(p, 0) for p in mask_to_points(int(m)))
            if occ > int(cap):
                viol += 1
                max_exc = max(max_exc, occ - int(cap))
        out["rounded_solution_integral_max_abs_error"] = float(np.max(np.abs(res.x - xr)))
        out["support_stats"] = st
        out["exact_wang_violation_count"] = int(viol)
        out["exact_wang_max_excess"] = int(max_exc)
        if mode == "max_sum_nu":
            out["objective_sum_nu"] = int(st["sum_nu"])
            out["proved_upper_bound_sum_nu_if_optimal"] = int(st["sum_nu"]) if int(res.status) == 0 else None
        elif mode == "min_sum_nu_wang_only":
            out["objective_sum_nu"] = int(st["sum_nu"])
        elif mode == "no_saturation":
            out["no_saturation_verified"] = bool(st["rank9_saturated_count"] == 0 and min(int(k) for k in st["rank9_hit_histogram"].keys()) >= 10)
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--cache-dir", type=Path, default=OUTDIR / "cache")
    ap.add_argument("--cores", nargs="*", default=["E11"], choices=list(CORES))
    ap.add_argument("--modes", nargs="*", default=["max_sum_nu", "no_saturation", "min_sum_nu_wang_only"], choices=["max_sum_nu", "no_saturation", "min_sum_nu_wang_only"])
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--time-limit", type=float, default=120.0)
    ap.add_argument("--out", type=Path, default=OUTDIR / "trace_gate_milp.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    lut, meta = load_lut(args.lut)
    result = {
        "schema": "trace_gate_milp_v1",
        "rank_s": int(args.rank),
        "field": "F2",
        "purpose": "Complete support-level MILP gate for saturation of invertible contractions under all Wang occupation inequalities.",
        "lut_meta_brief": {"coverage_ok": meta.get("coverage_ok"), "conflict_count": meta.get("conflict_count"), "subspace_count": len(lut)},
        "parameters": {"cores": args.cores, "modes": args.modes, "time_limit": args.time_limit},
        "cores": {},
    }
    t_all = time.time()
    for name in args.cores:
        cfg = CORES[name]
        print(f"=== {name} ===", flush=True)
        raw, _T, c_ranks, inv_qs, nu = core_raw_summary(name, cfg["pivot_mask"])
        cache = build_or_load_core_cache(name, cfg["pivot_mask"], args.rank, lut, args.cache_dir, rebuild=False)
        rec = {"raw_gate": raw, "milp": {}}
        for mode in args.modes:
            print(f"  solve {mode} ...", flush=True)
            out = solve_milp(name, cache, c_ranks, inv_qs, nu, mode, args.time_limit)
            rec["milp"][mode] = out
            print(json.dumps({"mode": mode, "status": out["status"], "fun": out["fun"], "sum_nu": out.get("objective_sum_nu"), "sat": (out.get("support_stats") or {}).get("rank9_saturated_count"), "elapsed": out["elapsed_sec"]}, sort_keys=True), flush=True)
        result["cores"][name] = rec
    result["elapsed_sec"] = round(time.time() - t_all, 3)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(args.out), "elapsed_sec": result["elapsed_sec"]}, indent=2))


if __name__ == "__main__":
    main()
