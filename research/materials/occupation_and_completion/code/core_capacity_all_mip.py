#!/usr/bin/env python3
"""Solve the complete core-level Wang occupation capacity system by MIP.

For a pivot p and core rank s, variables x_q count projective A-factors in the
8-dimensional quotient.  This script enumerates every subspace Psi <= F2^8 and
adds the exact Wang-derived inequality

    sum_{q in Psi\0} x_q <= s - L_T(span(p, lift(Psi))).

This is a complete finite necessary condition for a rank-s decomposition of the
core.  Infeasibility at s=19 proves the corresponding core has F2 rank at least
20.  Feasibility produces an admissible A-factor multiset but does not by itself
produce B/C factors.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from core_capacity_from_wang_lut import CoreQuotient, PIVOTS, occupancy_key8  # noqa: E402
from wang_capacity_lazy import unpack_basis, subspace_points_from_basis, pack_basis, rref_basis  # noqa: E402
from wang_capacity_orbit_closed import extension_keys  # noqa: E402


def load_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return payload["lut"], payload.get("meta", {})


def enumerate_subspace_keys(n: int = 8) -> List[int]:
    levels = {0: {pack_basis(tuple())}}
    all_keys = set(levels[0])
    for d in range(n):
        nxt = set()
        for key in levels[d]:
            for ekey in extension_keys(unpack_basis(key), n=n):
                if (ekey & 0xF) == d + 1:
                    nxt.add(ekey)
        levels[d + 1] = nxt
        all_keys.update(nxt)
        print(f"  enumerated dim {d+1}: {len(nxt):,}")
    return sorted(all_keys)


def build_core_matrix(core: CoreQuotient, lut: Dict[int, int], s: int, include_dims: Tuple[int, int]) -> Tuple[LinearConstraint, List[int], dict]:
    t0 = time.time()
    keys8 = enumerate_subspace_keys(8)
    lo_dim, hi_dim = include_dims
    keys8 = [k for k in keys8 if lo_dim <= (k & 0xF) <= hi_dim]
    print(f"Using {len(keys8):,} core subspace constraints with dims {include_dims}")

    rows = []
    cols = []
    data = []
    lb = np.full(len(keys8) + 1, -np.inf, dtype=float)
    ub = np.empty(len(keys8) + 1, dtype=float)

    # total equality row
    rows.extend([0] * 255)
    cols.extend(range(255))
    data.extend([1.0] * 255)
    lb[0] = s
    ub[0] = s

    by_dim = Counter()
    by_L = Counter()
    min_cap = 999
    max_cap = -999
    for ri, key8 in enumerate(keys8, start=1):
        key9 = core.key9_from_key8(key8)
        L = lut[key9]
        cap = s - L
        pts = subspace_points_from_basis(unpack_basis(key8))
        rows.extend([ri] * len(pts))
        cols.extend([p - 1 for p in pts])
        data.extend([1.0] * len(pts))
        ub[ri] = cap
        by_dim[key8 & 0xF] += 1
        by_L[L] += 1
        min_cap = min(min_cap, cap)
        max_cap = max(max_cap, cap)
    A = coo_matrix((np.array(data, dtype=float), (np.array(rows, dtype=np.int32), np.array(cols, dtype=np.int32))), shape=(len(keys8) + 1, 255)).tocsr()
    meta = {
        "constraint_rows_including_total": int(A.shape[0]),
        "subspace_constraints": len(keys8),
        "variables": 255,
        "nonzeros": int(A.nnz),
        "cuts_by_dim8": dict(by_dim),
        "cuts_by_original_L": dict(by_L),
        "min_capacity": min_cap,
        "max_capacity": max_cap,
        "build_elapsed_sec": time.time() - t0,
    }
    return LinearConstraint(A, lb, ub), keys8, meta


def verify_solution(sol: Dict[int, int], core: CoreQuotient, lut: Dict[int, int], s: int, keys8: Iterable[int], max_report=50):
    t0 = time.time()
    violations = []
    for key8 in keys8:
        key9 = core.key9_from_key8(key8)
        L = lut[key9]
        cap = s - L
        occ = occupancy_key8(key8, sol)
        if occ > cap:
            violations.append({"key8": key8, "basis8": list(unpack_basis(key8)), "key9": key9, "basis9": list(unpack_basis(key9)), "dim8": key8 & 0xF, "L": L, "cap": cap, "occupancy": occ, "excess": occ - cap})
            if len(violations) >= max_report:
                break
    return {"violation_count_reported": len(violations), "violations_head": violations, "elapsed_sec": time.time() - t0}


def solve_core(name: str, pivot: int, lut: Dict[int, int], s: int, outdir: Path, include_dims=(0, 8), time_limit=600.0):
    core = CoreQuotient(pivot)
    cons, keys8, meta = build_core_matrix(core, lut, s, include_dims)
    bounds = Bounds(np.zeros(255), np.full(255, s))
    integrality = np.ones(255)
    c = np.zeros(255)
    options = {"time_limit": time_limit, "mip_rel_gap": 0.0, "disp": True}
    t0 = time.time()
    res = milp(c, integrality=integrality, bounds=bounds, constraints=cons, options=options)
    elapsed = time.time() - t0
    sol = None
    verify = None
    if getattr(res, "x", None) is not None:
        rounded = [int(round(v)) for v in res.x]
        sol = {i + 1: v for i, v in enumerate(rounded) if v}
        verify = verify_solution(sol, core, lut, s, keys8)
    result = {
        "problem": "complete core Wang occupation capacity MIP",
        "field": "F2",
        "core_name": name,
        "pivot_mask": pivot,
        "rank_s": s,
        "include_dims": list(include_dims),
        "meaning": "Infeasible at s=19 proves this core rank is at least 20 over F2. Feasible gives only an admissible A-factor multiset for subsequent B/C solving.",
        "matrix_meta": meta,
        "status": int(res.status),
        "success": bool(res.success),
        "message": str(res.message),
        "fun": None if res.fun is None else float(res.fun),
        "solve_elapsed_sec": elapsed,
        "solution_support_size": None if sol is None else len(sol),
        "solution_total_multiplicity": None if sol is None else sum(sol.values()),
        "solution_max_multiplicity": None if sol is None else max(sol.values()),
        "solution": None if sol is None else {str(k): v for k, v in sorted(sol.items())},
        "verification": verify,
    }
    outdir.mkdir(parents=True, exist_ok=True)
    outpath = outdir / f"complete_core_capacity_{name}_s{s}.json"
    outpath.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in ["core_name", "rank_s", "success", "status", "message", "solve_elapsed_sec", "solution_support_size", "solution_total_multiplicity", "solution_max_multiplicity", "verification"]}, indent=2, sort_keys=True))
    print(f"Saved {outpath}")
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--outdir", type=Path, default=Path("data/core_capacity_complete_mip"))
    ap.add_argument("--core", choices=list(PIVOTS) + ["all"], default="E11")
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--min-dim", type=int, default=0)
    ap.add_argument("--max-dim", type=int, default=8)
    ap.add_argument("--time-limit", type=float, default=600.0)
    args = ap.parse_args()
    lut, meta = load_lut(args.lut)
    print(f"Loaded T-level LUT {len(lut):,}; coverage_ok={meta.get('coverage_ok')} conflicts={meta.get('conflict_count')}")
    todo = list(PIVOTS.items()) if args.core == "all" else [(args.core, PIVOTS[args.core])]
    for name, pivot in todo:
        solve_core(name, pivot, lut, args.rank, args.outdir, (args.min_dim, args.max_dim), args.time_limit)


if __name__ == "__main__":
    main()
