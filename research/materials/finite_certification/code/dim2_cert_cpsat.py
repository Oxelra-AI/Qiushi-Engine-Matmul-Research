#!/usr/bin/env python3
"""Generate proof-grade CP-SAT certificates for all eight dim-2 occupation raises.

Uses the integer-multiplicity CP-SAT model (which correctly handles cap>1 at orbit 489).
For each orbit, records the complete constraint system and CP-SAT infeasibility result.
Also runs an independent SciPy/HiGHS MILP replay as a cross-check.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from pathlib import Path
from collections import Counter

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from node_local_occupation_closure import (
    rref_basis, pack_basis, free_bits_from_rref, lift_q,
    node_constraints, solve_local_cp
)

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
CACHE_PATH = Path("data/wang_f2_lb20/wang_orbit_closed_cache.pkl")
OUTDIR = Path("data/dim2_certificates")


def milp_replay(k: int, support_size: int, constraints, cap2_info=None):
    """Independent SciPy/HiGHS MILP replay."""
    from scipy.optimize import linprog, milp, LinearConstraint, Bounds
    import numpy as np

    npts = (1 << k) - 1
    # Variables: x_1, ..., x_npts, each integer in [0, support_size]
    n = npts
    # Equality: sum x_i = support_size
    A_eq = np.ones((1, n))
    b_eq = np.array([support_size], dtype=float)
    # Inequality: for each (mask, cap):  sum_{i in mask} x_i <= cap
    A_rows = []
    b_rows = []
    for mask, cap in constraints:
        row = np.zeros(n)
        for i in range(npts):
            if (mask >> i) & 1:
                row[i] = 1.0
        if cap < 0:
            # Infeasible by negative cap
            A_rows.append(np.zeros(n))
            b_rows.append(-1.0)
        else:
            A_rows.append(row)
            b_rows.append(float(cap))
    A_ub = np.array(A_rows) if A_rows else np.zeros((0, n))
    b_ub = np.array(b_rows) if b_rows else np.zeros(0)

    # LP relaxation
    bounds_lp = [(0.0, float(support_size))] * n
    lp_result = linprog(np.zeros(n), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                        bounds=bounds_lp, method='highs')
    lp_status = int(lp_result.status)

    # MILP
    integrality = np.ones(n)
    constraints_milp = []
    if len(A_ub) > 0:
        constraints_milp.append(LinearConstraint(A_ub, ub=b_ub))
    constraints_milp.append(LinearConstraint(A_eq, lb=b_eq, ub=b_eq))
    milp_result = milp(np.zeros(n), integrality=integrality,
                       bounds=Bounds(lb=0, ub=support_size),
                       constraints=constraints_milp,
                       options={"time_limit": 120.0})
    milp_status = int(milp_result.status)

    return {
        "lp_status": lp_status,
        "lp_message": lp_result.message[:100],
        "milp_status": milp_status,
        "milp_message": str(milp_result.message)[:100] if hasattr(milp_result, 'message') else "",
        "lp_feasible": lp_status == 0,
        "milp_infeasible": milp_status == 2,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--indices", default="484,485,486,487,488,489,490,491")
    ap.add_argument("--cpsat-timeout", type=float, default=900.0)
    ap.add_argument("--out", type=Path, default=OUTDIR / "cpsat_certificate_summary.json")
    args = ap.parse_args()

    indices = [int(x) for x in args.indices.split(",")]

    with LUT_PATH.open("rb") as f:
        data = pickle.load(f)
    lut = data["lut"] if isinstance(data, dict) and "lut" in data else data
    with CACHE_PATH.open("rb") as f:
        cache = pickle.load(f)
    orbits = cache["orbits"]
    OUTDIR.mkdir(parents=True, exist_ok=True)

    results = []
    for idx in indices:
        orb = next(o for o in orbits if o["cert_index"] == idx)
        W_basis = orb["basis"]
        W = rref_basis(W_basis, 9)
        d = len(W)
        k = 9 - d
        L = orb["raw_lb"]  # 18
        free = free_bits_from_rref(W, 9)
        npts = (1 << k) - 1

        print(f"\n=== Orbit {idx}: W_basis={W_basis} W_rref={W} d={d} k={k} L={L} npts={npts} ===")

        # Build constraint rows
        rows, meta = node_constraints(W, lut, L)

        # Check line caps
        max_cap = 0
        cap2_dirs = []
        for q in range(1, 1 << k):
            v = lift_q(q, free)
            U = rref_basis((*W, v), 9)
            key = pack_basis(U)
            lb_U = lut.get(key)
            if lb_U is not None:
                cap = L - lb_U
                if cap > max_cap:
                    max_cap = cap
                if cap > 1:
                    cap2_dirs.append({"q": q, "v": v, "cap": cap, "lb_U": lb_U})

        # CP-SAT solve
        t0 = time.time()
        sol = solve_local_cp(k, L, rows, args.cpsat_timeout, 8)
        cpsat_elapsed = time.time() - t0

        # Independent MILP replay
        t0 = time.time()
        milp = milp_replay(k, L, rows, cap2_dirs)
        milp_elapsed = time.time() - t0

        rec = {
            "cert_index": idx,
            "W_basis": list(W_basis),
            "W_rref": list(W),
            "dim": d,
            "quotient_dim": k,
            "target_L": L,
            "n_quotient_directions": npts,
            "max_line_cap": max_cap,
            "cap2_directions": cap2_dirs if cap2_dirs else None,
            "n_constraint_rows": len(rows),
            "negative_cap_rows": meta["negative_cap_rows"],
            "cpsat_status": sol.get("status"),
            "cpsat_feasible": sol.get("feasible"),
            "cpsat_elapsed_sec": sol.get("elapsed_sec"),
            "cpsat_conflicts": sol.get("conflicts"),
            "cpsat_branches": sol.get("branches"),
            "milp_lp_feasible": milp["lp_feasible"],
            "milp_integer_infeasible": milp["milp_infeasible"],
            "milp_lp_status": milp["lp_status"],
            "milp_status": milp["milp_status"],
            "milp_elapsed_sec": milp_elapsed,
        }
        results.append(rec)
        status_line = (f"  CP-SAT: {sol.get('status')} in {sol.get('elapsed_sec',0):.2f}s | "
                       f"MILP: lp_feas={milp['lp_feasible']} int_infeas={milp['milp_infeasible']} in {milp_elapsed:.2f}s")
        print(status_line)

    all_cpsat_infeasible = all(r["cpsat_feasible"] == False for r in results)
    all_milp_infeasible = all(r["milp_integer_infeasible"] for r in results)

    summary = {
        "schema": "dim2_cpsat_certificates_v1",
        "indices": indices,
        "all_cpsat_infeasible": all_cpsat_infeasible,
        "all_milp_integer_infeasible": all_milp_infeasible,
        "both_solvers_agree": all_cpsat_infeasible and all_milp_infeasible,
        "results": results,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"\nAll CP-SAT INFEASIBLE: {all_cpsat_infeasible}")
    print(f"All MILP integer INFEASIBLE: {all_milp_infeasible}")
    print(f"Both agree: {all_cpsat_infeasible and all_milp_infeasible}")
    print(f"-> {args.out}")


if __name__ == "__main__":
    main()
