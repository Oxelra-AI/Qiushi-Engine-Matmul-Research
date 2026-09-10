#!/usr/bin/env python3
r"""analysis: Global LP relaxation of the E11 core distinct Wang system.

Build the complete LP with all 417,199 core Wang constraints, 255 continuous
variables in [0,1], sum=19.  Check whether LP vertices are integral.  If any
fractional vertex is found, analyze its structure and look for Gomory/CG cuts.

The LP is: min/max c^T x  s.t.  Ax <= b, sum x = 19, 0 <= x <= 1,
where A is the point-incidence matrix (binary) and b_i = 19 - L_i (the cap).
"""
from __future__ import annotations

import json
import pickle
import sys
import time
from pathlib import Path

import numpy as np
from scipy import sparse
from scipy.optimize import linprog

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/joint_hull"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"

BASE_SUPPORT = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]


def build_sparse_matrix(records, n_cols=255):
    """Build sparse constraint matrix from core records."""
    rows_list = []
    cols_list = []
    caps = []
    for i, rec in enumerate(records):
        cap = 19 - int(rec["L"])
        if cap < 0:
            cap = 0  # trivially violated constraints: occupation > cap always
        caps.append(cap)
        bs = int(rec["point_bitset"])
        while bs:
            b = bs & -bs
            col = b.bit_length() - 1  # 0-indexed column
            rows_list.append(i)
            cols_list.append(col)
            bs ^= b
    A = sparse.csr_matrix(
        (np.ones(len(rows_list), dtype=np.float64),
         (np.array(rows_list, dtype=np.int32), np.array(cols_list, dtype=np.int32))),
        shape=(len(records), n_cols)
    )
    b = np.array(caps, dtype=np.float64)
    return A, b


def check_integrality(x, tol=1e-6):
    """Check if solution is integral."""
    rounded = np.round(x)
    max_frac = np.max(np.abs(x - rounded))
    n_fractional = np.sum(np.abs(x - rounded) > tol)
    return {
        "is_integral": bool(max_frac < tol),
        "max_fractional_part": float(max_frac),
        "n_fractional": int(n_fractional),
    }


def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)

    # Load and build
    lut, _ = load_lut(LUT_PATH)
    core = CoreQuotient(1)
    records, meta = build_core_constraints(core, lut)
    print(f"Built {len(records)} records in {time.time()-t0:.1f}s")

    # Build sparse matrix
    t1 = time.time()
    A, b = build_sparse_matrix(records)
    print(f"Sparse matrix: {A.shape}, nnz={A.nnz}, built in {time.time()-t1:.1f}s")

    # Equality constraint: sum x = 19
    A_eq = sparse.csr_matrix(np.ones((1, 255)))
    b_eq = np.array([19.0])

    # Bounds: 0 <= x <= 1
    bounds = [(0.0, 1.0)] * 255

    results = []

    # Test 1: Random objectives
    np.random.seed(42)
    for trial in range(10):
        c = np.random.randn(255)
        t2 = time.time()
        res = linprog(c, A_ub=A, b_ub=b, A_eq=A_eq, b_eq=b_eq,
                     bounds=bounds, method='highs',
                     options={'time_limit': 60})
        elapsed = time.time() - t2

        if res.success:
            integ = check_integrality(res.x)
            # Count active constraints
            slacks = b - A.dot(res.x)
            n_active = int(np.sum(np.abs(slacks) < 1e-6))

            results.append({
                "trial": trial,
                "objective": "random",
                "optimal_value": round(float(res.fun), 8),
                "is_integral": integ["is_integral"],
                "max_fractional_part": integ["max_fractional_part"],
                "n_fractional": integ["n_fractional"],
                "n_active_constraints": n_active,
                "elapsed_sec": round(elapsed, 2),
            })
            status = "INTEGRAL" if integ["is_integral"] else f"FRACTIONAL ({integ['n_fractional']} frac vars)"
            print(f"  Trial {trial}: {status}, {n_active} active, {elapsed:.1f}s")

            if not integ["is_integral"]:
                # Record fractional details
                frac_vars = [(int(i), round(float(res.x[i]), 6))
                            for i in range(255) if abs(res.x[i] - round(res.x[i])) > 1e-6]
                results[-1]["fractional_vars"] = frac_vars[:20]

                # Find near-miss violations at this fractional point
                violations_at_frac = []
                for j in range(len(records)):
                    if slacks[j] < -1e-6:
                        violations_at_frac.append({
                            "row": j,
                            "dim8": int(records[j]["dim8"]),
                            "L": int(records[j]["L"]),
                            "excess": round(float(-slacks[j]), 4),
                        })
                results[-1]["violations_at_fractional"] = violations_at_frac[:10]
        else:
            results.append({
                "trial": trial, "objective": "random",
                "status": res.message, "elapsed_sec": round(elapsed, 2),
            })
            print(f"  Trial {trial}: {res.message}, {elapsed:.1f}s")

    # Test 2: Maximize occupation of a specific dim-5 L=12 subspace
    # Use the first dim-5 violation subspace of the base near-miss
    support_bits = 0
    for p in BASE_SUPPORT:
        support_bits |= 1 << (p - 1)

    viol_subspaces = []
    for rec in records:
        L = int(rec["L"])
        cap = 19 - L
        occ = bin(int(rec["point_bitset"]) & support_bits).count('1')
        if occ > cap and int(rec["dim8"]) == 5:
            viol_subspaces.append(rec)

    print(f"\nDim-5 violation subspaces for base near-miss: {len(viol_subspaces)}")

    for vs_idx, vrec in enumerate(viol_subspaces[:3]):
        c_obj = np.zeros(255)
        bs = int(vrec["point_bitset"])
        while bs:
            b_bit = bs & -bs
            col = b_bit.bit_length() - 1
            c_obj[col] = -1.0  # maximize
            bs ^= b_bit

        t2 = time.time()
        res = linprog(c_obj, A_ub=A, b_ub=b, A_eq=A_eq, b_eq=b_eq,
                     bounds=bounds, method='highs',
                     options={'time_limit': 60})
        elapsed = time.time() - t2

        if res.success:
            integ = check_integrality(res.x)
            opt_val = -res.fun
            results.append({
                "trial": f"max_viol_subspace_{vs_idx}",
                "dim8": int(vrec["dim8"]),
                "L": int(vrec["L"]),
                "cap": 19 - int(vrec["L"]),
                "optimal_occupation": round(opt_val, 4),
                "is_integral": integ["is_integral"],
                "max_fractional_part": integ["max_fractional_part"],
                "n_fractional": integ["n_fractional"],
                "elapsed_sec": round(elapsed, 2),
            })
            status = "INTEGRAL" if integ["is_integral"] else f"FRACTIONAL ({integ['n_fractional']})"
            print(f"  Viol subspace {vs_idx}: max occupation={opt_val:.1f} (cap={19-int(vrec['L'])}), {status}, {elapsed:.1f}s")

            if not integ["is_integral"]:
                frac_vars = [(int(i), round(float(res.x[i]), 6))
                            for i in range(255) if abs(res.x[i] - round(res.x[i])) > 1e-6]
                results[-1]["fractional_vars"] = frac_vars[:20]
        else:
            results.append({
                "trial": f"max_viol_subspace_{vs_idx}",
                "status": res.message, "elapsed_sec": round(elapsed, 2),
            })

    # Summary
    n_integral = sum(1 for r in results if r.get("is_integral", False))
    n_fractional = sum(1 for r in results if r.get("is_integral") == False)
    n_failed = sum(1 for r in results if "status" in r and "status" != "Optimization terminated successfully")

    summary = {
        "total_trials": len(results),
        "integral_vertices": n_integral,
        "fractional_vertices": n_fractional,
        "failed": n_failed,
        "conclusion": "LP vertices are all integral" if n_fractional == 0 else "LP has fractional vertices - integer cuts possible",
    }
    print(f"\nSummary: {n_integral} integral, {n_fractional} fractional, {n_failed} failed")

    out = OUTDIR / "global_lp_analysis.json"
    out.write_text(json.dumps({
        "schema": "global_lp_v1",
        "elapsed_sec": round(time.time() - t0, 3),
        "matrix_shape": list(A.shape),
        "matrix_nnz": int(A.nnz),
        "results": results,
        "summary": summary,
    }, indent=2) + "\n")
    print(f"Saved: {out}")
    print(f"Total: {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
