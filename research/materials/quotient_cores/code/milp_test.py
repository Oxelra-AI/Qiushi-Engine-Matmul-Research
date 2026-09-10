#!/usr/bin/env python3
r"""analysis: MILP feasibility test for E11 core distinct Wang system.

Test whether there exists a 0/1 vector x in {0,1}^255 with sum(x)=19
satisfying all 417,199 E11 core Wang occupation constraints.

If feasible: a complete-Wang-admissible distinct 19-point support EXISTS.
If infeasible: R_F2(core_E11) >= 20, and by the bridge, R_F2(T) >= 21.
"""
from __future__ import annotations

import json
import pickle
import sys
import time
from pathlib import Path

import numpy as np
from scipy import sparse
from scipy.optimize import milp, LinearConstraint, Bounds

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/joint_hull"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"


def build_sparse_matrix(records, n_cols=255):
    """Build sparse constraint matrix from core records."""
    rows_list = []
    cols_list = []
    caps = []
    for i, rec in enumerate(records):
        cap = 19 - int(rec["L"])
        caps.append(cap)
        bs = int(rec["point_bitset"])
        while bs:
            b = bs & -bs
            col = b.bit_length() - 1
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

    # Filter to only binding/near-binding constraints (cap <= 10)
    # This dramatically reduces the problem size while keeping all relevant constraints
    binding_mask = b <= 10  # L >= 9, cap <= 10
    A_filtered = A[binding_mask]
    b_filtered = b[binding_mask]
    print(f"Filtered to cap<=10: {A_filtered.shape[0]} constraints (from {A.shape[0]})")

    # MILP setup
    # Objective: maximize nothing (feasibility test) - use zero objective
    c_obj = np.zeros(255)

    # Binary integrality
    integrality = np.ones(255, dtype=int)  # 1 = integer

    # Constraints:
    # 1. Ax <= b (Wang occupation)
    # 2. sum(x) = 19
    constraints = [
        LinearConstraint(A_filtered, ub=b_filtered),
        LinearConstraint(np.ones((1, 255)), lb=19.0, ub=19.0),
    ]

    # Bounds: x in {0,1}
    bounds_obj = Bounds(lb=0, ub=1)

    # Solve with time limit
    time_limit = 300  # 5 minutes
    print(f"\nSolving MILP (binary feasibility), time limit={time_limit}s...")
    t2 = time.time()

    # Try with full constraints first
    try:
        result = milp(
            c=c_obj,
            constraints=constraints,
            integrality=integrality,
            bounds=bounds_obj,
            options={"time_limit": time_limit, "presolve": True},
        )
        milp_elapsed = time.time() - t2

        if result.success:
            x = result.x
            support = sorted([i+1 for i in range(255) if abs(x[i] - 1.0) < 0.5])
            n_selected = len(support)

            # Verify against full constraint set
            full_occ = A.dot(np.round(x))
            full_violations = int(np.sum(full_occ > b + 0.5))

            print(f"MILP: FEASIBLE in {milp_elapsed:.1f}s")
            print(f"  Support size: {n_selected}")
            print(f"  Support: {support}")
            print(f"  Full Wang violations: {full_violations}")

            milp_result = {
                "status": "feasible",
                "support": support,
                "support_size": n_selected,
                "full_wang_violations": full_violations,
                "elapsed_sec": round(milp_elapsed, 2),
                "solver_message": str(result.message),
            }
        else:
            print(f"MILP: {result.message} in {milp_elapsed:.1f}s")
            milp_result = {
                "status": str(result.message),
                "elapsed_sec": round(milp_elapsed, 2),
            }
            if "infeasible" in str(result.message).lower():
                milp_result["interpretation"] = "No 0/1 support exists: R_F2(core_E11) >= 20"

    except Exception as e:
        milp_elapsed = time.time() - t2
        print(f"MILP error: {e} in {milp_elapsed:.1f}s")
        milp_result = {"status": "error", "error": str(e), "elapsed_sec": round(milp_elapsed, 2)}

    # Also try a lazy MILP: start with tight constraints, add violated ones
    print("\n--- Lazy MILP approach ---")
    # Start with cap <= 4 rows only
    tight_mask = b <= 4  # L >= 15
    A_tight = A[tight_mask]
    b_tight = b[tight_mask]
    print(f"Tight constraints (cap<=4): {A_tight.shape[0]}")

    lazy_results = []
    current_A = A_tight
    current_b = b_tight

    for iteration in range(5):
        constraints_lazy = [
            LinearConstraint(current_A, ub=current_b),
            LinearConstraint(np.ones((1, 255)), lb=19.0, ub=19.0),
        ]

        t3 = time.time()
        try:
            res_lazy = milp(
                c=c_obj,
                constraints=constraints_lazy,
                integrality=integrality,
                bounds=bounds_obj,
                options={"time_limit": 120, "presolve": True},
            )
            lazy_elapsed = time.time() - t3

            if res_lazy.success:
                x_lazy = np.round(res_lazy.x)
                # Check full constraints
                full_occ = A.dot(x_lazy)
                violated_rows = np.where(full_occ > b + 0.5)[0]
                n_violated = len(violated_rows)

                support_lazy = sorted([i+1 for i in range(255) if x_lazy[i] > 0.5])
                print(f"  Iter {iteration}: FEASIBLE, support={support_lazy[:10]}..., full violations={n_violated}, {lazy_elapsed:.1f}s")

                lazy_results.append({
                    "iteration": iteration,
                    "n_constraints": int(current_A.shape[0]),
                    "status": "feasible",
                    "support": support_lazy,
                    "full_violations": n_violated,
                    "elapsed_sec": round(lazy_elapsed, 2),
                })

                if n_violated == 0:
                    print(f"  *** WANG-ADMISSIBLE SUPPORT FOUND: {support_lazy} ***")
                    break

                # Add violated rows
                A_new = A[violated_rows]
                b_new = b[violated_rows]
                current_A = sparse.vstack([current_A, A_new])
                current_b = np.concatenate([current_b, b_new])
                print(f"  Added {n_violated} violated constraints, total now {current_A.shape[0]}")
            else:
                print(f"  Iter {iteration}: {res_lazy.message}, {lazy_elapsed:.1f}s")
                lazy_results.append({
                    "iteration": iteration,
                    "n_constraints": int(current_A.shape[0]),
                    "status": str(res_lazy.message),
                    "elapsed_sec": round(lazy_elapsed, 2),
                })
                if "infeasible" in str(res_lazy.message).lower():
                    break
        except Exception as e:
            lazy_elapsed = time.time() - t3
            print(f"  Iter {iteration}: error {e}, {lazy_elapsed:.1f}s")
            lazy_results.append({"iteration": iteration, "status": "error", "error": str(e)})
            break

    # Save all results
    out = OUTDIR / "milp_feasibility_test.json"
    out.write_text(json.dumps({
        "schema": "milp_feasibility_v1",
        "elapsed_sec": round(time.time() - t0, 3),
        "full_milp_result": milp_result,
        "lazy_milp_results": lazy_results,
        "constraint_counts": {
            "total": int(A.shape[0]),
            "cap_le_10": int(np.sum(b <= 10)),
            "cap_le_4": int(np.sum(b <= 4)),
        },
    }, indent=2) + "\n")
    print(f"\nSaved: {out}")
    print(f"Total: {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
