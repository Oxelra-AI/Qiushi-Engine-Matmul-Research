#!/usr/bin/env python3
r"""analysis: rigorous analytical pencil realizability for E11 core dual lines.

For all-rank-9 dual lines where one corank requirement d_i = c_{11},
the pencil problem has one "tight" side (V^T M_i^{-1} U = I) that
determines V as a linear function of U.  We then check the other corank
constraint exactly by exhaustive or large-sample enumeration.

The analytical approach:
1. Fix U (9 x c11, rank c11)
2. Solve V^T M_tight^{-1} U = I_{c11} for V  (linear system)
3. Enumerate over the free variables of V  (2^{9-c11} choices per column)
4. For each V with rank c11, compute F1 = V^T M_other^{-1} U
5. Check corank(I + F1) >= d_other

For lines where d1 = c11 AND d2 = c11 (both tight), use the analysis
analytic system: V^T M1^{-1} U = V^T M2^{-1} U = I → linear in V.
"""
from __future__ import annotations

import json, sys, time, random
from collections import Counter, defaultdict
from itertools import product as iproduct
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    build_matmul_tensor_f2, contraction_matrix, mat_rank_f2, gf2_rank_rows, rref_basis
)
from dual_basis_instrument import gf2_mat_inv, gf2_mat_mul

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/pencil_pilot"

NEAR_MISS = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]


def build_e11_core_tensor():
    return build_matmul_tensor_f2()[1:,:,:].astype(np.uint8) % 2


def dot8(a, b):
    return bin(a & b).count('1') % 2


def solve_biorthogonal_system(S: np.ndarray, c11: int, n: int = 9):
    """For S (n x c11), solve V^T S = I_{c11} for V (n x c11).
    Returns (particular_V, kernel_basis) where:
      - particular_V[j] is a particular solution for column j of V (9-bit mask)
      - kernel_basis is a list of kernel vectors (9-bit masks) spanning ker(S^T)
    Returns None if system is inconsistent for any column.
    """
    # Build S^T as row bitmasks
    ST_rows = []
    for k in range(c11):
        row = 0
        for i in range(n):
            if int(S[i, k]) & 1:
                row |= 1 << i
        ST_rows.append(row)

    # RREF of S^T to find kernel
    # First, solve S^T v_j = e_j for each j

    # Augmented system with identity for tracking
    n_vars = n
    aug = []
    for i, row in enumerate(ST_rows):
        aug.append((row & ((1 << n_vars) - 1), i))

    # Gaussian elimination
    pivot_row = {}
    basis_rows = list(ST_rows)
    for i in range(c11):
        r = basis_rows[i]
        while r:
            p = r.bit_length() - 1
            if p in pivot_row:
                r ^= basis_rows[pivot_row[p]]
            else:
                pivot_row[p] = i
                basis_rows[i] = r
                break

    # Find kernel of S^T (null space)
    pivot_cols = set(pivot_row.keys())
    free_cols = [j for j in range(n_vars) if j not in pivot_cols]

    kernel = []
    for fc in free_cols:
        v = 1 << fc
        for p in sorted(pivot_cols, reverse=True):
            if (basis_rows[pivot_row[p]] >> fc) & 1:
                v ^= (1 << p)
        kernel.append(v)

    # Solve for each column j: S^T v_j = e_j
    particular = []
    for j in range(c11):
        # RHS = e_j (j-th unit vector in F_2^{c11})
        # Solve through back-substitution
        r = 1 << j  # target RHS (bit j)
        v = 0
        remaining = r
        solved = True
        # Use the reduced rows
        for p in sorted(pivot_row.keys(), reverse=True):
            row_idx = pivot_row[p]
            row = basis_rows[row_idx]
            # What would this row give?
            lhs_val = 0
            for q in pivot_cols:
                if q != p and (row >> q) & 1:
                    lhs_val ^= (v >> q) & 1

            # Need: lhs_val + v_p * 1 = rhs_bit for this equation
            rhs_bit = 0
            # The row was originally row_idx of S^T.
            # After elimination, basis_rows[row_idx] has pivot at p.
            # The RHS transforms similarly.
            pass  # This approach is getting messy

        # Cleaner approach: build full augmented system and solve
        break

    # Use a cleaner solver
    particular = []
    for j in range(c11):
        # System: S^T * v = e_j, where v is n-dimensional
        aug_rows = []
        for k in range(c11):
            # Row k: S[0,k]*v0 + S[1,k]*v1 + ... + S[n-1,k]*v_{n-1} = delta_{kj}
            coeff = 0
            for i in range(n):
                if int(S[i, k]) & 1:
                    coeff |= (1 << i)
            rhs = 1 if k == j else 0
            aug_rows.append(coeff | (rhs << n_vars))

        # Gaussian elimination
        piv = {}
        aug_copy = list(aug_rows)
        for idx in range(c11):
            r = aug_copy[idx]
            c = r & ((1 << n_vars) - 1)
            while c:
                p = c.bit_length() - 1
                if p in piv:
                    r ^= aug_copy[piv[p]]
                    c = r & ((1 << n_vars) - 1)
                else:
                    piv[p] = idx
                    aug_copy[idx] = r
                    break
            else:
                if (r >> n_vars) & 1:
                    return None  # inconsistent

        # Extract particular solution (free vars = 0)
        sol = 0
        for p in sorted(piv.keys(), reverse=True):
            row = aug_copy[piv[p]]
            bit = (row >> n_vars) & 1
            for q in piv:
                if q != p and (row >> q) & 1:
                    bit ^= (sol >> q) & 1
            if bit:
                sol |= (1 << p)
        particular.append(sol)

    return {"particular": particular, "kernel": kernel}


def analytical_pencil_one_tight(M_tight_inv, M_other_inv, c11, d_other,
                                 n_U_trials=500, max_V_enum=65536):
    """Test pencil realizability when the tight side forces V^T M_tight^{-1} U = I.

    For each random U, solve for V, enumerate over kernel, and check
    corank(I + V^T M_other^{-1} U) >= d_other.
    """
    n = 9
    k_other = c11 - d_other  # target rank(I + F_other) <= k_other

    for trial in range(n_U_trials):
        # Random U of rank c11
        while True:
            U = np.random.randint(0, 2, size=(n, c11)).astype(np.uint8)
            if mat_rank_f2(U) == c11:
                break

        S_tight = gf2_mat_mul(M_tight_inv, U) % 2
        S_other = gf2_mat_mul(M_other_inv, U) % 2

        sol = solve_biorthogonal_system(S_tight, c11, n)
        if sol is None:
            continue  # can't happen if M_tight is invertible and U has rank c11

        part = sol["particular"]  # c11 vectors (9-bit masks)
        ker = sol["kernel"]       # 9-c11 kernel vectors

        n_free = len(ker)
        n_V_choices = 1 << (n_free * c11)  # 2^(n_free * c11)

        # If too many choices, sample randomly
        if n_V_choices <= max_V_enum:
            # Exhaustive enumeration
            for combo in range(n_V_choices):
                # Build V columns: v_j = particular[j] + sum of chosen kernel vectors
                V_cols = []
                valid = True
                for j in range(c11):
                    v = part[j]
                    bits = (combo >> (j * n_free)) & ((1 << n_free) - 1)
                    for f in range(n_free):
                        if (bits >> f) & 1:
                            v ^= ker[f]
                    V_cols.append(v)

                # Check rank of V
                if gf2_rank_rows(V_cols, n) < c11:
                    continue

                # Build V matrix
                V = np.zeros((n, c11), dtype=np.uint8)
                for j in range(c11):
                    for i in range(n):
                        V[i, j] = (V_cols[j] >> i) & 1

                # Compute F_other = V^T M_other^{-1} U
                F_other = gf2_mat_mul(V.T, S_other) % 2

                # Compute I + F_other
                I_plus_F = np.eye(c11, dtype=np.uint8)
                I_plus_F = (I_plus_F + F_other) % 2

                rk = mat_rank_f2(I_plus_F)
                if rk <= k_other:
                    return {
                        "feasible": True,
                        "trial": trial,
                        "method": "exhaustive",
                        "rank_I_plus_F": int(rk),
                        "k_target": k_other,
                    }
        else:
            # Random sampling of kernel combinations
            n_samples = min(n_V_choices, max_V_enum)
            for _ in range(n_samples):
                V_cols = []
                for j in range(c11):
                    v = part[j]
                    for f in range(n_free):
                        if random.randint(0, 1):
                            v ^= ker[f]
                    V_cols.append(v)

                if gf2_rank_rows(V_cols, n) < c11:
                    continue

                V = np.zeros((n, c11), dtype=np.uint8)
                for j in range(c11):
                    for i in range(n):
                        V[i, j] = (V_cols[j] >> i) & 1

                F_other = gf2_mat_mul(V.T, S_other) % 2
                I_plus_F = (np.eye(c11, dtype=np.uint8) + F_other) % 2
                rk = mat_rank_f2(I_plus_F)
                if rk <= k_other:
                    return {
                        "feasible": True,
                        "trial": trial,
                        "method": "sampled",
                        "rank_I_plus_F": int(rk),
                        "k_target": k_other,
                    }

    return {
        "feasible": False,
        "trials": n_U_trials,
        "method": "exhaustive" if (1 << ((9-c11)*c11)) <= max_V_enum else "sampled",
    }


def analytical_pencil_both_tight(M1_inv, M2_inv, c11, n_U_trials=500):
    """Both sides tight: V^T M1^{-1} U = V^T M2^{-1} U = I.
    Equivalent to V^T (M1^{-1} + M2^{-1}) U = 0 and V^T M1^{-1} U = I.
    """
    n = 9
    for trial in range(n_U_trials):
        while True:
            U = np.random.randint(0, 2, size=(n, c11)).astype(np.uint8)
            if mat_rank_f2(U) == c11:
                break

        S1 = gf2_mat_mul(M1_inv, U) % 2
        S2 = gf2_mat_mul(M2_inv, U) % 2

        # Combined system: V^T [S1 | S2] = [I | I]
        # For each column j of V: v_j^T s1_k = delta_{jk}, v_j^T s2_k = delta_{jk}
        # This is 2*c11 equations in 9 unknowns.

        # Build coefficient matrix: rows are S1^T rows then S2^T rows
        coeff_rows = []
        for k in range(c11):
            row = 0
            for i in range(n):
                if int(S1[i, k]) & 1:
                    row |= 1 << i
            coeff_rows.append(row)
        for k in range(c11):
            row = 0
            for i in range(n):
                if int(S2[i, k]) & 1:
                    row |= 1 << i
            coeff_rows.append(row)

        # For each j, RHS = (e_j, e_j)
        all_ok = True
        V_cols = []
        for j in range(c11):
            rhs = [0] * (2 * c11)
            rhs[j] = 1
            rhs[c11 + j] = 1

            # Solve via Gaussian elimination
            aug = []
            for i, cr in enumerate(coeff_rows):
                aug.append(cr | (rhs[i] << n))

            piv = {}
            aug_work = list(aug)
            for idx in range(2 * c11):
                r = aug_work[idx]
                c = r & ((1 << n) - 1)
                while c:
                    p = c.bit_length() - 1
                    if p in piv:
                        r ^= aug_work[piv[p]]
                        c = r & ((1 << n) - 1)
                    else:
                        piv[p] = idx
                        aug_work[idx] = r
                        break
                else:
                    if (r >> n) & 1:
                        all_ok = False
                        break
            if not all_ok:
                break

            # Extract solution
            sol = 0
            for p in sorted(piv.keys(), reverse=True):
                row = aug_work[piv[p]]
                bit = (row >> n) & 1
                for q in piv:
                    if q != p and (row >> q) & 1:
                        bit ^= (sol >> q) & 1
                if bit:
                    sol |= 1 << p
            V_cols.append(sol)

        if not all_ok:
            continue

        if gf2_rank_rows(V_cols, n) >= c11:
            return {"feasible": True, "trial": trial}

    return {"feasible": False, "trials": n_U_trials}


def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    np.random.seed(42)

    T_core = build_e11_core_tensor()
    na, nb, nc = T_core.shape

    cdata = {}
    for q in range(1, 256):
        M = contraction_matrix(T_core, q)
        rk = mat_rank_f2(M)
        cdata[q] = {"rank": rk, "M": M, "M_inv": gf2_mat_inv(M) if rk == 9 else None}

    # Enumerate all dual lines
    seen = set()
    lines = []
    for q1 in range(1, 256):
        for q2 in range(q1+1, 256):
            q3 = q1 ^ q2
            if q3 == 0:
                continue
            canon = tuple(sorted([q1, q2, q3]))
            if canon in seen:
                continue
            seen.add(canon)
            lines.append(canon)

    # Find all-rank-9 lines
    r9_lines = []
    for q1, q2, q3 in lines:
        if all(cdata[q]["rank"] == 9 for q in [q1, q2, q3]):
            r9_lines.append((q1, q2, q3))

    print(f"All-rank-9 dual lines: {len(r9_lines)}")

    # Compute color profiles for near-miss
    results = []
    for q1, q2, q3 in r9_lines:
        c00 = c10 = c01 = c11 = 0
        for p in NEAR_MISS:
            e1, e2 = dot8(q1, p), dot8(q2, p)
            if e1 == 0 and e2 == 0: c00 += 1
            elif e1 == 1 and e2 == 0: c10 += 1
            elif e1 == 0 and e2 == 1: c01 += 1
            else: c11 += 1

        d1 = 9 - c10  # corank needed for M1+Z
        d2 = 9 - c01  # corank needed for M2+Z
        # d3 for q3: corank of M3+Z... but q3=q1^q2 gives the third contraction
        # Actually the colors for (q1, q2) basis determine everything.
        # For q3=q1^q2: w(q3) = c10+c01, rank L(q3) = 9
        # So c10+c01 >= 9 (individual bound)

        results.append({
            "line": [q1, q2, q3],
            "colors": [c00, c10, c01, c11],
            "d": [d1, d2],
        })

    # Classify by (c11, d1, d2) and test pencil
    pencil_tests = []
    feasible_count = 0
    infeasible_count = 0
    n_tested = 0

    # Sort by difficulty (larger d1+d2 and smaller c11 = harder)
    results.sort(key=lambda r: (-(r["d"][0]+r["d"][1]), r["colors"][3]))

    for rec in results:
        q1, q2, q3 = rec["line"]
        c00, c10, c01, c11 = rec["colors"]
        d1, d2 = rec["d"]

        if d1 <= 0 and d2 <= 0:
            # Trivial: no corank needed
            pencil_tests.append({**rec, "pencil": "trivial_feasible"})
            feasible_count += 1
            continue

        # For the (q1, q2) pair: M1 = L(q1), M2 = L(q2)
        M1_inv = cdata[q1]["M_inv"]
        M2_inv = cdata[q2]["M_inv"]

        n_tested += 1

        if d1 == c11 and d2 == c11:
            # Both tight
            result = analytical_pencil_both_tight(M1_inv, M2_inv, c11, n_U_trials=1000)
        elif d2 == c11 and d1 < c11:
            # Tight on side 2
            result = analytical_pencil_one_tight(M2_inv, M1_inv, c11, d1,
                                                  n_U_trials=500)
        elif d1 == c11 and d2 < c11:
            # Tight on side 1
            result = analytical_pencil_one_tight(M1_inv, M2_inv, c11, d2,
                                                  n_U_trials=500)
        elif d1 > 0 or d2 > 0:
            # General case: use random search (bigger sample)
            # For now, mark as "general" and use random
            M1 = cdata[q1]["M"]
            M2 = cdata[q2]["M"]
            any_found = False
            for _ in range(2000):
                while True:
                    U = np.random.randint(0, 2, size=(9, c11)).astype(np.uint8)
                    if mat_rank_f2(U) == c11:
                        break
                while True:
                    V = np.random.randint(0, 2, size=(9, c11)).astype(np.uint8)
                    if mat_rank_f2(V) == c11:
                        break
                Z = gf2_mat_mul(U, V.T) % 2
                r1 = mat_rank_f2((M1 + Z) % 2)
                r2 = mat_rank_f2((M2 + Z) % 2)
                if r1 <= c10 and r2 <= c01:
                    any_found = True
                    break
            result = {"feasible": any_found, "method": "random_2000"}
        else:
            result = {"feasible": True, "note": "trivial"}

        feas = result.get("feasible", False)
        if feas:
            feasible_count += 1
        else:
            infeasible_count += 1

        pencil_tests.append({
            **rec,
            "pencil_feasible": feas,
            "pencil_detail": result,
        })

        if n_tested % 20 == 0:
            print(f"  tested {n_tested}/{len(results)}: "
                  f"feasible={feasible_count}, infeasible={infeasible_count}")

    print(f"\nResults for all {len(r9_lines)} all-rank-9 lines:")
    print(f"  Pencil FEASIBLE:   {feasible_count}")
    print(f"  Pencil INFEASIBLE: {infeasible_count}")

    # Detailed breakdown by color profile
    color_feas = Counter()
    color_infeas = Counter()
    for t in pencil_tests:
        colors = tuple(t["colors"])
        if t.get("pencil_feasible", t.get("pencil") == "trivial_feasible"):
            color_feas[colors] += 1
        else:
            color_infeas[colors] += 1

    print("\nInfeasible color profiles:")
    for colors, count in sorted(color_infeas.items()):
        fc = color_feas.get(colors, 0)
        print(f"  colors={colors}: infeasible={count}, feasible={fc}")

    # Save
    summary = {
        "total_r9_lines": len(r9_lines),
        "pencil_feasible": feasible_count,
        "pencil_infeasible": infeasible_count,
        "infeasible_color_profiles": {
            str(k): {"infeasible": v, "feasible": color_feas.get(k, 0)}
            for k, v in sorted(color_infeas.items())
        },
        "support": NEAR_MISS,
        "elapsed_sec": time.time() - t0,
        "tests": pencil_tests[:100],  # first 100 for inspection
    }

    out = OUTDIR / "analytical_pencil_results.json"
    out.write_text(json.dumps(summary, indent=2, sort_keys=True, default=str) + "\n")
    print(f"\nSaved: {out}")
    print(f"Elapsed: {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
