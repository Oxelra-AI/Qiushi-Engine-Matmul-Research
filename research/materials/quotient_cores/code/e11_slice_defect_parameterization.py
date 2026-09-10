#!/usr/bin/env python3
"""Parameter counts for E11 slice completion under the defect/leak budget.

For a slice with c=3+d active terms, the own-block equation is
    V W^T = I_3
with V,W in F2^{3 x c}.  The off-block equations imply leak rowspaces
L_v <= Q^perp and L_w <= P^perp are orthogonal under the induced nondegenerate
pairing, hence dim L_v + dim L_w <= d.

This script records the resulting exact finite counts for c=3,4,5 that are useful
for extending the completion module beyond the GL3 (c=3) case.  It does not try to
enumerate global decompositions; it quantifies the local parameter space and gives
small verifications of the linear algebra.
"""
from __future__ import annotations

import json
import math
import time
from pathlib import Path
from typing import Iterable, List, Tuple

import numpy as np


def rank_int(rows: Iterable[int]) -> int:
    basis = {}
    r = 0
    for x0 in rows:
        x = int(x0)
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                r += 1
                break
    return r


def mat_rows_from_bits(bits: int, ncols: int) -> List[int]:
    return [sum(((bits >> (r*ncols+c)) & 1) << c for c in range(ncols)) for r in range(3)]


def mat_vec(row_masks: List[int], x: int, ncols: int) -> int:
    """Return compact 3-bit vector M x for 3 x ncols row-mask matrix M."""
    y = 0
    for r, mask in enumerate(row_masks):
        if ((mask & x).bit_count() & 1):
            y |= 1 << r
    return y


def nullspace(row_masks: List[int], ncols: int) -> List[int]:
    return [x for x in range(1 << ncols) if mat_vec(row_masks, x, ncols) == 0]


def count_rank3_matrices_3xc(c: int) -> int:
    cnt = 0
    for bits in range(1 << (3*c)):
        rows = mat_rows_from_bits(bits, c)
        if rank_int(rows) == 3:
            cnt += 1
    return cnt


def q_binom(n: int, r: int, q: int = 2) -> int:
    if r < 0 or r > n:
        return 0
    num = 1
    den = 1
    for i in range(r):
        num *= q**n - q**i
        den *= q**r - q**i
    return num // den


def count_m_by_d_rank(m: int, d: int, r: int, q: int = 2) -> int:
    """Number of m x d matrices over F_q of rank r."""
    if r < 0 or r > min(m, d):
        return 0
    num = 1
    den = 1
    for i in range(r):
        num *= (q**m - q**i) * (q**d - q**i)
        den *= (q**r - q**i)
    return num // den


def leak_pair_count(m: int, d: int, lv: int, lw: int, q: int = 2) -> int:
    """Count ordered pairs of m x d coefficient matrices (A,B) with
    rank(A)=lv, rank(B)=lw and rowspace(A) orthogonal to rowspace(B), assuming
    the ambient d-dimensional spaces are in perfect duality.
    """
    if lv + lw > d:
        return 0
    # Choose lv-dimensional rowspace A: [d choose lv]_q.
    # Number of m x lv coordinate matrices with full rank lv gives rowspace exactly A.
    # Then choose B as an m x d matrix of rank lw with rowspace contained in A^perp (dimension d-lv).
    choose_A = q_binom(d, lv, q)
    matrices_A_exact = count_m_by_d_rank(m, lv, lv, q)  # m x lv full column rank in coordinates of A
    matrices_B_in_Aperp_rank = count_m_by_d_rank(m, d - lv, lw, q)
    return choose_A * matrices_A_exact * matrices_B_in_Aperp_rank


def verify_own_solution_counts(c: int, sample_limit: int = 5) -> dict:
    """Enumerate rank-3 V matrices and verify W-solution count on samples."""
    rank3_count = 0
    samples = []
    target_cols = [1, 2, 4]  # e0,e1,e2 as RHS columns for rows of W
    for bits in range(1 << (3*c)):
        rows = mat_rows_from_bits(bits, c)
        if rank_int(rows) != 3:
            continue
        rank3_count += 1
        if len(samples) < sample_limit:
            solutions_per_rhs = []
            ns = nullspace(rows, c)
            for rhs in target_cols:
                sols = [x for x in range(1 << c) if mat_vec(rows, x, c) == rhs]
                solutions_per_rhs.append(len(sols))
            samples.append({
                "V_rows": rows,
                "kernel_size": len(ns),
                "solutions_per_rhs": solutions_per_rhs,
                "W_matrix_count_product": math.prod(solutions_per_rhs),
            })
    d = c - 3
    expected_rank3 = math.prod([2**c - 2**i for i in range(3)])
    expected_W = 2 ** (3*d)
    return {
        "c": c,
        "d": d,
        "rank3_V_count_enumerated": rank3_count,
        "rank3_V_count_formula": expected_rank3,
        "W_own_solutions_per_V": expected_W,
        "own_block_pair_count": rank3_count * expected_W,
        "samples": samples,
    }


def main():
    t0 = time.time()
    records = []
    for c in [3, 4, 5]:
        d = c - 3
        own = verify_own_solution_counts(c)
        leak_profile_counts = {}
        total_leak = 0
        for lv in range(d + 1):
            for lw in range(d + 1):
                if lv + lw <= d:
                    cnt = leak_pair_count(6, d, lv, lw)
                    leak_profile_counts[str((lv, lw))] = cnt
                    total_leak += cnt
        records.append({
            **own,
            "allowed_leak_profile_counts_per_own_pair": leak_profile_counts,
            "total_allowed_leak_assignments_per_own_pair": total_leak,
            "full_local_completion_count_without_term_permutation_reduction": own["own_block_pair_count"] * total_leak,
        })
    result = {
        "purpose": "local slice parameter counts for defect/leak-budget completion of E11 core slices",
        "field": "F2",
        "model": "For c=3+d active terms, choose own-block V of row rank 3, W solving V W^T=I3, then choose leak row matrices in d-dimensional dual defect spaces with orthogonal rowspaces.",
        "records": records,
        "implications": {
            "c3": "168 GL3 completions, matching analysis",
            "c4": "20,160 own-block pairs and 127 allowed leak assignments per own pair; half-purity profiles (1,0) or (0,1) plus pure (0,0).",
            "c5": "1,666,560 own-block pairs and 20,098 allowed leak assignments per own pair; dominant balanced profile is (1,1). Explicit enumeration is too large without sharing/canonicalization, but the defect-space parameterization is finite and structured.",
        },
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = Path("data/block_spread/defect_parameterization_counts.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": "ok",
        "out": str(out),
        "records_summary": [
            {
                "c": r["c"],
                "rank3_V_count": r["rank3_V_count_enumerated"],
                "W_per_V": r["W_own_solutions_per_V"],
                "own_pairs": r["own_block_pair_count"],
                "leak_per_own": r["total_allowed_leak_assignments_per_own_pair"],
                "full_local_count": r["full_local_completion_count_without_term_permutation_reduction"],
                "leak_profiles": r["allowed_leak_profile_counts_per_own_pair"],
            }
            for r in records
        ],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
