#!/usr/bin/env python3
"""analysis: Fast column dependency analysis using integer GF(2) arithmetic.

For a defect-1 deletion from rank-23, compute:
1. Single-column removal D-defect (22 checks)
2. If any column is "free" (removal keeps defect=1), do targeted B-search
"""
from __future__ import annotations
import json, time, sys
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from linear_completion import (
    build_t333_f2, tensor_to_D, parse_qmm_scheme_f2,
    verify_decomposition_f2, mask_to_vec, vec_to_mask, gf2_solve_multi
)

def fast_gf2_rank(rows_int, n_cols):
    """Fast GF(2) rank using Python integers as bit vectors.
    rows_int: list of integers, each representing a row.
    Returns rank."""
    rows = list(rows_int)
    rank = 0
    for col in range(n_cols):
        mask = 1 << col
        # Find pivot
        pivot = -1
        for i in range(rank, len(rows)):
            if rows[i] & mask:
                pivot = i; break
        if pivot < 0:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for i in range(len(rows)):
            if i != rank and rows[i] & mask:
                rows[i] ^= rows[rank]
        rank += 1
    return rank

def matrix_to_int_rows(M):
    """Convert numpy matrix (rows x cols, uint8) to list of integers."""
    rows, cols = M.shape
    result = []
    for r in range(rows):
        val = 0
        for c in range(cols):
            if M[r, c]:
                val |= (1 << c)
        result.append(val)
    return result

def build_K_int(A, B):
    """Build K matrix as list of 81 integer rows (each with r bits)."""
    r = len(A)
    rows = []
    for s in range(9):
        for beta in range(9):
            val = 0
            for t in range(r):
                if ((A[t] >> s) & 1) and ((B[t] >> beta) & 1):
                    val |= (1 << t)
            rows.append(val)
    return rows

def D_to_int_cols(D):
    """Build D as 9 column-integers, each with 81 bits."""
    cols = []
    for c in range(9):
        val = 0
        for r in range(81):
            if D[r, c]:
                val |= (1 << r)
        cols.append(val)
    return cols

def fast_D_defect(K_rows, D_rows, n_K_cols):
    """Compute D-defect using integer GF(2) rank.
    K_rows: 81 integers with n_K_cols bits (K transposed format).
    D_rows: same but for the D matrix columns appended.
    """
    # Transpose: we need column rank = rank of K^T as rows
    # K_rows are 81 rows with n_K_cols bits each
    # Augment: K_D has n_K_cols + 9 column bits
    # We compute rank(K) and rank(K|D) using row reduction on the 81 rows
    
    rank_K = fast_gf2_rank(list(K_rows), n_K_cols)
    
    # Build K|D rows
    KD_rows = []
    for i in range(81):
        val = K_rows[i]
        # Append D columns
        for c in range(9):
            s = i // 9
            beta = i % 9
            # Wait, D_rows are D-columns, I need D[i, c]
            pass
    
    return None  # Need better approach

def compute_D_defect_fast(A, B, T):
    """Compute D-defect using numpy augmented rank."""
    D = tensor_to_D(T)
    r = len(A)
    
    # Build K as 81 x r
    K = np.zeros((81, r), dtype=np.uint8)
    for t in range(r):
        for s in range(9):
            if not ((A[t] >> s) & 1): continue
            for beta in range(9):
                if (B[t] >> beta) & 1:
                    K[s*9+beta, t] = 1
    
    # rank(K)
    KT_rows = matrix_to_int_rows(K.T)
    rank_K = fast_gf2_rank(KT_rows, 81)
    
    # rank([K|D])
    KD = np.hstack([K, D])
    KDT_rows = matrix_to_int_rows(KD.T)
    rank_KD = fast_gf2_rank(KDT_rows, 81)
    
    return rank_KD - rank_K

def main():
    scheme = Path('data/cn122_3x3_r23_repro/scheme.qmm')
    outdir = Path('data/column_dep')
    outdir.mkdir(parents=True, exist_ok=True)
    
    A23, B23, C23 = parse_qmm_scheme_f2(scheme)
    T = build_t333_f2()
    D = tensor_to_D(T)
    
    results = {}
    
    for del_t in range(23):
        A22 = [A23[t] for t in range(23) if t != del_t]
        B22 = [B23[t] for t in range(23) if t != del_t]
        
        base_d = compute_D_defect_fast(A22, B22, T)
        
        if base_d != 1:
            continue
        
        # Single-column removal
        single_deps = []
        for rem_t in range(22):
            A21 = [A22[i] for i in range(22) if i != rem_t]
            B21 = [B22[i] for i in range(22) if i != rem_t]
            d = compute_D_defect_fast(A21, B21, T)
            single_deps.append(d)
        
        dep_hist = {}
        for d in single_deps:
            dep_hist[d] = dep_hist.get(d, 0) + 1
        
        free_cols = [t for t, d in enumerate(single_deps) if d == 1]
        
        print(f"del {del_t}: dep_hist={dep_hist}, free={free_cols}")
        
        results[del_t] = {
            'base_defect': base_d,
            'single_dep_defects': single_deps,
            'dep_hist': dep_hist,
            'free_columns': free_cols,
        }
        
        # If free columns exist, do targeted B-search for them
        if free_cols:
            for fc in free_cols[:2]:
                print(f"  Searching free column {fc} for del {del_t}...")
                A21 = [A22[i] for i in range(22) if i != fc]
                B21 = [B22[i] for i in range(22) if i != fc]
                hits = 0
                for delta in range(1, 512):
                    new_b = B22[fc] ^ delta
                    A_test = A21 + [A22[fc]]
                    B_test = B21 + [new_b]
                    d = compute_D_defect_fast(A_test, B_test, T)
                    if d == 0:
                        hits += 1
                        if hits <= 2:
                            # Solve for C
                            K = np.zeros((81, 22), dtype=np.uint8)
                            for t in range(22):
                                for s in range(9):
                                    if not ((A_test[t] >> s) & 1): continue
                                    for beta in range(9):
                                        if (B_test[t] >> beta) & 1:
                                            K[s*9+beta, t] = 1
                            CT = gf2_solve_multi(K, D)
                            if CT is not None:
                                C22 = [vec_to_mask(CT[t]) for t in range(22)]
                                diff = verify_decomposition_f2(A_test, B_test, C22)
                                print(f"    delta={delta}: brent_diff={diff}")
                                if diff == 0:
                                    print(f"    *** RANK-22 DECOMPOSITION FOUND! ***")
                                    dp = outdir / f'rank22_del{del_t}_fc{fc}_d{delta}.json'
                                    dp.write_text(json.dumps({
                                        'rank':22,'A':A_test,'B':B_test,'C':C22,
                                        'brent_diff':0
                                    },indent=2)+'\n')
                print(f"    Total hits for col {fc}: {hits}/511")
    
    opath = outdir / 'column_dep_all.json'
    opath.write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved: {opath}")

if __name__ == '__main__':
    main()
