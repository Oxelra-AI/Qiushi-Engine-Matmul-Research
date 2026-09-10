#!/usr/bin/env python3
"""
Full coupled dual-basis analysis with corrected convention.
Greedy minimal inconsistent subset + coupling structure.
"""

import numpy as np
import json
import itertools
from pathlib import Path

def gf2_rref(A):
    A = A.copy() % 2
    m, n = A.shape
    pivots = []
    row = 0
    for col in range(n):
        found = -1
        for r in range(row, m):
            if A[r, col]:
                found = r
                break
        if found < 0:
            continue
        A[[row, found]] = A[[found, row]]
        for r in range(m):
            if r != row and A[r, col]:
                A[r] ^= A[row]
        pivots.append(col)
        row += 1
    return A, row, pivots

def gf2_consistent(A, b):
    A = np.array(A, dtype=np.uint8) % 2
    b = np.array(b, dtype=np.uint8).reshape(-1, 1) % 2
    Ab = np.hstack([A, b])
    _, rank_Ab, _ = gf2_rref(Ab)
    _, rank_A, _ = gf2_rref(A)
    return rank_A == rank_Ab, rank_A, rank_Ab


def mat_rank_gf2(M):
    return gf2_rref(np.array(M, dtype=np.uint8))[1]

def mat_inv_gf2(M):
    n = M.shape[0]
    A = np.hstack([M.copy() % 2, np.eye(n, dtype=np.uint8)])
    rref, r, _ = gf2_rref(A)
    assert r == n
    return rref[:, n:] % 2

def lambda_to_mat(lam_int):
    positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    M = np.zeros((3,3), dtype=np.uint8)
    for bit_idx, (i,j) in enumerate(positions):
        if lam_int & (1 << bit_idx):
            M[i,j] = 1
    return M

def contraction_matrix(lam_int):
    Lambda = lambda_to_mat(lam_int)
    return np.kron(Lambda.T, np.eye(3, dtype=np.uint8)) % 2

def build_e11_core():
    T = np.zeros((8, 9, 9), dtype=np.uint8)
    a_positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    for idx, (ai, aj) in enumerate(a_positions):
        bi, bj = aj, ai
        for k in range(3):
            T[idx, 3*bi + k, 3*bj + k] = 1
    return T

def build_system(support, T_core, trace_lams=None):
    """Build tensor identity + optional trace equations."""
    s = len(support)
    nv = s * 81
    
    # Tensor identity: for each slice i, each (r,c): sum_{t: bit i of a_t} X_t[r,c] = T[i,r,c]
    rows_A, rows_b = [], []
    for si in range(8):
        for r in range(9):
            for c in range(9):
                row = np.zeros(nv, dtype=np.uint8)
                for t, a in enumerate(support):
                    if a & (1 << si):
                        row[t * 81 + r * 9 + c] = 1
                rows_A.append(row)
                rows_b.append(T_core[si, r, c])
    
    if trace_lams:
        for lam in trace_lams:
            Lambda = lambda_to_mat(lam)
            lr = int(mat_rank_gf2(Lambda))
            if lr != 3:
                continue
            M = contraction_matrix(lam)
            M_inv = mat_inv_gf2(M)
            
            active = [t for t, a in enumerate(support)
                     if bin(a & lam).count('1') % 2 == 1]
            if len(active) != 9:
                continue
            
            for t in active:
                row = np.zeros(nv, dtype=np.uint8)
                for r in range(9):
                    for ss in range(9):
                        if M_inv[r, ss]:
                            row[t * 81 + ss * 9 + r] ^= 1
                rows_A.append(row)
                rows_b.append(1)
    
    return np.array(rows_A, dtype=np.uint8), np.array(rows_b, dtype=np.uint8)

def main():
    T_core = build_e11_core()
    L15 = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]
    
    # Find all tight rank-9 contractions
    tight_r9 = []
    for lam in range(1, 256):
        Lambda = lambda_to_mat(lam)
        lr = int(mat_rank_gf2(Lambda))
        if lr != 3:
            continue
        active = [t for t, a in enumerate(L15) if bin(a & lam).count('1') % 2 == 1]
        if len(active) == 9:
            tight_r9.append(lam)
    
    print(f"L15 support: {L15}")
    print(f"Tight rank-9 contractions: {len(tight_r9)}")
    print(f"  λ values: {tight_r9}")
    
    # 1. Verify tensor-only consistent
    A, b = build_system(L15, T_core, trace_lams=None)
    cons, rank_A, rank_Ab = gf2_consistent(A, b)
    print(f"\nTensor-only: consistent={cons}, rank={rank_A}")
    
    # 2. Full trace: should be inconsistent
    A, b = build_system(L15, T_core, trace_lams=tight_r9)
    cons, rank_A, rank_Ab = gf2_consistent(A, b)
    print(f"Full trace ({len(tight_r9)} contractions): consistent={cons}, "
          f"rank={rank_A}, augmented={rank_Ab}")
    
    # 3. Per-contraction check
    print(f"\nPer-contraction check:")
    for lam in tight_r9:
        A, b = build_system(L15, T_core, trace_lams=[lam])
        cons, rA, rAb = gf2_consistent(A, b)
        if not cons:
            print(f"  λ={lam}: INCONSISTENT alone!")
    print(f"  All 16 individually consistent ✓" if all(
        gf2_consistent(*build_system(L15, T_core, trace_lams=[l]))[0] 
        for l in tight_r9) else "  Some individually inconsistent!")
    
    # 4. Greedy minimal inconsistent subset
    print(f"\nGreedy minimal inconsistent subset search:")
    current = list(tight_r9)
    while True:
        removed = False
        for i in range(len(current)):
            candidate = current[:i] + current[i+1:]
            A, b = build_system(L15, T_core, trace_lams=candidate)
            cons, _, _ = gf2_consistent(A, b)
            if not cons:
                print(f"  Removed λ={current[i]} (remaining {len(candidate)})")
                current = candidate
                removed = True
                break
        if not removed:
            break
    
    print(f"  Greedy minimum size: {len(current)}")
    print(f"  Contractions: {current}")
    
    # 5. Try exact search for smaller subsets (from greedy size - 1 down to 2)
    min_size = len(current)
    min_subset = current
    
    # Try exact search at size greedy-1
    if min_size > 2:
        target_size = min_size - 1
        print(f"\n  Exact search at size {target_size}...")
        found = False
        count = 0
        for subset in itertools.combinations(tight_r9, target_size):
            count += 1
            A, b = build_system(L15, T_core, trace_lams=list(subset))
            cons, _, _ = gf2_consistent(A, b)
            if not cons:
                print(f"  Found inconsistent subset of size {target_size}: {list(subset)}")
                min_size = target_size
                min_subset = list(subset)
                found = True
                break
            if count % 1000 == 0:
                print(f"    checked {count}...")
        if not found:
            print(f"  No inconsistent subset of size {target_size} found ({count} checked)")
    
    # 6. Coupling analysis
    print(f"\n=== Coupling structure ===")
    term_in_contractions = {t: [] for t in range(19)}
    for lam in tight_r9:
        active = [t for t, a in enumerate(L15) if bin(a & lam).count('1') % 2 == 1]
        for t in active:
            term_in_contractions[t].append(lam)
    
    for t in range(19):
        print(f"  term {t} (a={L15[t]:3d}): in {len(term_in_contractions[t])} contractions")
    
    # Pairwise overlap
    print(f"\n=== Pairwise overlaps among tight rank-9 ===")
    overlaps = {}
    for i, l1 in enumerate(tight_r9):
        a1 = set(t for t, a in enumerate(L15) if bin(a & l1).count('1') % 2 == 1)
        for j, l2 in enumerate(tight_r9):
            if i >= j:
                continue
            a2 = set(t for t, a in enumerate(L15) if bin(a & l2).count('1') % 2 == 1)
            ov = len(a1 & a2)
            overlaps[(l1,l2)] = ov
    
    ov_hist = {}
    for v in overlaps.values():
        ov_hist[v] = ov_hist.get(v, 0) + 1
    print(f"  Overlap histogram: {dict(sorted(ov_hist.items()))}")
    
    # Save results
    outdir = Path("data/coupled_dual_basis")
    outdir.mkdir(parents=True, exist_ok=True)
    
    result = {
        'support': L15,
        'tight_r9': tight_r9,
        'full_trace_consistent': bool(cons),
        'full_trace_rank': int(rank_A),
        'full_trace_augmented': int(rank_Ab),
        'greedy_min_size': min_size,
        'greedy_min_subset': min_subset,
        'coupling': {str(t): len(cs) for t, cs in term_in_contractions.items()},
        'overlap_hist': {str(k): v for k, v in sorted(ov_hist.items())},
    }
    
    with open(outdir / "l15_corrected_trace_analysis.json", 'w') as f:
        json.dump(result, f, indent=2)
    print(f"\nSaved to {outdir / 'l15_corrected_trace_analysis.json'}")

main()
