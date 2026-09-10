#!/usr/bin/env python3
"""Debug: check if rank-23 B-factors satisfy tight-contraction column-space constraints."""
import numpy as np
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from linear_completion import (
    build_t333_f2, parse_qmm_scheme_f2, mask_to_vec, vec_to_mask
)

def gf2_rank(M):
    A = M.copy().astype(np.uint8)
    r, c = A.shape
    rank = 0
    for col in range(c):
        found = -1
        for i in range(rank, r):
            if A[i,col]: found = i; break
        if found < 0: continue
        A[[rank,found]] = A[[found,rank]]
        for i in range(r):
            if i != rank and A[i,col]: A[i] ^= A[rank]
        rank += 1
    return rank

def col_space_vectors(M):
    """All nonzero vectors in col(M) over F₂."""
    r = gf2_rank(M)
    # Find r linearly independent columns
    MT = M.T.copy().astype(np.uint8)
    rows_mt, cols_mt = MT.shape
    pivots = []
    rr = 0
    for c in range(cols_mt):
        found = -1
        for i in range(rr, rows_mt):
            if MT[i,c]: found = i; break
        if found < 0: continue
        MT[[rr,found]] = MT[[found,rr]]
        for i in range(rows_mt):
            if i != rr and MT[i,c]: MT[i] ^= MT[rr]
        pivots.append(c)
        rr += 1
    # Basis columns of M
    basis_cols = [M[:, p].copy() for p in pivots]
    # Generate all nonzero combinations
    vecs = set()
    for mask in range(1, 1 << r):
        v = np.zeros(M.shape[0], dtype=np.uint8)
        for i in range(r):
            if (mask >> i) & 1:
                v ^= basis_cols[i]
        if np.any(v):
            vecs.add(vec_to_mask(v))
    return vecs

T = build_t333_f2()
A23, B23, C23 = parse_qmm_scheme_f2(
    'data/cn122_3x3_r23_repro/scheme.qmm')

# Find all tight contractions for rank-23
failures = []
for lam in range(1, 512):
    active = [t for t in range(23) if bin(lam & A23[t]).count('1') % 2 == 1]
    M = np.zeros((9,9), dtype=np.uint8)
    for s in range(9):
        if (lam >> s) & 1:
            M ^= T[s]
    r = gf2_rank(M)
    
    if len(active) == r and r > 0 and r < 9:
        # This is a tight contraction with rank < 9
        col_vecs = col_space_vectors(M)
        
        # Check each active B
        for t in active:
            b_mask = B23[t]
            if b_mask not in col_vecs:
                failures.append({
                    'lambda': lam, 'rank': r, 'term': t,
                    'B_mask': b_mask, 'col_space_size': len(col_vecs),
                    'active': active
                })

print(f"Tight contraction failures for rank-23 B-factors: {len(failures)}")
for f in failures[:20]:
    lam = f['lambda']
    M = np.zeros((9,9), dtype=np.uint8)
    for s in range(9):
        if (lam >> s) & 1:
            M ^= T[s]
    r = gf2_rank(M)
    
    # Check: does the actual decomposition give M_λ?
    actual_M = np.zeros((9,9), dtype=np.uint8)
    for t in f['active']:
        a = mask_to_vec(A23[t])
        b = mask_to_vec(B23[t])
        c = mask_to_vec(C23[t])
        # Contribution to M_λ: Σ_{s:λ[s]=1} a[s] * b c^T
        coeff = 0
        for s in range(9):
            if (lam >> s) & 1:
                coeff ^= ((A23[t] >> s) & 1)
        if coeff:
            actual_M ^= np.outer(b, c).astype(np.uint8) % 2
    
    match = np.array_equal(actual_M % 2, M % 2)
    actual_rank = gf2_rank(actual_M)
    print(f"  λ={lam}, rank={r}, term={f['term']}, B={f['B_mask']}, "
          f"col_space={f['col_space_size']}, actual_M_match={match}, "
          f"actual_rank={actual_rank}")
    if not match:
        print(f"    *** M_λ MISMATCH: actual has rank {actual_rank} ***")
