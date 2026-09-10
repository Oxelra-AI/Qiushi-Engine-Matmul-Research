#!/usr/bin/env python3
"""analysis: Tight-contraction B-constraints for rank-22 search.

For a tight contraction λ with M_λ of rank r and exactly r active terms:
  - Left null vectors n_i of M_λ force: n_i^T b_t = 0 for active t
  - This means b_t must lie in col(M_λ), a r-dimensional subspace
  - For rank-3 contractions: b_t ∈ 3D subspace (8 choices over F₂)

Multiple tight contractions with overlapping active terms intersect their
constraints, potentially reducing each b_t to a very small set.

This script computes these constraints for rank-23 deletion A-multisets.
"""
from __future__ import annotations
import json, time, sys
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from linear_completion import (
    build_t333_f2, parse_qmm_scheme_f2, mask_to_vec, vec_to_mask, gf2_rref
)

def lambda_matrix_f2(T, lam):
    M = np.zeros((9,9), dtype=np.uint8)
    for s in range(9):
        if (lam >> s) & 1:
            M ^= T[s]
    return M

def gf2_rank(M):
    A = M.copy().astype(np.uint8)
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        found = -1
        for i in range(r, rows):
            if A[i,c]: found = i; break
        if found < 0: continue
        A[[r,found]] = A[[found,r]]
        for i in range(rows):
            if i != r and A[i,c]: A[i] ^= A[r]
        r += 1
    return r

def gf2_col_space_basis(M):
    """Return basis vectors (as 9-bit masks) for column space of M over F₂."""
    r = gf2_rank(M)
    # RREF of M^T to find pivot columns
    MT = M.T.copy().astype(np.uint8)
    rows, cols = MT.shape
    pivots = []
    rr = 0
    for c in range(cols):
        found = -1
        for i in range(rr, rows):
            if MT[i,c]: found = i; break
        if found < 0: continue
        MT[[rr,found]] = MT[[found,rr]]
        for i in range(rows):
            if i != rr and MT[i,c]: MT[i] ^= MT[rr]
        pivots.append(c)
        rr += 1
    # Pivot columns of M are the basis
    basis = []
    for p in pivots:
        basis.append(vec_to_mask(M[:,p]))
    return basis, r

def compute_b_constraints(A_multiset, T):
    """For each A-multiset element, compute the B-constraint from tight contractions.
    Returns: for each term t, the set of allowed B-masks."""
    n = len(A_multiset)
    
    # Initialize: each b_t can be any nonzero 9-bit mask
    allowed_B = [set(range(1, 512)) for _ in range(n)]
    
    tight_contractions = []
    for lam in range(1, 512):
        active = [t for t in range(n) if bin(lam & A_multiset[t]).count('1') % 2 == 1]
        M = lambda_matrix_f2(T, lam)
        r = gf2_rank(M)
        if len(active) == r and r > 0:
            # Tight contraction: b_t must be in col(M) for active t
            col_basis, col_rank = gf2_col_space_basis(M)
            
            # Generate all nonzero vectors in col(M)
            col_masks = set()
            for subset_mask in range(1, 1 << col_rank):
                v = 0
                for i in range(col_rank):
                    if (subset_mask >> i) & 1:
                        v ^= col_basis[i]
                if v: col_masks.add(v)
            
            for t in active:
                allowed_B[t] &= col_masks
            
            tight_contractions.append({
                'lambda': lam,
                'rank': r,
                'active': active,
                'col_space_size': len(col_masks),
            })
    
    return allowed_B, tight_contractions


def main():
    scheme = Path('data/cn122_3x3_r23_repro/scheme.qmm')
    outdir = Path('data/b_constraints')
    outdir.mkdir(parents=True, exist_ok=True)
    
    A23, B23, C23 = parse_qmm_scheme_f2(scheme)
    T = build_t333_f2()
    
    # Test rank-23: do original B satisfy the constraints?
    allowed_23, tight_23 = compute_b_constraints(A23, T)
    print(f"=== Rank-23 scheme: {len(tight_23)} tight contractions ===")
    b_ok_count = sum(1 for t in range(23) if B23[t] in allowed_23[t])
    print(f"Original B satisfies constraints: {b_ok_count}/23")
    print(f"Allowed B sizes: {[len(s) for s in allowed_23]}")
    print(f"Tight contraction rank histogram: {{}}")
    rank_hist = {}
    for tc in tight_23:
        rank_hist[tc['rank']] = rank_hist.get(tc['rank'], 0) + 1
    print(f"Tight contraction rank histogram: {rank_hist}")
    
    # Test defect-1 deletions
    print(f"\n=== Deletion A-multisets ===")
    for del_t in [2, 3, 4, 14, 15, 20, 21, 22]:
        A22 = [A23[t] for t in range(23) if t != del_t]
        B22 = [B23[t] for t in range(23) if t != del_t]
        
        allowed, tight = compute_b_constraints(A22, T)
        sizes = [len(s) for s in allowed]
        empty = sum(1 for s in allowed if len(s) == 0)
        b_ok = sum(1 for t in range(22) if B22[t] in allowed[t])
        total_search = 1
        for s in sizes:
            total_search *= max(s, 1)
        
        rank_hist = {}
        for tc in tight:
            rank_hist[tc['rank']] = rank_hist.get(tc['rank'], 0) + 1
        
        print(f"  del {del_t}: tight={len(tight)}, rank_hist={rank_hist}, "
              f"B_ok={b_ok}/22, empty={empty}, "
              f"min_allowed={min(sizes)}, max_allowed={max(sizes)}, "
              f"search_space={total_search:.2e}")
        
        if empty > 0:
            print(f"    *** INFEASIBLE: {empty} terms have no allowed B! ***")
    
    # Test peer candidate
    peer_A = [400,260,73,393,292,8,265,274,269,72,392,144,278,9,256,146,448,7,32,268,56,16]
    allowed_peer, tight_peer = compute_b_constraints(peer_A, T)
    sizes_peer = [len(s) for s in allowed_peer]
    empty_peer = sum(1 for s in allowed_peer if len(s) == 0)
    rank_hist_peer = {}
    for tc in tight_peer:
        rank_hist_peer[tc['rank']] = rank_hist_peer.get(tc['rank'], 0) + 1
    search_peer = 1
    for s in sizes_peer:
        search_peer *= max(s, 1)
    
    print(f"\n=== Peer candidate ===")
    print(f"  tight={len(tight_peer)}, rank_hist={rank_hist_peer}, "
          f"empty={empty_peer}, min_allowed={min(sizes_peer)}, "
          f"max_allowed={max(sizes_peer)}, search_space={search_peer:.2e}")
    
    if empty_peer > 0:
        print(f"  *** INFEASIBLE: {empty_peer} terms have no allowed B! ***")
    
    # Save
    out = {
        'rank23_tight_count': len(tight_23),
        'rank23_b_ok': b_ok_count,
        'peer_tight_count': len(tight_peer),
        'peer_empty_terms': empty_peer,
        'peer_search_space': float(search_peer),
    }
    opath = outdir / 'b_constraints.json'
    opath.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved: {opath}")

if __name__ == '__main__':
    main()
