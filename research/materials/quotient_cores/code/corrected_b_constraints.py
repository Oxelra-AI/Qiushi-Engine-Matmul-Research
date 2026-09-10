#!/usr/bin/env python3
"""analysis: CORRECTED tight-contraction B-constraints.

Bug fix: col_space_vectors was computing row space, not column space.
The column space of M is found by row-reducing M and selecting its pivot columns.
"""
from __future__ import annotations
import json, time, sys
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from linear_completion import (
    build_t333_f2, parse_qmm_scheme_f2, mask_to_vec, vec_to_mask,
    verify_decomposition_f2, tensor_to_D, gf2_solve_multi
)

def gf2_rank(M):
    A = M.copy().astype(np.uint8)
    r, c = A.shape; rank = 0
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

def col_space_vectors_corrected(M):
    """All nonzero vectors in the COLUMN space of M over F₂.
    Row-reduce M to find pivot columns, then generate all nonzero combinations."""
    A = M.copy().astype(np.uint8)
    rows, cols = A.shape
    pivots = []
    r = 0
    for c in range(cols):
        found = -1
        for i in range(r, rows):
            if A[i,c]: found = i; break
        if found < 0: continue
        A[[r,found]] = A[[found,r]]
        for i in range(rows):
            if i != r and A[i,c]: A[i] ^= A[r]
        pivots.append(c)
        r += 1
    
    # Pivot columns of M span col(M)
    basis_cols = [M[:, p].copy() for p in pivots]
    rank = len(basis_cols)
    
    vecs = set()
    for mask in range(1, 1 << rank):
        v = np.zeros(rows, dtype=np.uint8)
        for i in range(rank):
            if (mask >> i) & 1:
                v ^= basis_cols[i]
        v_mask = vec_to_mask(v)
        if v_mask: vecs.add(v_mask)
    return vecs, rank

def lambda_matrix_f2(T, lam):
    M = np.zeros((9,9), dtype=np.uint8)
    for s in range(9):
        if (lam >> s) & 1:
            M ^= T[s]
    return M

def compute_b_constraints_corrected(A_multiset, T):
    n = len(A_multiset)
    allowed_B = [set(range(1, 512)) for _ in range(n)]
    tight_info = []
    
    for lam in range(1, 512):
        active = [t for t in range(n) if bin(lam & A_multiset[t]).count('1') % 2 == 1]
        M = lambda_matrix_f2(T, lam)
        r = gf2_rank(M)
        if len(active) == r and r > 0 and r < 9:
            col_vecs, col_rank = col_space_vectors_corrected(M)
            for t in active:
                allowed_B[t] &= col_vecs
            tight_info.append({'lambda': lam, 'rank': r, 'active': active,
                              'col_space_size': len(col_vecs)})
    
    return allowed_B, tight_info


def build_K_np(A, B):
    r = len(A)
    K = np.zeros((81, r), dtype=np.uint8)
    for t in range(r):
        for s in range(9):
            if not ((A[t]>>s)&1): continue
            for b in range(9):
                if (B[t]>>b)&1:
                    K[s*9+b, t] = 1
    return K

def D_defect_np(K, D):
    def fr(M):
        A = M.copy(); r,c = A.shape; rank=0
        for col in range(c):
            f=-1
            for i in range(rank,r):
                if A[i,col]: f=i; break
            if f<0: continue
            A[[rank,f]]=A[[f,rank]]
            for i in range(r):
                if i!=rank and A[i,col]: A[i]^=A[rank]
            rank+=1
        return rank
    rK = fr(K.T.copy())
    KD = np.hstack([K,D])
    rKD = fr(KD.T.copy())
    return rKD - rK


def main():
    scheme = Path('data/cn122_3x3_r23_repro/scheme.qmm')
    outdir = Path('data/b_constraints')
    outdir.mkdir(parents=True, exist_ok=True)
    
    A23, B23, C23 = parse_qmm_scheme_f2(scheme)
    T = build_t333_f2()
    D = tensor_to_D(T)
    
    # Verify rank-23 first
    allowed_23, tight_23 = compute_b_constraints_corrected(A23, T)
    b_ok = sum(1 for t in range(23) if B23[t] in allowed_23[t])
    sizes_23 = [len(s) for s in allowed_23]
    empty_23 = sum(1 for s in sizes_23 if s == 0)
    print(f"=== Rank-23 (CORRECTED) ===")
    print(f"Tight contractions (rank<9): {len(tight_23)}")
    print(f"B satisfies constraints: {b_ok}/23")
    print(f"Empty terms: {empty_23}")
    print(f"Allowed sizes: {sizes_23}")
    
    if b_ok < 23:
        # Debug failures
        for t in range(23):
            if B23[t] not in allowed_23[t]:
                # Find which constraint fails
                for tc in tight_23:
                    if t in tc['active']:
                        M = lambda_matrix_f2(T, tc['lambda'])
                        col_vecs, _ = col_space_vectors_corrected(M)
                        if B23[t] not in col_vecs:
                            print(f"  Term {t}: B={B23[t]} not in col(M_λ={tc['lambda']}), "
                                  f"rank={tc['rank']}, |col|={len(col_vecs)}")
                            break
    
    # Deletion A-multisets
    print(f"\n=== Deletion A-multisets (CORRECTED) ===")
    for del_t in [2, 3, 4, 14, 15, 20, 21, 22]:
        A22 = [A23[t] for t in range(23) if t != del_t]
        B22 = [B23[t] for t in range(23) if t != del_t]
        
        allowed, tight = compute_b_constraints_corrected(A22, T)
        sizes = [len(s) for s in allowed]
        empty = sum(1 for s in sizes if s == 0)
        b_ok = sum(1 for t in range(22) if B22[t] in allowed[t])
        
        search = 1
        for s in sizes:
            search *= max(s, 1)
        
        print(f"  del {del_t}: tight={len(tight)}, B_ok={b_ok}/22, "
              f"empty={empty}, sizes={sorted(set(sizes))}, search={search:.2e}")
        
        if empty > 0:
            print(f"    INFEASIBLE: {empty} terms have no allowed B")
        elif search < 1e12:
            print(f"    FEASIBLE search space: {search:.2e}")
            # Try enumeration if small enough
            if search < 1e8:
                print(f"    Attempting constrained B enumeration...")
                # TODO: implement
    
    # Peer candidate
    peer_A = [400,260,73,393,292,8,265,274,269,72,392,144,278,9,256,146,448,7,32,268,56,16]
    allowed_p, tight_p = compute_b_constraints_corrected(peer_A, T)
    sizes_p = [len(s) for s in allowed_p]
    empty_p = sum(1 for s in sizes_p if s == 0)
    search_p = 1
    for s in sizes_p: search_p *= max(s,1)
    
    print(f"\n=== Peer candidate (CORRECTED) ===")
    print(f"Tight (rank<9): {len(tight_p)}, empty={empty_p}, "
          f"sizes={sorted(set(sizes_p))}, search={search_p:.2e}")
    if empty_p > 0:
        print(f"  INFEASIBLE: {empty_p} terms have no allowed B")
    
    # Save
    out = {
        'schema': 'b_constraints_corrected_v1',
        'rank23_b_ok': b_ok,
        'rank23_empty': empty_23,
        'deletion_results': {},
    }
    for del_t in [2, 3, 4, 14, 15, 20, 21, 22]:
        A22 = [A23[t] for t in range(23) if t != del_t]
        allowed, _ = compute_b_constraints_corrected(A22, T)
        sizes = [len(s) for s in allowed]
        out['deletion_results'][str(del_t)] = {
            'empty': sum(1 for s in sizes if s == 0),
            'sizes': sizes,
        }
    
    opath = outdir / 'b_constraints_corrected.json'
    opath.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved: {opath}")

if __name__ == '__main__':
    main()
