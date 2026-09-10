#!/usr/bin/env python3
"""Verify all three slot split flattenings of T<3,3,3> over F2.

By cyclic symmetry of T_{3,3,3}, all three slot flattenings should be
27x27 permutation matrices of rank 27.  This gives:
  sum rank(a_t) >= 27,  sum rank(b_t) >= 27,  sum rank(c_t) >= 27
for any exact decomposition.  These are free prefilters on candidate schemes.
"""
import numpy as np
import json, time, sys
from pathlib import Path

def build_t333():
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T

def gf2_rank(M):
    """GF(2) row echelon rank."""
    M = M.copy().astype(np.uint8)
    rows, cols = M.shape
    rank = 0
    for c in range(cols):
        pivot = None
        for r in range(rank, rows):
            if M[r, c]:
                pivot = r; break
        if pivot is None: continue
        if pivot != rank:
            M[[rank, pivot]] = M[[pivot, rank]]
        for r in range(rows):
            if r != rank and M[r, c]:
                M[r] ^= M[rank]
        rank += 1
    return rank

def slot_flattening(T, slot):
    """Build the correct 27x27 split flattening for a matrix slot.

    The slot whose coordinate is split as a 3x3 matrix contributes its row
    index to the flattening rows and its column index to the flattening
    columns.  The two unsplit tensor slots are placed cyclically after the
    split slot.  This is the same convention as `flattening_rank_sum_bounds.py`:

        row = (first split index, next tensor slot),
        col = (second split index, remaining tensor slot).

    For a rank-one term a⊗b⊗c this matrix has rank at most the 3x3 rank of
    the chosen slot factor.  For T_{3,3,3}, each slot flattening is a 27x27
    permutation matrix.
    """
    dims = T.shape
    s1, s2 = (slot + 1) % 3, (slot + 2) % 3
    Phi = np.zeros((3 * dims[s1], 3 * dims[s2]), dtype=np.uint8)
    it = np.nditer(T, flags=["multi_index"])
    for val in it:
        if not int(val):
            continue
        idx = it.multi_index
        x = idx[slot]
        i, j = divmod(x, 3)
        # C is encoded as output coordinate (i,k).  The C-rank flattening that
        # realizes cyclic trace symmetry uses C^T, i.e. split order (k,i).
        # This is rank-equivalent for every C-factor and gives the valid
        # sum_rank_C >= 27 bound.
        if slot == 2:
            i, j = j, i
        Phi[dims[s1] * i + idx[s1], dims[s2] * j + idx[s2]] ^= 1
    return Phi

def rank_sum_check(T, A_masks, B_masks=None, C_masks=None):
    """Compute sum of GF2 matrix ranks for each slot."""
    results = {}
    if A_masks is not None:
        rs = sum(bin(int(a)).count('1') if int(a) < 8 else 
                 gf2_rank(np.array([[(int(a)>>(3*i+j))&1 for j in range(3)] for i in range(3)], dtype=np.uint8))
                 for a in A_masks)
        # Proper way: convert each 9-bit mask to 3x3 matrix and compute rank
        total = 0
        for a in A_masks:
            M = np.zeros((3,3), dtype=np.uint8)
            for i in range(3):
                for j in range(3):
                    if (int(a) >> (3*i+j)) & 1:
                        M[i,j] = 1
            total += gf2_rank(M)
        results['sum_rank_A'] = total
    return results

def main():
    T = build_t333()
    t0 = time.time()
    results = {}
    
    for slot, name in [(0, 'A'), (1, 'B'), (2, 'C')]:
        Phi = slot_flattening(T, slot)
        r = gf2_rank(Phi)
        is_perm = (Phi.sum(axis=0) == 1).all() and (Phi.sum(axis=1) == 1).all()
        nnz = int(Phi.sum())
        results[f'slot_{name}'] = {
            'rank': int(r),
            'is_permutation': bool(is_perm),
            'nnz': nnz,
            'shape': list(Phi.shape),
        }
        print(f"Slot {name}: rank={r}, is_permutation={is_perm}, nnz={nnz}")
    
    # Check on known rank-23 scheme
    print("\n=== Rank-sum checks on known rank-23 schemes ===")
    # Load flip scheme
    flip_path = Path('data/flip_cpd_inspect/src/khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt')
    if flip_path.exists():
        sys.path.insert(0, 'scripts')
        from extract_known_supports import parse_rank23_txt
        terms = parse_rank23_txt(flip_path)
        A = [a for a,b,c in terms]
        B = [b for a,b,c in terms]
        C = [c for a,b,c in terms]
        
        for masks, name in [(A, 'A'), (B, 'B'), (C, 'C')]:
            total = 0
            for m in masks:
                M = np.zeros((3,3), dtype=np.uint8)
                for i in range(3):
                    for j in range(3):
                        if (int(m) >> (3*i+j)) & 1:
                            M[i,j] = 1
                total += gf2_rank(M)
            results[f'flip_sum_rank_{name}'] = total
            print(f"  flip scheme sum_rank_{name} = {total} (bound: 27)")
    
    results['elapsed_sec'] = time.time() - t0
    out = Path('data/flattening_bounds/cslot_flattening_verification.json')
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved: {out}")

if __name__ == '__main__':
    main()
