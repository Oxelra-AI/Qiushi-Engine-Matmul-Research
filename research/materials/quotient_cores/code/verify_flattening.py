#!/usr/bin/env python3
"""analysis: independently verify the A-slot split flattening bound for T_{<3,3,3>}.

The peer claims: Phi_A(T333)[(i, 3j+k), (j, 3i+k)] is a 27x27 permutation matrix.
If true, rank(Phi_A) = 27 over any field, giving sum_t rank(a_t) >= 27 for any
decomposition T = sum a_t x b_t x c_t.

At n=20: sum rank(a_t) >= 27 with 20 terms means at least 4 have rank >= 2.
Combined with rank-2/rank-3 quotient infeasibility, this gives R >= 21.
"""
import numpy as np
import json, sys
from pathlib import Path

def main():
    # T_{<3,3,3>}: the structure tensor of 3x3 matrix multiplication over F_2.
    # T = sum_{i,j,k in {0,1,2}} E_{ij} x E_{jk} x E_{ki}
    # where E_{ab} is the (a,b) standard matrix unit.
    
    # A-slot split flattening: split the first factor E_{ij} into
    # row index i and column index j.
    # Row of Phi_A: (i, 3j+k) -- i from A-row, (j,k) from B
    # Col of Phi_A: (j, 3i+k) -- j from A-col, (i,k) from C
    
    n = 3
    size = n * n * n  # 27
    
    # Build the 27x27 matrix
    Phi = np.zeros((size, size), dtype=int)
    
    terms = []
    for i in range(n):
        for j in range(n):
            for k in range(n):
                row = i * (n*n) + n*j + k  # (i, 3j+k) flattened
                col = j * (n*n) + n*i + k  # (j, 3i+k) flattened
                Phi[row, col] = 1
                terms.append({'i': i, 'j': j, 'k': k, 'row': row, 'col': col})
    
    # Check: is it a permutation matrix?
    row_sums = Phi.sum(axis=1)
    col_sums = Phi.sum(axis=0)
    is_perm = (np.all(row_sums == 1) and np.all(col_sums == 1) and Phi.sum() == size)
    
    print(f"Phi_A size: {size}x{size}")
    print(f"Row sums all 1: {np.all(row_sums == 1)}")
    print(f"Col sums all 1: {np.all(col_sums == 1)}")
    print(f"Total entries: {Phi.sum()}")
    print(f"Is permutation matrix: {is_perm}")
    
    # Verify rank over F_2 (should be 27)
    # Over F_2, a permutation matrix has full rank iff the permutation has
    # no fixed-point-free involution... actually over any field, a permutation
    # matrix has rank = size.  Let me verify by computing det mod 2.
    rank_f2 = np.linalg.matrix_rank(Phi)  # This is over R, but for a {0,1} perm matrix, rank is 27
    print(f"Rank (computed over R): {rank_f2}")
    
    # For F_2: rank of a permutation matrix is always full (the columns are
    # the standard basis vectors permuted, which are linearly independent over any field)
    print(f"Rank over F_2: {size} (permutation matrix is always full rank)")
    
    # Extract the permutation
    perm = np.argmax(Phi, axis=1)  # perm[row] = col
    print(f"\nPermutation (first 10): {perm[:10].tolist()}")
    
    # Check cycle structure
    visited = [False] * size
    cycles = []
    for start in range(size):
        if visited[start]:
            continue
        cycle = []
        p = start
        while not visited[p]:
            visited[p] = True
            cycle.append(p)
            p = perm[p]
        cycles.append(cycle)
    
    cycle_lengths = sorted([len(c) for c in cycles])
    print(f"Cycle structure: {cycle_lengths}")
    print(f"Number of cycles: {len(cycles)}")
    print(f"Number of fixed points: {sum(1 for c in cycles if len(c) == 1)}")
    
    # Now verify the consequence for decompositions
    print("\n--- Consequence for decompositions ---")
    print(f"For any decomposition T = sum_t a_t x b_t x c_t:")
    print(f"  sum_t rank(a_t) >= {size}")
    print(f"  (because Phi_A(a_t x b_t x c_t) has rank = rank(a_t))")
    
    for n_terms in [20, 21, 22, 23]:
        # With n terms: need sum rank(a_t) >= 27
        # If x terms have rank >= 2, rest have rank 1:
        # worst case all rank-2: 2x + (n-x) = n+x >= 27 => x >= 27-n
        # If some rank-3: 3y + 2x + (n-x-y) = n + x + 2y >= 27 => x+2y >= 27-n
        # minimum rank>=2 terms: ceil((27-n)/2) if 27-n > 0
        deficit = max(0, 27 - n_terms)
        min_rank2 = (deficit + 1) // 2  # ceiling division
        min_rank2_any = deficit  # if all exactly rank 2
        print(f"\n  At n={n_terms}: deficit = {deficit}")
        print(f"    Min rank>=2 terms (with possible rank-3): {min_rank2}")
        print(f"    Min rank>=2 terms (all rank-2): {min_rank2_any}")
        if min_rank2 > 0:
            print(f"    => A rank-2 or rank-3 A-factor always exists")
        else:
            print(f"    => All rank-1 is possible, no guaranteed rank>=2 factor")
    
    # B-slot flattening check (the peer claims rank 24 for quotient tensors)
    # The B-slot split: split E_{jk} into j and k
    # Phi_B[(j, 3i+k), (k, 3j+i)] or similar
    # But T_{<3,3,3>} has full symmetry under cyclic permutation of (A,B,C) with
    # appropriate index relabeling, so the B-flattening also gives a 27x27 perm matrix
    # with the same rank bound.
    
    # Actually check the B-flattening explicitly
    Phi_B = np.zeros((size, size), dtype=int)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                # B-factor is E_{jk}, split into row j and col k
                # Row: (j, ...) paired with A-factor data
                # Col: (k, ...) paired with C-factor data
                # A-factor: E_{ij} -> needs indices i,j
                # C-factor: E_{ki} -> needs indices k,i
                row_B = j * (n*n) + n*i + k  # (j, 3i+k) -- j from B-row, (i,k) from A's col,C's col
                col_B = k * (n*n) + n*j + i  # (k, 3j+i) -- k from B-col, (j,i) from C's row,A's row
                Phi_B[row_B, col_B] = 1
    
    is_perm_B = (np.all(Phi_B.sum(axis=1)==1) and np.all(Phi_B.sum(axis=0)==1))
    print(f"\nB-flattening is permutation matrix: {is_perm_B}")
    
    # Save results
    out = {
        'schema': 's0908_flattening_verification_v1',
        'A_flattening': {
            'size': int(size),
            'is_permutation_matrix': bool(is_perm),
            'rank': int(size),
            'cycle_structure': cycle_lengths,
            'num_cycles': len(cycles),
            'fixed_points': sum(1 for c in cycles if len(c) == 1),
        },
        'B_flattening': {
            'is_permutation_matrix': bool(is_perm_B),
        },
        'consequence': {
            'rank_sum_bound': int(size),
            'at_n20_min_rank2_factors': 4,
            'at_n20_min_rank2_or_rank3': True,
        },
    }
    outpath = Path("data/domain_dfs_soundness/flattening_verification.json")
    outpath.write_text(json.dumps(out, indent=2) + '\n')
    print(f"\nSaved: {outpath}")
    print(json.dumps(out, indent=2))

if __name__ == '__main__':
    main()
