#!/usr/bin/env python3
"""Search for the true minimum inconsistent subset of tight rank-9 contractions
for the L15 support, using precomputed trace rows for efficiency."""

import numpy as np
import itertools
from pathlib import Path
import json

def gf2_rref(A):
    A = A.copy() % 2
    m, n = A.shape
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
        row += 1
    return row

def gf2_consistent_fast(A, b):
    """Check consistency using augmented matrix rank comparison."""
    Ab = np.hstack([A, b.reshape(-1,1)])
    rank_Ab = gf2_rref(Ab)
    rank_A = gf2_rref(A.copy())
    return rank_A == rank_Ab

def lambda_to_mat(lam_int):
    positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    M = np.zeros((3,3), dtype=np.uint8)
    for bit_idx, (i,j) in enumerate(positions):
        if lam_int & (1 << bit_idx):
            M[i,j] = 1
    return M

def mat_inv_gf2(M):
    n = M.shape[0]
    A = np.hstack([M.copy() % 2, np.eye(n, dtype=np.uint8)])
    m = A.shape[0]
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
        row += 1
    return A[:, n:] % 2

def main():
    L15 = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]
    tight_r9 = [42, 43, 49, 57, 70, 71, 87, 94, 133, 151, 157, 179, 186, 214, 234, 241]
    s = len(L15)
    nv = s * 81
    
    # Build core tensor
    T = np.zeros((8, 9, 9), dtype=np.uint8)
    a_positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    for idx, (ai, aj) in enumerate(a_positions):
        bi, bj = aj, ai
        for k in range(3):
            T[idx, 3*bi + k, 3*bj + k] = 1
    
    # Build tensor identity system (fixed)
    A_tensor = np.zeros((648, nv), dtype=np.uint8)
    b_tensor = np.zeros(648, dtype=np.uint8)
    eq = 0
    for si in range(8):
        for r in range(9):
            for c in range(9):
                for t, a in enumerate(L15):
                    if a & (1 << si):
                        A_tensor[eq, t * 81 + r * 9 + c] = 1
                b_tensor[eq] = T[si, r, c]
                eq += 1
    
    # Build trace rows per contraction (bank)
    trace_rows = {}  # lam -> (A_rows, b_rows)
    for lam in tight_r9:
        Lambda = lambda_to_mat(lam)
        M = np.kron(Lambda.T, np.eye(3, dtype=np.uint8)) % 2
        M_inv = mat_inv_gf2(M)
        
        active = [t for t, a in enumerate(L15) if bin(a & lam).count('1') % 2 == 1]
        
        rows = []
        rhs = []
        for t in active:
            row = np.zeros(nv, dtype=np.uint8)
            for r in range(9):
                for ss in range(9):
                    if M_inv[r, ss]:
                        row[t * 81 + ss * 9 + r] ^= 1
            rows.append(row)
            rhs.append(1)
        
        trace_rows[lam] = (np.array(rows, dtype=np.uint8), np.array(rhs, dtype=np.uint8))
    
    def check_subset(subset):
        """Check if tensor + trace from subset is inconsistent."""
        parts_A = [A_tensor]
        parts_b = [b_tensor]
        for lam in subset:
            ar, br = trace_rows[lam]
            parts_A.append(ar)
            parts_b.append(br)
        A = np.vstack(parts_A)
        b = np.concatenate(parts_b)
        return not gf2_consistent_fast(A, b)
    
    # Search from small to large
    print(f"Searching for minimum inconsistent subset among {len(tight_r9)} contractions...")
    
    for size in range(2, len(tight_r9) + 1):
        n_comb = 1
        for i in range(size):
            n_comb = n_comb * (len(tight_r9) - i) // (i + 1)
        print(f"\n  Size {size}: {n_comb} subsets to check")
        
        found = None
        count = 0
        for subset in itertools.combinations(tight_r9, size):
            count += 1
            if check_subset(subset):
                found = list(subset)
                print(f"  *** FOUND at size {size}: {found} (checked {count}/{n_comb})")
                break
            if count % 5000 == 0:
                print(f"    ...checked {count}/{n_comb}")
        
        if found:
            # Search all at this size to count how many
            total_inconsistent = 1
            for subset in itertools.combinations(tight_r9, size):
                if list(subset) == found:
                    continue
                total_inconsistent += 1 if check_subset(subset) else 0
                # Don't count all; just report first
            print(f"  Minimum inconsistent size: {size}")
            print(f"  Example: {found}")
            
            # Save
            outdir = Path("data/coupled_dual_basis")
            outdir.mkdir(parents=True, exist_ok=True)
            result = {
                'support': L15,
                'tight_r9': tight_r9,
                'min_inconsistent_size': size,
                'min_inconsistent_example': found,
                'subsets_checked_at_min': count,
            }
            with open(outdir / "min_inconsistent_search.json", 'w') as f:
                json.dump(result, f, indent=2)
            print(f"  Saved to {outdir / 'min_inconsistent_search.json'}")
            break
        else:
            print(f"  No inconsistent subset of size {size} (checked {count})")

main()
