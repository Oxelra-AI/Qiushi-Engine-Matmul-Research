#!/usr/bin/env python3
"""
Compressed 3×3 shadow system for E11 core trace analysis.

review insight: define π(X)_{ij} = tr(X_{ij}) (block traces of 9×9 matrix).
Then the corrected trace condition tr(M_λ^{-1} X_t) = tr(Y_t Λ^{-1}) = 1
where Y_t = π(X_t) ∈ Mat_3(F_2).

The shadow system is EQUIVALENT to the full 81-variable-per-term system
for consistency (proven by lifting argument: error ∈ A ⊗ ker(π) can be
corrected since the A-vectors span F_2^8 and trace conditions depend only on π).

Variables: 19 × 9 = 171 (entries of Y_t, 3×3 matrices)
Tensor identity: 8 × 9 = 72 equations (shadow slices)
Trace: 9 per tight rank-9 contraction

This is ~9x smaller than the full system, enabling exhaustive subset search.
"""

import numpy as np
import json
import itertools
from pathlib import Path

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
    return row  # rank

def gf2_consistent(A, b):
    Ab = np.hstack([A, b.reshape(-1,1)])
    rank_Ab = gf2_rref(Ab)
    rank_A = gf2_rref(A.copy())
    return rank_A == rank_Ab, rank_A, rank_Ab


def mat_rank_gf2(M):
    """Rank over GF(2), not over R. Two 3x3 binary masks differ between these fields."""
    return gf2_rref(np.array(M, dtype=np.uint8))

def lambda_to_mat(lam_int):
    positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    M = np.zeros((3,3), dtype=np.uint8)
    for bit_idx, (i,j) in enumerate(positions):
        if lam_int & (1 << bit_idx):
            M[i,j] = 1
    return M

def mat_inv_gf2_3x3(M):
    """Invert 3×3 matrix over GF(2)."""
    A = np.hstack([M.copy() % 2, np.eye(3, dtype=np.uint8)])
    for col in range(3):
        found = -1
        for r in range(col, 3):
            if A[r, col]:
                found = r
                break
        if found < 0:
            return None  # singular
        A[[col, found]] = A[[found, col]]
        for r in range(3):
            if r != col and A[r, col]:
                A[r] ^= A[col]
    return A[:, 3:] % 2

def build_shadow_system(support, tight_r9_lams=None):
    """Build the compressed 3×3 shadow system.
    
    Variables: Y_t ∈ Mat_3(F_2) for t=0..s-1.
    Encoded as 9-entry vectors: Y_t[3a+b] = Y_t[a,b].
    Total: s × 9 variables.
    """
    s = len(support)
    nv = s * 9
    
    # Build shadow target K_k for each of the 8 A-slices
    # A-position (i_k, j_k) → B⊗C block (j_k, i_k) → shadow E_{j_k, i_k}
    a_positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    shadow_targets = []
    for ai, aj in a_positions:
        # Shadow slice is E_{aj, ai} (3×3 elementary matrix)
        K = np.zeros((3,3), dtype=np.uint8)
        K[aj, ai] = 1  # tr(I_3) = 1 over F_2
        shadow_targets.append(K)
    
    rows_A = []
    rows_b = []
    
    # Tensor identity in shadow: for each slice k, each (a,b):
    # Σ_{t: bit k of a_t} Y_t[a,b] = K_k[a,b]
    for k in range(8):
        K = shadow_targets[k]
        for a in range(3):
            for b in range(3):
                row = np.zeros(nv, dtype=np.uint8)
                for t, av in enumerate(support):
                    if av & (1 << k):
                        row[t * 9 + 3*a + b] = 1
                rows_A.append(row)
                rows_b.append(K[a, b])
    
    # Trace equations: tr(Y_t Λ^{-1}) = 1 for tight rank-9, active t
    if tight_r9_lams:
        for lam in tight_r9_lams:
            Lambda = lambda_to_mat(lam)
            lr = int(mat_rank_gf2(Lambda))
            if lr != 3:
                continue
            Lambda_inv = mat_inv_gf2_3x3(Lambda)
            if Lambda_inv is None:
                continue
            
            # Active terms
            active = [t for t, a in enumerate(support) 
                     if bin(a & lam).count('1') % 2 == 1]
            if len(active) != 9:
                continue
            
            for t in active:
                # tr(M_λ^{-1} X_t) = Σ_{j,i} (Λ^{-1})_{ji} tr(X_block(j,i))
                # = Σ_{j,i} (Λ^{-1})_{ji} Y_t[j,i]
                # Coefficient of Y_t[j,i] (at var t*9+3j+i) is Λ^{-1}[j,i]
                row = np.zeros(nv, dtype=np.uint8)
                for j in range(3):
                    for i in range(3):
                        if Lambda_inv[j, i]:
                            row[t * 9 + 3*j + i] ^= 1
                rows_A.append(row)
                rows_b.append(1)
    
    return np.array(rows_A, dtype=np.uint8), np.array(rows_b, dtype=np.uint8)


def find_tight_r9(support):
    """Find all tight rank-9 contraction λ values."""
    tight = []
    for lam in range(1, 256):
        Lambda = lambda_to_mat(lam)
        lr = int(mat_rank_gf2(Lambda))
        if lr != 3:
            continue
        active = sum(1 for a in support if bin(a & lam).count('1') % 2 == 1)
        if active == 9:
            tight.append(lam)
    return tight


def main():
    L15 = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]
    tight_r9 = find_tight_r9(L15)
    
    print(f"L15 support: {L15}")
    print(f"Tight rank-9 contractions: {len(tight_r9)}")
    print(f"Shadow system: {len(L15)*9} variables")
    
    # 1. Tensor-only shadow
    A, b = build_shadow_system(L15, tight_r9_lams=None)
    cons, rA, rAb = gf2_consistent(A, b)
    print(f"\nTensor-only shadow: {cons}, rank {rA}/{len(A)} eqs, {len(L15)*9} vars")
    
    # 2. Full shadow
    A, b = build_shadow_system(L15, tight_r9_lams=tight_r9)
    cons, rA, rAb = gf2_consistent(A, b)
    print(f"Full shadow: consistent={cons}, rank={rA}, augmented={rAb}, "
          f"eqs={len(A)}, vars={len(L15)*9}")
    
    # 3. Per-contraction
    indiv_ok = 0
    for lam in tight_r9:
        A, b = build_shadow_system(L15, [lam])
        c, _, _ = gf2_consistent(A, b)
        if c:
            indiv_ok += 1
    print(f"Individual consistent: {indiv_ok}/{len(tight_r9)}")
    
    # 4. Exhaustive search for minimum inconsistent subset
    print(f"\nExhaustive min inconsistent search (shadow is FAST)...")
    min_found = None
    
    for size in range(2, len(tight_r9) + 1):
        n_comb = 1
        for i in range(size):
            n_comb = n_comb * (len(tight_r9) - i) // (i + 1)
        
        found_any = False
        count = 0
        examples = []
        
        for subset in itertools.combinations(tight_r9, size):
            count += 1
            A, b = build_shadow_system(L15, list(subset))
            c, _, _ = gf2_consistent(A, b)
            if not c:
                examples.append(list(subset))
                found_any = True
                if len(examples) >= 3:  # collect a few examples
                    break
        
        if found_any:
            print(f"  Size {size}: FIRST INCONSISTENT ({count}/{n_comb} checked)")
            print(f"    Example: {examples[0]}")
            min_found = {'size': size, 'examples': examples, 'checked': count, 'total': n_comb}
            break
        else:
            print(f"  Size {size}: all {n_comb} consistent")
    
    # If found, count ALL inconsistent subsets at this size
    if min_found:
        size = min_found['size']
        total_incons = 0
        for subset in itertools.combinations(tight_r9, size):
            A, b = build_shadow_system(L15, list(subset))
            c, _, _ = gf2_consistent(A, b)
            if not c:
                total_incons += 1
        n_total = 1
        for i in range(size):
            n_total = n_total * (len(tight_r9) - i) // (i + 1)
        print(f"  Total inconsistent at size {size}: {total_incons}/{n_total}")
        min_found['total_inconsistent'] = total_incons
    
    # 5. Coupling analysis with inverse masks
    print(f"\n=== Inverse mask analysis ===")
    # For each tight contraction, compute h_λ (the 9-bit inverse mask)
    inv_masks = {}
    for lam in tight_r9:
        Lambda = lambda_to_mat(lam)
        Lambda_inv = mat_inv_gf2_3x3(Lambda)
        # h_λ at position 3a+b = (Λ^{-1})[b,a]
        h = np.zeros(9, dtype=np.uint8)
        for a in range(3):
            for b in range(3):
                h[3*a+b] = Lambda_inv[b, a]
        inv_masks[lam] = h
        print(f"  λ={lam:3d}: Λ^-1 = {Lambda_inv.flatten().tolist()}, "
              f"h = {h.tolist()}, wt(h)={int(np.sum(h))}")
    
    # Check linear dependencies among inverse masks
    all_h = np.array([inv_masks[l] for l in tight_r9], dtype=np.uint8)
    h_rank = gf2_rref(all_h.copy())
    print(f"\n  Rank of 16 inverse masks: {h_rank}/9")
    print(f"  (Full rank = 9 means they span all of Mat_3(F_2))")
    
    # Save
    outdir = Path("data/coupled_dual_basis")
    outdir.mkdir(parents=True, exist_ok=True)
    
    result = {
        'support': L15,
        'tight_r9': tight_r9,
        'shadow_variables': len(L15) * 9,
        'tensor_equations': 72,
        'trace_equations_per_contraction': 9,
        'full_shadow_consistent': bool(cons),
        'full_shadow_rank': int(rA),
        'full_shadow_augmented': int(rAb),
        'individual_all_consistent': indiv_ok == len(tight_r9),
        'min_inconsistent': min_found,
        'inverse_mask_rank': int(h_rank),
    }
    
    with open(outdir / "shadow_system_analysis.json", 'w') as f:
        json.dump(result, f, indent=2, default=lambda x: x.tolist() if hasattr(x, 'tolist') else x)
    print(f"\nSaved to {outdir / 'shadow_system_analysis.json'}")

main()
