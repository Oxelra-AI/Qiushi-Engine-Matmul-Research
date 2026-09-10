#!/usr/bin/env python3
"""
Verify the trace convention on the cn122 core's actual factors.

For each tight rank-9 contraction of the 21-TERM core (not the 18-direction support),
check c_t^T M_λ^{-1} b_t = 1 for all 9 active terms, using the corrected convention.
Also check off-diagonal: c_s^T M_λ^{-1} b_t = 0 for s ≠ t (both in I_λ).
"""

import numpy as np
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

def mat_inv_gf2(M):
    n = M.shape[0]
    A = np.hstack([M.copy() % 2, np.eye(n, dtype=np.uint8)])
    rref, r, _ = gf2_rref(A)
    assert r == n, f"Not invertible (rank {r})"
    return rref[:, n:] % 2

def lambda_to_mat(lam_int):
    positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    M = np.zeros((3,3), dtype=np.uint8)
    for bit_idx, (i,j) in enumerate(positions):
        if lam_int & (1 << bit_idx):
            M[i,j] = 1
    return M

def load_cn122_terms():
    scheme_path = "data/cn122_3x3_r23_repro/scheme.qmm"
    positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    
    terms = []
    with open(scheme_path) as f:
        lines = f.readlines()
    
    current = {}
    for line in lines:
        line = line.strip()
        if line.startswith('term '):
            if current and 'u' in current:
                terms.append(current)
            current = {'idx': int(line.split()[1])}
        elif line.startswith('u '):
            current['u'] = [int(x) % 2 for x in line.split()[1:]]
        elif line.startswith('v '):
            current['v'] = [int(x) % 2 for x in line.split()[1:]]
        elif line.startswith('w '):
            current['w'] = [int(x) % 2 for x in line.split()[1:]]
    if current and 'u' in current:
        terms.append(current)
    
    core_terms = []
    for term in terms:
        u = term['u']
        a_bits = 0
        for bit_idx, (i,j) in enumerate(positions):
            if u[3*i + j]:
                a_bits |= (1 << bit_idx)
        if a_bits != 0:
            core_terms.append({
                'a': a_bits,
                'b': np.array(term['v'], dtype=np.uint8),
                'c': np.array(term['w'], dtype=np.uint8),
                'original_idx': term['idx'],
            })
    return core_terms

def main():
    core_terms = load_cn122_terms()
    print(f"Core terms: {len(core_terms)}")
    
    # Find tight rank-9 contractions of the 21-TERM core
    n_terms = len(core_terms)
    
    tight_r9 = {}
    for lam in range(1, 256):
        Lambda = lambda_to_mat(lam)
        # Rank over F2, not over the reals; masks 119 and 175 differ.
        lr = gf2_rref(Lambda)[1]
        if lr != 3:
            continue
        # Active TERMS (not directions)
        active = [t for t in range(n_terms) 
                  if bin(core_terms[t]['a'] & lam).count('1') % 2 == 1]
        if len(active) == 9:  # tight
            tight_r9[lam] = active
    
    print(f"Tight rank-9 contractions (21-term): {len(tight_r9)}")
    
    # Check dual-basis conditions
    diagonal_pass = 0
    diagonal_fail = 0
    offdiag_pass = 0
    offdiag_fail = 0
    
    for lam, active in tight_r9.items():
        Lambda = lambda_to_mat(lam)
        M = np.kron(Lambda.T, np.eye(3, dtype=np.uint8)) % 2
        M_inv = mat_inv_gf2(M)
        
        bs = [core_terms[t]['b'] for t in active]
        cs = [core_terms[t]['c'] for t in active]
        
        # Diagonal: c_t^T M^{-1} b_t should be 1
        for k in range(9):
            val = int(cs[k] @ M_inv @ bs[k]) % 2
            if val == 1:
                diagonal_pass += 1
            else:
                diagonal_fail += 1
                if diagonal_fail <= 5:
                    print(f"  DIAGONAL FAIL: lam={lam}, term_idx={active[k]}, "
                          f"a={core_terms[active[k]]['a']}, val={val}")
        
        # Off-diagonal: c_s^T M^{-1} b_t should be 0 for s≠t  
        for s in range(9):
            for t in range(9):
                if s == t:
                    continue
                val = int(cs[s] @ M_inv @ bs[t]) % 2
                if val == 0:
                    offdiag_pass += 1
                else:
                    offdiag_fail += 1
    
    print(f"\nDiagonal (c_t^T M^-1 b_t = 1):")
    print(f"  Pass: {diagonal_pass}, Fail: {diagonal_fail}")
    print(f"Off-diagonal (c_s^T M^-1 b_t = 0 for s≠t):")
    print(f"  Pass: {offdiag_pass}, Fail: {offdiag_fail}")
    
    # Also verify using trace formula: tr(M^{-1} X_t) = Σ_{r,s} M_inv[r,s] X_t[s,r]
    print(f"\nTrace formula verification (tr(M^-1 X_t) using entry-level sum):")
    trace_pass = 0
    trace_fail = 0
    for lam, active in list(tight_r9.items())[:3]:  # first 3 contractions
        Lambda = lambda_to_mat(lam)
        M = np.kron(Lambda.T, np.eye(3, dtype=np.uint8)) % 2
        M_inv = mat_inv_gf2(M)
        
        for k, t in enumerate(active):
            b = core_terms[t]['b']
            c = core_terms[t]['c']
            X = np.outer(b, c) % 2
            
            # Method 1: c^T M^{-1} b (correct)
            val1 = int(c @ M_inv @ b) % 2
            
            # Method 2: tr(M^{-1} X) = Σ_{r,s} M_inv[r,s] X[s,r]
            val2 = 0
            for r in range(9):
                for s in range(9):
                    val2 ^= (int(M_inv[r, s]) & int(X[s, r]))
            
            # Method 3: wrong convention (M_inv[r,s] * X[r,s] - the transpose error)
            val3 = 0
            for r in range(9):
                for s in range(9):
                    val3 ^= (int(M_inv[r, s]) & int(X[r, s]))
            
            agree = "✓" if val1 == val2 else "✗"
            if k == 0:
                print(f"  lam={lam}: c^T M^-1 b={val1}, tr(M^-1 X)={val2}, "
                      f"wrong_conv={val3} {agree}")

main()
