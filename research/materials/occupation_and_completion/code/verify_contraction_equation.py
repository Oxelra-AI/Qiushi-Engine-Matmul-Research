#!/usr/bin/env python3
"""
Deep verification of the contraction equation and dual-basis for cn122 core.
Check: does Σ_{t ∈ I_λ} b_t c_t^T actually equal M_λ for tight contractions?
"""

import numpy as np

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

def load_cn122():
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
    
    core = []
    for term in terms:
        u = term['u']
        a_bits = 0
        for bit_idx, (i,j) in enumerate(positions):
            if u[3*i + j]:
                a_bits |= (1 << bit_idx)
        # Keep all terms, including E00-only (a_bits=0)
        core.append({
            'a': a_bits,
            'u_full': np.array(term['u'], dtype=np.uint8),
            'b': np.array(term['v'], dtype=np.uint8),
            'c': np.array(term['w'], dtype=np.uint8),
            'has_e00': bool(u[0]),  # u[0] = A_{00} component
            'idx': term['idx'],
        })
    return core

def main():
    core = load_cn122()
    print(f"Total terms: {len(core)}")
    
    # Split: core terms (a ≠ 0) and pure E00 terms (a = 0 with u[0]=1)
    core_terms = [t for t in core if t['a'] != 0]
    e00_terms = [t for t in core if t['a'] == 0]
    print(f"Core-contributing terms: {len(core_terms)}")
    print(f"Pure E00 terms: {len(e00_terms)}")
    
    # Check how many terms have E00 component
    with_e00 = [t for t in core if t['has_e00']]
    print(f"Terms with E00 component: {len(with_e00)}")
    for t in with_e00:
        print(f"  term {t['idx']}: a={t['a']}, u_full={t['u_full'].tolist()}")
    
    # Build expected core tensor
    positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    T_core = np.zeros((8, 9, 9), dtype=np.uint8)
    for idx, (ai, aj) in enumerate(positions):
        for k in range(3):
            # Correct convention: A-entry (i,j) maps to B⊗C block (j,i), so M_λ = Λ^T⊗I₃.
            T_core[idx, 3*aj + k, 3*ai + k] = 1
    
    # Verify that core terms sum to core tensor
    T_check = np.zeros((8, 9, 9), dtype=np.uint8)
    for t in core_terms:
        for bit_idx in range(8):
            if t['a'] & (1 << bit_idx):
                T_check[bit_idx] += np.outer(t['b'], t['c'])
    T_check %= 2
    
    if np.array_equal(T_core, T_check):
        print("\n✓ Core terms correctly reconstruct T_core")
    else:
        diff = np.sum(T_core != T_check)
        print(f"\n✗ Core reconstruction FAILS: {diff} mismatched entries")
        # Check if including the E00 component helps
        # Terms with E00 also contribute to their respective core slices
        T_check2 = np.zeros((8, 9, 9), dtype=np.uint8)
        for t in core:  # ALL terms, including those with a=0
            for bit_idx in range(8):
                if t['a'] & (1 << bit_idx):
                    T_check2[bit_idx] += np.outer(t['b'], t['c'])
        T_check2 %= 2
        if np.array_equal(T_core, T_check2):
            print("  (Using all terms: ✓)")
    
    # Now test contraction equation for tight rank-9
    print(f"\n=== Contraction equation verification ===")
    for lam in [43, 51, 71]:  # First few tight rank-9 from above
        Lambda = lambda_to_mat(lam)
        # Rank over F2, not over the reals; masks 119 and 175 differ.
        lr = gf2_rref(Lambda)[1]
        if lr != 3:
            continue
        
        M_expected = np.kron(Lambda.T, np.eye(3, dtype=np.uint8)) % 2
        
        # Active terms
        active = [i for i, t in enumerate(core_terms)
                  if bin(t['a'] & lam).count('1') % 2 == 1]
        
        # Compute actual sum
        M_actual = np.zeros((9,9), dtype=np.uint8)
        for t_idx in active:
            t = core_terms[t_idx]
            M_actual += np.outer(t['b'], t['c'])
        M_actual %= 2
        
        match = np.array_equal(M_expected, M_actual)
        print(f"\nlam={lam}: |I|={len(active)}, rank(Λ)={lr}, "
              f"M_actual==M_expected: {match}")
        if not match:
            diff = np.sum(M_expected != M_actual)
            print(f"  Mismatches: {diff} entries")
            
            # Check: is M_actual = M_expected + something from E00?
            # Terms with has_e00 and a&lam parity=1 contribute to contraction
            extra = np.zeros((9,9), dtype=np.uint8)
            for t in core:
                if t['a'] == 0:
                    continue
                if t['has_e00'] and bin(t['a'] & lam).count('1') % 2 == 1:
                    # This term has E00 but we're only counting its core contribution
                    pass  # already counted above
            
            print(f"  rank_F2(M_actual)={gf2_rref(M_actual)[1]}")
            print(f"  rank_F2(M_expected)={gf2_rref(M_expected)[1]}")
        else:
            # Verify dual-basis
            M_inv = mat_inv_gf2(M_expected)
            bs = [core_terms[t]['b'] for t in active]
            cs = [core_terms[t]['c'] for t in active]
            
            B = np.column_stack(bs) % 2  # 9×9
            C = np.column_stack(cs) % 2  # 9×9
            
            B_rank = gf2_rref(B.T)[1]
            C_rank = gf2_rref(C.T)[1]
            
            # C^T M^{-1} B should be I_9
            dual_prod = (C.T @ M_inv @ B) % 2
            is_identity = np.array_equal(dual_prod, np.eye(9, dtype=np.uint8))
            
            print(f"  B rank: {B_rank}, C rank: {C_rank}")
            print(f"  C^T M^-1 B = I_9: {is_identity}")
            if not is_identity:
                diag = np.diag(dual_prod)
                print(f"  Diagonal: {diag.tolist()}")
                print(f"  Diagonal sum: {np.sum(diag)}")

main()
