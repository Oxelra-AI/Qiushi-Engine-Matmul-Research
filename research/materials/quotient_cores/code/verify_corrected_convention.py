#!/usr/bin/env python3
"""Quick test: verify corrected core tensor matches cn122 decomposition."""

import numpy as np
import sys
sys.path.insert(0, 'scripts')
from coupled_dual_basis_system import (
    build_e11_core, contraction_matrix, lambda_to_mat, mat_inv_gf2,
    gf2_rref, load_cn122_core
)

def main():
    T_core, a_positions = build_e11_core()
    print(f"Core tensor shape: {T_core.shape}, nnz: {np.sum(T_core)}")
    
    # Load cn122 core terms
    scheme_path = "data/cn122_3x3_r23_repro/scheme.qmm"
    core_terms = load_cn122_core(scheme_path)
    print(f"Core terms: {len(core_terms)}")
    
    # Reconstruct tensor from terms
    T_check = np.zeros((8, 9, 9), dtype=np.uint8)
    for t in core_terms:
        for bit_idx in range(8):
            if t['a'] & (1 << bit_idx):
                T_check[bit_idx] += np.outer(t['b'], t['c'])
    T_check %= 2
    
    match = np.array_equal(T_core, T_check)
    print(f"Core reconstruction matches: {match}")
    if not match:
        diff = np.sum(T_core != T_check)
        print(f"  Mismatched entries: {diff}")
        return
    
    # Test contractions: M_λ = Λ^T ⊗ I₃
    print(f"\n=== Contraction verification ===")
    for lam in range(1, 256):
        Lambda = lambda_to_mat(lam)
        # Rank over F2, not over the reals; masks 119 and 175 differ.
        lr = gf2_rref(Lambda)[1]
        if lr != 3:
            continue
        
        M = contraction_matrix(lam)
        
        # Active terms
        active = [i for i, t in enumerate(core_terms)
                  if bin(t['a'] & lam).count('1') % 2 == 1]
        
        if len(active) != 9:
            continue  # only test tight rank-9
        
        # Sum of active terms
        M_sum = np.zeros((9,9), dtype=np.uint8)
        for t_idx in active:
            t = core_terms[t_idx]
            M_sum += np.outer(t['b'], t['c'])
        M_sum %= 2
        
        match = np.array_equal(M, M_sum)
        if not match:
            diff = np.sum(M != M_sum)
            print(f"  lam={lam}: MISMATCH ({diff} entries)")
            continue
        
        # Check dual-basis
        M_inv = mat_inv_gf2(M)
        bs = [core_terms[t]['b'] for t in active]
        cs = [core_terms[t]['c'] for t in active]
        
        B = np.column_stack(bs) % 2
        C = np.column_stack(cs) % 2
        
        dual = (C.T @ M_inv @ B) % 2
        is_id = np.array_equal(dual, np.eye(9, dtype=np.uint8))
        
        diag_pass = sum(1 for k in range(9) if dual[k,k] == 1)
        offdiag_pass = sum(1 for s in range(9) for t in range(9) 
                         if s != t and dual[s,t] == 0)
        
        print(f"  lam={lam}: contraction ✓, dual-basis={is_id}, "
              f"diag={diag_pass}/9, offdiag={offdiag_pass}/72")
        if not is_id and diag_pass < 9:
            break  # stop on first failure for analysis
    
    # Run L15 trace system with corrected convention
    print(f"\n=== L15 trace system (corrected convention) ===")
    from coupled_dual_basis_system import (
        support_active_sets, find_tight_contractions, check_combined_system
    )
    
    L15 = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]
    active = support_active_sets(L15)
    tight = find_tight_contractions(L15, active)
    tight_r9 = {l: v for l, v in tight.items() if v['lambda_rank'] == 3}
    
    result_tensor = check_combined_system(L15, T_core, tight_r9, active, include_trace=False)
    result_full = check_combined_system(L15, T_core, tight_r9, active, include_trace=True)
    
    print(f"Tight rank-9 contractions: {len(tight_r9)}")
    print(f"Tensor-only: consistent={result_tensor['consistent']}, rank={result_tensor['rank_A']}")
    print(f"Full trace:  consistent={result_full['consistent']}, "
          f"rank={result_full['rank_combined']}, augmented={result_full['rank_combined_augmented']}")
    print(f"Trace rank gain: {result_full['trace_rank_gain']}")

main()
