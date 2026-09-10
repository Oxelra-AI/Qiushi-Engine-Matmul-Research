#!/usr/bin/env python3
"""analysis: Analyze K-defect for peer Wang-admissible A-multisets and rank-23 deletions.

Key questions:
1. What is the minimum achievable D-defect for a given A over all B choices?
2. How does the D-defect behave for random B?
3. Is there a fundamental obstruction from A alone?

The D-defect depends on B. For a given A, the achievable directions are:
V_A = span{a_t ⊗ e_j : t=1..r, j=0..8}
which has dimension 9 * dim(span{a_1,...,a_r}).

If span(A) has full rank 9, V_A = F₂^81 and D is achievable in principle.
But we need 22 specific columns of K to span col(D), not just V_A.

This script:
1. Computes dim(span(A)) for various A-multisets
2. For each, samples random B and measures D-defect distribution
3. Runs B hill-climb and reports minimum defect found
"""
from __future__ import annotations
import json, time, sys, random, argparse
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from linear_completion import (
    build_t333_f2, tensor_to_D, parse_qmm_scheme_f2, verify_decomposition_f2,
    mask_to_vec, vec_to_mask, gf2_rref, gf2_solve_multi
)
from b_repair_hillclimb import build_K, D_defect, hill_climb_B


def A_span_dim(A):
    """Dimension of span of A-masks over F₂."""
    vecs = np.array([mask_to_vec(a) for a in A], dtype=np.uint8)
    _, _, r = gf2_rref(vecs)
    return r


def VA_contains_D(A, D):
    """Check if V_A = span{a_t ⊗ e_j} contains all D-columns."""
    # V_A has dimension 9 * dim(span(A)) if span is "generic"
    # Build V_A basis
    basis_vecs = []
    for a in A:
        a_vec = mask_to_vec(a)
        for j in range(9):
            ej = np.zeros(9, dtype=np.uint8)
            ej[j] = 1
            v = np.outer(a_vec, ej).ravel()
            basis_vecs.append(v)
    V = np.array(basis_vecs, dtype=np.uint8)
    _, _, rank_V = gf2_rref(V)
    
    # Check each D-column
    for c in range(D.shape[1]):
        V_aug = np.vstack([V, D[:, c]])
        _, _, rank_aug = gf2_rref(V_aug)
        if rank_aug > rank_V:
            return False, rank_V
    return True, rank_V


def random_B_defect_sample(A, D, n_samples=100, seed=42):
    """Sample random B and measure D-defect distribution."""
    rng = random.Random(seed)
    r = len(A)
    defects = []
    for _ in range(n_samples):
        B = [rng.randrange(1, 512) for _ in range(r)]
        K = build_K(A, B)
        d = D_defect(K, D)
        defects.append(d)
    return defects


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--scheme', type=Path, required=True)
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--peer-multiset', type=str, default='400,260,73,393,292,8,265,274,269,72,392,144,278,9,256,146,448,7,32,268,56,16')
    args = ap.parse_args()
    
    t0 = time.time()
    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)
    
    A23, B23, C23 = parse_qmm_scheme_f2(args.scheme)
    T = build_t333_f2()
    D = tensor_to_D(T)
    
    results = {'schema': 'K_defect_analysis_v1', 'analyses': []}
    
    # Analyze rank-23 full scheme
    A_dim = A_span_dim(A23)
    print(f"Rank-23 A-masks: span dimension = {A_dim}")
    K23 = build_K(A23, B23)
    d23 = D_defect(K23, D)
    print(f"Rank-23 K defect (with original B): {d23}")
    
    # Analyze peer candidate
    peer_A = [int(x) for x in args.peer_multiset.split(',')]
    peer_dim = A_span_dim(peer_A)
    va_ok, va_rank = VA_contains_D(peer_A, D)
    print(f"\nPeer A-multiset: span dim = {peer_dim}, V_A rank = {va_rank}, V_A ⊃ D: {va_ok}")
    
    if va_ok:
        # Sample random B
        defects = random_B_defect_sample(peer_A, D, n_samples=200)
        defect_hist = {}
        for d in defects:
            defect_hist[d] = defect_hist.get(d, 0) + 1
        print(f"  Random B defect distribution (200 samples): {defect_hist}")
        
        # Hill-climb from random starts
        min_defect = 9
        for trial in range(10):
            rng = random.Random(trial * 100)
            B_rand = [rng.randrange(1, 512) for _ in range(len(peer_A))]
            B_best, def_best, _ = hill_climb_B(peer_A, B_rand, D, 
                                                max_iters=2000, max_restarts=3, 
                                                seed=trial*100+7)
            min_defect = min(min_defect, def_best)
            print(f"  Trial {trial}: final defect = {def_best}")
        
        results['analyses'].append({
            'name': 'peer_candidate1',
            'A': peer_A,
            'A_span_dim': peer_dim,
            'VA_rank': va_rank,
            'VA_contains_D': va_ok,
            'random_B_defect_hist': defect_hist,
            'hillclimb_min_defect': min_defect,
        })
    
    # Analyze each defect-1 deletion
    print("\n=== Defect-1 deletions ===")
    for del_t in range(23):
        A22 = [A23[t] for t in range(23) if t != del_t]
        B22 = [B23[t] for t in range(23) if t != del_t]
        K = build_K(A22, B22)
        base_d = D_defect(K, D)
        
        if base_d == 1:
            ad = A_span_dim(A22)
            va_ok, va_rank = VA_contains_D(A22, D)
            defects = random_B_defect_sample(A22, D, n_samples=100, seed=del_t*10)
            dh = {}
            for d in defects:
                dh[d] = dh.get(d, 0) + 1
            
            print(f"  del {del_t}: A_dim={ad}, VA⊃D={va_ok}, "
                  f"random defect hist: {dh}")
            
            results['analyses'].append({
                'name': f'deletion_{del_t}',
                'A_span_dim': ad,
                'VA_contains_D': va_ok,
                'VA_rank': va_rank,
                'base_defect_with_rank23_B': base_d,
                'random_B_defect_hist': {str(k): v for k, v in sorted(dh.items())},
            })
    
    results['elapsed_sec'] = time.time() - t0
    opath = outdir / 'K_defect_analysis.json'
    opath.write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved: {opath}")

if __name__ == '__main__':
    main()
