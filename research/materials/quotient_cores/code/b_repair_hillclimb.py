#!/usr/bin/env python3
"""analysis: B-repair hill-climb for rank-22 linear completion.

For a given A-multiset (from rank-23 deletion or any Wang-admissible source),
search for B-masks via local bit-flipping so that col(K) covers all 9 D-columns.
C is then determined by linear algebra.

The objective is: defect = number of D-columns NOT in col(K).
Each ARTIFACT flips one bit of one B-mask and checks if defect decreases.

Also: for each rank-23 deletion, analyze K_{-t} defect per column removal,
to understand the column-space geometry.
"""
from __future__ import annotations
import json, time, sys, argparse, random
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from linear_completion import (
    build_t333_f2, tensor_to_D, parse_qmm_scheme_f2, verify_decomposition_f2,
    mask_to_vec, vec_to_mask, gf2_rref, gf2_solve_multi
)


def build_K(A, B):
    """Build 81×r K matrix."""
    r = len(A)
    K = np.zeros((81, r), dtype=np.uint8)
    for t in range(r):
        a = np.array([(A[t] >> i) & 1 for i in range(9)], dtype=np.uint8)
        b = np.array([(B[t] >> i) & 1 for i in range(9)], dtype=np.uint8)
        K[:, t] = np.outer(a, b).ravel()
    return K


def D_defect(K, D):
    """Number of D-columns not in col(K). 0 means completion possible."""
    KT = K.T.copy()
    _, _, rank_K = gf2_rref(KT)
    K_D = np.hstack([K, D])
    _, _, rank_KD = gf2_rref(K_D.T.copy())
    return rank_KD - rank_K


def column_removal_analysis(A22, B22, D):
    """For each term t, compute D-defect after removing column t."""
    r = len(A22)
    results = []
    for t in range(r):
        A_rem = [A22[i] for i in range(r) if i != t]
        B_rem = [B22[i] for i in range(r) if i != t]
        K_rem = build_K(A_rem, B_rem)
        d = D_defect(K_rem, D)
        results.append({'removed_term': t, 'A_mask': A22[t], 'B_mask': B22[t], 'defect_after_removal': d})
    return results


def hill_climb_B(A, B_init, D, max_iters=10000, max_restarts=5, seed=42):
    """Hill-climb: flip one B-bit at a time to minimize D-defect.
    Returns best (B, defect, history)."""
    rng = random.Random(seed)
    r = len(A)
    best_B = list(B_init)
    best_defect = D_defect(build_K(A, best_B), D)
    history = [{'iter': 0, 'defect': best_defect, 'action': 'init'}]
    
    if best_defect == 0:
        return best_B, 0, history
    
    for restart in range(max_restarts):
        B = list(best_B)
        current_defect = best_defect
        stuck = 0
        
        for it in range(max_iters):
            improved = False
            # Try all single-bit flips in random order
            moves = [(t, j) for t in range(r) for j in range(9)]
            rng.shuffle(moves)
            
            for t, j in moves:
                old_b = B[t]
                B[t] = old_b ^ (1 << j)
                K = build_K(A, B)
                d = D_defect(K, D)
                
                if d < current_defect:
                    current_defect = d
                    improved = True
                    history.append({'iter': restart * max_iters + it, 'defect': d, 
                                    'action': f'flip t={t} j={j}', 'restart': restart})
                    if d < best_defect:
                        best_defect = d
                        best_B = list(B)
                    if d == 0:
                        return best_B, 0, history
                    break  # Restart inner loop with new defect
                else:
                    B[t] = old_b  # Revert
            
            if not improved:
                stuck += 1
                if stuck >= 3:
                    # Random perturbation
                    for _ in range(rng.randint(1, 3)):
                        t = rng.randrange(r)
                        j = rng.randrange(9)
                        B[t] ^= (1 << j)
                    current_defect = D_defect(build_K(A, B), D)
                    history.append({'iter': restart * max_iters + it, 'defect': current_defect, 
                                    'action': 'perturbation', 'restart': restart})
                    stuck = 0
    
    return best_B, best_defect, history


def random_B_start(A, D, rng):
    """Generate a random B initialization."""
    r = len(A)
    return [rng.randrange(1, 512) for _ in range(r)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--scheme', type=Path, required=True)
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--mode', choices=['analyze', 'search', 'both'], default='both')
    ap.add_argument('--max-iters', type=int, default=5000)
    ap.add_argument('--restarts', type=int, default=10)
    ap.add_argument('--random-starts', type=int, default=5,
                    help='Number of random B initializations to try')
    args = ap.parse_args()
    
    t0 = time.time()
    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)
    
    A23, B23, C23 = parse_qmm_scheme_f2(args.scheme)
    T = build_t333_f2()
    D = tensor_to_D(T)
    
    results = {'schema': 'b_repair_v1', 'deletion_analysis': [], 'search_results': []}
    
    if args.mode in ('analyze', 'both'):
        print("=== Column removal analysis ===")
        for del_t in range(23):
            A22 = [A23[t] for t in range(23) if t != del_t]
            B22 = [B23[t] for t in range(23) if t != del_t]
            K = build_K(A22, B22)
            base_defect = D_defect(K, D)
            
            if base_defect == 1:  # Only analyze defect-1 deletions
                removal = column_removal_analysis(A22, B22, D)
                # Find columns whose removal doesn't increase defect
                safe_removals = [r for r in removal if r['defect_after_removal'] <= base_defect]
                unsafe_removals = [r for r in removal if r['defect_after_removal'] > base_defect]
                
                print(f"  del {del_t}: base_defect={base_defect}, "
                      f"safe_removals={len(safe_removals)}, "
                      f"defects_after_removal: {sorted(set(r['defect_after_removal'] for r in removal))}")
                
                results['deletion_analysis'].append({
                    'deleted_term': del_t,
                    'base_defect': base_defect,
                    'safe_removal_count': len(safe_removals),
                    'removal_defect_hist': {str(d): sum(1 for r in removal if r['defect_after_removal'] == d) 
                                           for d in sorted(set(r['defect_after_removal'] for r in removal))},
                })
    
    if args.mode in ('search', 'both'):
        print("\n=== B-repair hill-climb search ===")
        
        # Try each defect-1 deletion as starting point
        for del_t in [2, 3, 4, 6, 8, 14, 15, 20, 21, 22]:
            A22 = [A23[t] for t in range(23) if t != del_t]
            B22 = [B23[t] for t in range(23) if t != del_t]
            
            print(f"\n  Starting from deletion {del_t} (rank-23 B factors)")
            B_best, defect, hist = hill_climb_B(A22, B22, D, 
                                                max_iters=args.max_iters, 
                                                max_restarts=args.restarts)
            
            rec = {
                'deleted_term': del_t,
                'start': 'rank23_B',
                'final_defect': defect,
                'steps': len(hist),
                'history_tail': hist[-5:],
            }
            
            if defect == 0:
                # SOLVE FOR C AND VERIFY!
                K = build_K(A22, B_best)
                CT = gf2_solve_multi(K, D)
                if CT is not None:
                    C22 = [vec_to_mask(CT[t]) for t in range(22)]
                    diff = verify_decomposition_f2(A22, B_best, C22)
                    rec['brent_diff'] = diff
                    rec['B_masks'] = B_best
                    rec['C_masks'] = C22
                    print(f"    *** DEFECT 0 REACHED! Brent diff = {diff} ***")
                    if diff == 0:
                        print(f"    *** VERIFIED RANK-22 DECOMPOSITION! ***")
                        dpath = outdir / f'rank22_hilclimb_del{del_t}.json'
                        dpath.write_text(json.dumps({
                            'rank': 22, 'A': A22, 'B': B_best, 'C': C22,
                            'brent_diff': diff, 'method': f'deletion_{del_t}_B_hillclimb',
                        }, indent=2, sort_keys=True) + '\n')
            else:
                print(f"    Best defect: {defect}")
            
            results['search_results'].append(rec)
        
        # Also try random B starts with deletion A-multisets
        if args.random_starts > 0:
            print(f"\n  Random B starts ({args.random_starts} per deletion)")
            for del_t in [2, 4, 15]:  # Top 3 defect-1 deletions
                A22 = [A23[t] for t in range(23) if t != del_t]
                for rs in range(args.random_starts):
                    rng = random.Random(del_t * 1000 + rs)
                    B_rand = random_B_start(A22, D, rng)
                    init_defect = D_defect(build_K(A22, B_rand), D)
                    
                    B_best, defect, hist = hill_climb_B(A22, B_rand, D,
                                                        max_iters=args.max_iters,
                                                        max_restarts=args.restarts,
                                                        seed=del_t*1000+rs+100)
                    
                    print(f"    del {del_t} random {rs}: init_defect={init_defect}, final={defect}")
                    
                    rec = {
                        'deleted_term': del_t,
                        'start': f'random_{rs}',
                        'init_defect': init_defect,
                        'final_defect': defect,
                        'steps': len(hist),
                    }
                    
                    if defect == 0:
                        K = build_K(A22, B_best)
                        CT = gf2_solve_multi(K, D)
                        if CT is not None:
                            C22 = [vec_to_mask(CT[t]) for t in range(22)]
                            diff = verify_decomposition_f2(A22, B_best, C22)
                            rec['brent_diff'] = diff
                            rec['B_masks'] = B_best
                            print(f"    *** DEFECT 0 from random start! Brent diff = {diff} ***")
                            if diff == 0:
                                print(f"    *** VERIFIED RANK-22 DECOMPOSITION! ***")
                    
                    results['search_results'].append(rec)
    
    results['elapsed_sec'] = time.time() - t0
    opath = outdir / 'b_repair.json'
    opath.write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved: {opath}, elapsed: {results['elapsed_sec']:.2f}s")

if __name__ == '__main__':
    main()
