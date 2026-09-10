#!/usr/bin/env python3
"""analysis: Column dependency analysis and two-B-modification feasibility check.

For a defect-1 deletion from rank-23, analyze WHY single-B modification fails
and whether two-B modification can succeed.

Key insight: K_{22} has 22 columns spanning 22D with 8/9 D-directions covered.
For single-B mod at column t: removing column t → K_{21} defect might be 2.
Then the new column needs to cover 2 missing directions with one outer product.

For two-B mod at (t1,t2): K_{20} defect determines how many directions need
covering by 2 new columns.
"""
from __future__ import annotations
import json, time, sys, argparse
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from linear_completion import (
    build_t333_f2, tensor_to_D, parse_qmm_scheme_f2,
    verify_decomposition_f2, mask_to_vec, vec_to_mask,
    gf2_rref, gf2_solve_multi
)
from b_repair_hillclimb import build_K, D_defect


def column_dep_D(K22, D):
    """For each column of K22, compute D-defect of K with that column removed."""
    r = K22.shape[1]
    defects = []
    for t in range(r):
        cols = [i for i in range(r) if i != t]
        K21 = K22[:, cols]
        d = D_defect(K21, D)
        defects.append(d)
    return defects


def pair_dep_D(K22, D, target_defect_threshold=2):
    """For select column pairs, compute D-defect of K with both removed.
    Only test pairs where both individual removals give defect >= 2."""
    r = K22.shape[1]
    single = column_dep_D(K22, D)
    
    results = []
    for t1 in range(r):
        for t2 in range(t1+1, r):
            cols = [i for i in range(r) if i != t1 and i != t2]
            K20 = K22[:, cols]
            d = D_defect(K20, D)
            results.append({'t1': t1, 't2': t2, 'defect_20': d,
                           'defect_21_t1': single[t1], 'defect_21_t2': single[t2]})
    return results


def two_B_search(A22, B22, K22, D, pair_rec):
    """For a pair (t1, t2), search over all (delta1, delta2) to cover D."""
    t1, t2 = pair_rec['t1'], pair_rec['t2']
    target_defect = pair_rec['defect_20']
    
    # Build K20 without columns t1, t2
    r = len(A22)
    cols20 = [i for i in range(r) if i != t1 and i != t2]
    K20 = K22[:, cols20]
    
    found = []
    checked = 0
    
    for d1 in range(512):
        b1_new = B22[t1] ^ d1 if d1 > 0 else B22[t1]
        col1 = np.outer(mask_to_vec(A22[t1]), mask_to_vec(b1_new)).ravel().astype(np.uint8)
        
        for d2 in range(512):
            b2_new = B22[t2] ^ d2 if d2 > 0 else B22[t2]
            col2 = np.outer(mask_to_vec(A22[t2]), mask_to_vec(b2_new)).ravel().astype(np.uint8)
            
            K_test = np.hstack([K20, col1.reshape(-1,1), col2.reshape(-1,1)])
            d = D_defect(K_test, D)
            checked += 1
            
            if d == 0:
                found.append({'delta1': d1, 'delta2': d2, 
                             'new_B1': B22[t1]^d1 if d1>0 else B22[t1],
                             'new_B2': B22[t2]^d2 if d2>0 else B22[t2]})
                if len(found) >= 3:
                    return found, checked
    
    return found, checked


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--scheme', type=Path, required=True)
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--deletion', type=int, default=2)
    ap.add_argument('--top-pairs', type=int, default=5, 
                    help='Number of best pairs to try full 2-B search')
    args = ap.parse_args()
    
    t0 = time.time()
    outdir = args.outdir; outdir.mkdir(parents=True, exist_ok=True)
    
    A23, B23, C23 = parse_qmm_scheme_f2(args.scheme)
    T = build_t333_f2()
    D = tensor_to_D(T)
    
    del_t = args.deletion
    A22 = [A23[t] for t in range(23) if t != del_t]
    B22 = [B23[t] for t in range(23) if t != del_t]
    K22 = build_K(A22, B22)
    
    base_defect = D_defect(K22, D)
    print(f"Deletion {del_t}: base D-defect = {base_defect}")
    
    # Single-column removal dependency
    single_deps = column_dep_D(K22, D)
    dep_hist = {}
    for d in single_deps:
        dep_hist[d] = dep_hist.get(d, 0) + 1
    print(f"\nSingle-column removal D-defect histogram: {dep_hist}")
    print(f"Columns with defect 1 (free for replacement): "
          f"{[t for t, d in enumerate(single_deps) if d == 1]}")
    print(f"Columns with defect 2 (essential): "
          f"{[t for t, d in enumerate(single_deps) if d == 2]}")
    
    # If any column has defect 1 after removal, single-B search should work
    free_cols = [t for t, d in enumerate(single_deps) if d == 1]
    if free_cols:
        print(f"\n*** Free columns exist! Single-B mod should work for these. ***")
        # Quick verify: for each free column, find replacement
        for t in free_cols[:3]:
            print(f"  Testing free column {t}...")
            K21 = K22[:, [i for i in range(22) if i != t]]
            hit_count = 0
            for delta in range(1, 512):
                new_b = B22[t] ^ delta
                new_col = np.outer(mask_to_vec(A22[t]), mask_to_vec(new_b)).ravel().astype(np.uint8)
                K_test = np.hstack([K21, new_col.reshape(-1,1)])
                if D_defect(K_test, D) == 0:
                    hit_count += 1
                    if hit_count <= 2:
                        # Solve for C and verify
                        CT = gf2_solve_multi(K_test, D)
                        if CT is not None:
                            B_new = list(B22); B_new[t] = new_b
                            C22 = [vec_to_mask(CT[i]) for i in range(22)]
                            diff = verify_decomposition_f2(A22, B_new, C22)
                            print(f"    delta={delta}: D-defect=0, brent_diff={diff}")
                            if diff == 0:
                                print(f"    *** RANK-22 VERIFIED! ***")
                                dpath = outdir / f'rank22_del{del_t}_free{t}_d{delta}.json'
                                dpath.write_text(json.dumps({
                                    'rank': 22, 'A': A22, 'B': B_new, 'C': C22,
                                    'brent_diff': diff,
                                }, indent=2) + '\n')
            print(f"    Total D-defect-0 deltas: {hit_count}/511")
    
    # Pair analysis
    print(f"\nPair column-removal analysis...")
    pair_results = pair_dep_D(K22, D)
    pair_defect_hist = {}
    for pr in pair_results:
        d = pr['defect_20']
        pair_defect_hist[d] = pair_defect_hist.get(d, 0) + 1
    print(f"Pair removal D-defect histogram: {pair_defect_hist}")
    
    # Select best pairs (lowest defect after removal)
    pair_results.sort(key=lambda x: x['defect_20'])
    best_pairs = pair_results[:args.top_pairs]
    
    print(f"\nTop {len(best_pairs)} pairs by defect:")
    for pr in best_pairs:
        print(f"  ({pr['t1']},{pr['t2']}): defect_20={pr['defect_20']}, "
              f"single_deps=({pr['defect_21_t1']},{pr['defect_21_t2']})")
    
    # Full 2-B search for the best pair(s)
    if best_pairs and best_pairs[0]['defect_20'] <= 2:
        for pr in best_pairs[:2]:
            if pr['defect_20'] > 2:
                break
            print(f"\n  Full 2-B search for pair ({pr['t1']},{pr['t2']}), "
                  f"defect_20={pr['defect_20']}...")
            found, checked = two_B_search(A22, B22, K22, D, pr)
            print(f"    Checked: {checked}, found D-defect-0: {len(found)}")
            for f in found[:2]:
                B_new = list(B22)
                B_new[pr['t1']] = f['new_B1']
                B_new[pr['t2']] = f['new_B2']
                K_new = build_K(A22, B_new)
                CT = gf2_solve_multi(K_new, D)
                if CT is not None:
                    C22 = [vec_to_mask(CT[i]) for i in range(22)]
                    diff = verify_decomposition_f2(A22, B_new, C22)
                    print(f"    2-mod: delta=({f['delta1']},{f['delta2']}), brent_diff={diff}")
                    if diff == 0:
                        print(f"    *** RANK-22 VERIFIED via 2-B mod! ***")
    
    # Save results
    out = {
        'deletion': del_t,
        'base_defect': base_defect,
        'single_column_dep_defects': single_deps,
        'single_dep_hist': dep_hist,
        'free_columns': free_cols,
        'pair_defect_hist': pair_defect_hist,
        'best_pairs': best_pairs[:10],
        'elapsed_sec': time.time() - t0,
    }
    opath = outdir / f'column_dep_del{del_t}.json'
    opath.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved: {opath}")

if __name__ == '__main__':
    main()
