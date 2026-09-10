#!/usr/bin/env python3
"""analysis: Fast pair-removal D-defect analysis.
For a defect-1 deletion, compute D-defect for all C(22,2) = 231 pairs of column removals.
Find pairs where defect_20 = 2 (minimum possible), then do targeted 2-B search."""
from __future__ import annotations
import json, time, sys
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from linear_completion import (
    build_t333_f2, tensor_to_D, parse_qmm_scheme_f2,
    verify_decomposition_f2, mask_to_vec, vec_to_mask, gf2_solve_multi
)

def fast_rank_np(M):
    """Fast GF(2) rank using numpy with integer row operations."""
    A = M.copy().astype(np.uint8)
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        found = -1
        for i in range(r, rows):
            if A[i,c]:
                found = i; break
        if found < 0: continue
        A[[r,found]] = A[[found,r]]
        mask = A[:,c].astype(bool)
        mask[r] = False
        A[mask] ^= A[r]
        r += 1
    return r

def D_defect_np(K, D):
    rank_K = fast_rank_np(K.T.copy())
    KD = np.hstack([K, D])
    rank_KD = fast_rank_np(KD.T.copy())
    return rank_KD - rank_K

def build_K_np(A, B):
    r = len(A)
    K = np.zeros((81, r), dtype=np.uint8)
    for t in range(r):
        for s in range(9):
            if not ((A[t]>>s)&1): continue
            for b in range(9):
                if (B[t]>>b)&1:
                    K[s*9+b, t] = 1
    return K

def main():
    scheme = Path('data/cn122_3x3_r23_repro/scheme.qmm')
    outdir = Path('data/pair_dep')
    outdir.mkdir(parents=True, exist_ok=True)
    
    A23, B23, C23 = parse_qmm_scheme_f2(scheme)
    T = build_t333_f2()
    D = tensor_to_D(T)
    
    # Test deletion 3 (has one free column)
    del_t = 3
    A22 = [A23[t] for t in range(23) if t != del_t]
    B22 = [B23[t] for t in range(23) if t != del_t]
    K22 = build_K_np(A22, B22)
    
    base_d = D_defect_np(K22, D)
    print(f"Deletion {del_t}: base D-defect = {base_d}")
    
    # All pair removals
    t0 = time.time()
    pair_defects = {}
    defect_hist = {}
    for t1 in range(22):
        for t2 in range(t1+1, 22):
            cols = [i for i in range(22) if i != t1 and i != t2]
            K20 = K22[:, cols]
            d = D_defect_np(K20, D)
            pair_defects[(t1,t2)] = d
            defect_hist[d] = defect_hist.get(d, 0) + 1
    
    print(f"Pair removal defect histogram: {dict(sorted(defect_hist.items()))}")
    print(f"Pair analysis time: {time.time()-t0:.2f}s")
    
    # Find best pairs (defect 2)
    best = [(k, v) for k, v in pair_defects.items() if v == 2]
    print(f"Pairs with defect 2: {len(best)}")
    if best:
        print(f"First 10: {[b[0] for b in best[:10]]}")
    
    # For the best pair, do 2-B search (512*512 = 262K checks)
    if best:
        pair = best[0][0]
        t1, t2 = pair
        print(f"\n2-B search for pair ({t1},{t2})...")
        
        cols20 = [i for i in range(22) if i != t1 and i != t2]
        K20 = K22[:, cols20]
        
        t1_search = time.time()
        found = 0
        for d1 in range(512):
            b1 = B22[t1] ^ d1 if d1 > 0 else B22[t1]
            col1 = np.zeros((81,1), dtype=np.uint8)
            for s in range(9):
                if not ((A22[t1]>>s)&1): continue
                for beta in range(9):
                    if (b1>>beta)&1:
                        col1[s*9+beta, 0] = 1
            
            for d2 in range(512):
                b2 = B22[t2] ^ d2 if d2 > 0 else B22[t2]
                col2 = np.zeros((81,1), dtype=np.uint8)
                for s in range(9):
                    if not ((A22[t2]>>s)&1): continue
                    for beta in range(9):
                        if (b2>>beta)&1:
                            col2[s*9+beta, 0] = 1
                
                K_test = np.hstack([K20, col1, col2])
                if D_defect_np(K_test, D) == 0:
                    found += 1
                    if found <= 3:
                        # Verify!
                        B_new = list(B22)
                        B_new[t1] = b1; B_new[t2] = b2
                        K_full = build_K_np(A22, B_new)
                        CT = gf2_solve_multi(K_full, D)
                        if CT is not None:
                            C22 = [vec_to_mask(CT[i]) for i in range(22)]
                            diff = verify_decomposition_f2(A22, B_new, C22)
                            print(f"  d1={d1},d2={d2}: brent_diff={diff}")
                            if diff == 0:
                                print(f"  *** RANK-22 VERIFIED! ***")
                                dp = outdir / f'rank22_del{del_t}_p{t1}_{t2}_d{d1}_{d2}.json'
                                dp.write_text(json.dumps({
                                    'rank':22,'A':A22,'B':B_new,'C':C22,
                                    'brent_diff':0,'method':f'2B_del{del_t}'
                                },indent=2)+'\n')
            
            if (d1+1) % 64 == 0:
                elapsed = time.time() - t1_search
                print(f"  d1={d1}/511, found={found}, elapsed={elapsed:.1f}s", flush=True)
        
        print(f"  Total 2-B search: found={found}, elapsed={time.time()-t1_search:.1f}s")
    
    out = {
        'deletion': del_t,
        'pair_defect_hist': {str(k):v for k,v in sorted(defect_hist.items())},
        'pairs_with_defect_2': len(best),
        'elapsed_sec': time.time()-t0,
    }
    opath = outdir / f'pair_dep_del{del_t}.json'
    opath.write_text(json.dumps(out, indent=2, sort_keys=True)+'\n')
    print(f"\nSaved: {opath}")

if __name__ == '__main__':
    main()
