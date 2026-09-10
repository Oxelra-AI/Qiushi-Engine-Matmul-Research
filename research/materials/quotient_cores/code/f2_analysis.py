#!/usr/bin/env python3
r"""analysisc: F2 rank-shortening analysis for T333 slices.

Over F_2, each T333 W-slice is a rank-3 binary 9×9 matrix.
For D=I: a rank-22 decomposition needs 13 shared rank-1 binary matrices
that simultaneously reduce all 9 rank-3 slices to rank 1.

This script:
1. Enumerates all nonzero rank-1 binary 9×9 matrices.
2. For each T333 slice, counts how many rank-1 corrections reduce rank by 1.
3. Analyzes pairwise compatibility: which pairs of corrections jointly reduce
   a slice to rank 1.
4. Checks whether the cn122 mod-2 decomposition gives a valid chart.
"""
import numpy as np
import time, json
from pathlib import Path

def make_T333_f2():
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T

def rank_f2(M):
    """Rank of a binary matrix over F_2 via Gaussian elimination."""
    M = M.copy().astype(np.uint8)
    m, n = M.shape
    row = 0
    for col in range(n):
        if row >= m: break
        piv = -1
        for r in range(row, m):
            if M[r, col]:
                piv = r; break
        if piv < 0: continue
        if piv != row:
            M[[row, piv]] = M[[piv, row]]
        for r in range(m):
            if r != row and M[r, col]:
                M[r] ^= M[row]
        row += 1
    return row

def enum_rank1_f2_9x9():
    """Enumerate all nonzero rank-1 9×9 binary matrices u v^T.
    u, v ∈ F_2^9 \ {0}.  Total: 511 * 511 = 261121.
    But u v^T = u' v'^T iff (u,v) and (u',v') differ only by a scalar (=1 in F_2).
    So there are exactly 511*511 = 261121 distinct rank-1 matrices.
    """
    vecs = []
    for i in range(1, 512):  # nonzero F_2^9 vectors
        v = np.array([(i >> b) & 1 for b in range(9)], dtype=np.uint8)
        vecs.append(v)
    
    mats = []
    labels = []
    for ui, u in enumerate(vecs):
        for vi, v in enumerate(vecs):
            M = np.outer(u, v).astype(np.uint8)
            mats.append(M)
            labels.append((ui + 1, vi + 1))  # 1-indexed bitmasks
    return np.array(mats, dtype=np.uint8), labels

def main():
    t0 = time.time()
    T = make_T333_f2()
    T_flat = T.reshape(81, 9)
    
    # T333 slices
    slices = []
    slice_names = []
    for c in range(9):
        M = T_flat[:, c].reshape(9, 9)
        r = rank_f2(M)
        slices.append(M)
        slice_names.append(f"c={c}({c//3},{c%3})")
        print(f"Slice {slice_names[-1]}: rank={r}, weight={int(M.sum())}")
    
    print(f"\nEnumerating rank-1 F2 9x9 matrices...")
    # Instead of full enumeration (261K), sample efficiently
    # For each slice, count rank-reducing corrections
    
    vecs = []
    for i in range(1, 512):
        v = np.array([(i >> b) & 1 for b in range(9)], dtype=np.uint8)
        vecs.append(v)
    n_vecs = len(vecs)
    
    results = {
        'purpose': 'F2 rank-shortening analysis for T333 slices',
        'n_rank1_matrices': n_vecs * n_vecs,
        'slice_analysis': [],
    }
    
    # For each slice, count: how many rank-1 matrices reduce rank by ≥1?
    print(f"\nAnalyzing rank-reducing corrections per slice...")
    
    for c in range(9):
        M_slice = slices[c]
        r_orig = rank_f2(M_slice)
        assert r_orig == 3, f"Slice {c} should have rank 3, got {r_orig}"
        
        n_reduce_by1 = 0  # rank(M ⊕ x) ≤ 2
        n_reduce_to1 = 0  # rank(M ⊕ x) ≤ 1
        n_increase = 0     # rank(M ⊕ x) > 3
        
        sample_reducers = []  # save a few examples
        
        for ui in range(n_vecs):
            u = vecs[ui]
            for vi in range(n_vecs):
                v = vecs[vi]
                x = np.outer(u, v).astype(np.uint8)
                M_new = (M_slice ^ x)  # XOR = addition in F_2
                r_new = rank_f2(M_new)
                if r_new <= 2:
                    n_reduce_by1 += 1
                    if r_new <= 1:
                        n_reduce_to1 += 1
                    if len(sample_reducers) < 5:
                        sample_reducers.append({
                            'u_mask': int(ui + 1), 'v_mask': int(vi + 1),
                            'new_rank': int(r_new),
                            'u_wt': int(u.sum()), 'v_wt': int(v.sum()),
                        })
                elif r_new > r_orig:
                    n_increase += 1
        
        rec = {
            'slice': c, 'name': slice_names[c],
            'original_rank': int(r_orig),
            'n_reduce_to_rank2': n_reduce_by1,
            'n_reduce_to_rank1': n_reduce_to1,
            'n_increase_rank': n_increase,
            'fraction_reduce': n_reduce_by1 / (n_vecs * n_vecs),
            'sample_reducers': sample_reducers,
        }
        results['slice_analysis'].append(rec)
        print(f"  Slice {c} ({c//3},{c%3}): reduce_to_2={n_reduce_by1}, "
              f"reduce_to_1={n_reduce_to1}, increase={n_increase}")
    
    # Check if any single rank-1 matrix reduces ALL 9 slices by ≥1
    print(f"\nChecking universal rank-reducers...")
    n_universal = 0
    for ui in range(n_vecs):
        u = vecs[ui]
        for vi in range(n_vecs):
            v = vecs[vi]
            x = np.outer(u, v).astype(np.uint8)
            all_reduce = True
            for c in range(9):
                M_new = (slices[c] ^ x)
                if rank_f2(M_new) > 2:
                    all_reduce = False; break
            if all_reduce:
                n_universal += 1
                if n_universal <= 3:
                    print(f"  Universal reducer: u={ui+1:03x}, v={vi+1:03x}, "
                          f"wt(u)={u.sum()}, wt(v)={v.sum()}")
    
    results['n_universal_rank_reducers'] = n_universal
    print(f"  Total universal rank-reducers: {n_universal} / {n_vecs*n_vecs}")
    
    elapsed = time.time() - t0
    results['elapsed_sec'] = round(elapsed, 2)
    
    out_dir = Path(__file__).resolve().parent.parent / 'data/f2_analysis'
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / 'f2_rank_shortening.json'
    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nElapsed: {elapsed:.1f}s")
    print(f"Saved to {out_path}")

if __name__ == '__main__':
    main()
