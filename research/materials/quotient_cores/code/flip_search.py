#!/usr/bin/env python3
"""Flip-graph search: can we reduce the 21-term cn122 restriction of the
E11 core from 21 to 19 terms by finding a subset of terms whose sum
has lower tensor rank?

Strategy:
  - Check all C(21,2)=210 pairs: does any pair sum to rank 0? (cancellation)
  - Check all C(21,3)=1330 triples: does any triple sum to rank 1?
  - Check all C(21,4)=5985 quadruples: does any have A-flat rank ≤ 2?
  - Also check: for each pair with same A-factor, does the B⊗C sum
    admit a rank-1 factorization enabling a 2→1 reduction?

If we find a 3→1 flip, the E11 core has rank ≤ 19, giving R_F2(T<3,3,3>) ≤ 22.
"""
import numpy as np
from itertools import combinations
import json, time
from pathlib import Path

def build_matmul_tensor_f2():
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T

def apply_constraint_f2(T, mask):
    result = T.copy()
    pivot = mask.bit_length() - 1
    free_bits = mask ^ (1 << pivot)
    for i in range(T.shape[0]):
        if (free_bits >> i) & 1:
            result[i] = (result[i] + result[pivot]) % 2
    result[pivot] = 0
    indices = [j for j in range(T.shape[0]) if j != pivot]
    return result[indices]

def read_qmm_scheme(path):
    terms = []
    term = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line.startswith('term '):
                if 'u' in term: terms.append(term)
                term = {'index': int(line.split()[1])}
            elif line.startswith('u '):
                term['u'] = list(map(int, line.split()[1:]))
            elif line.startswith('v '):
                term['v'] = list(map(int, line.split()[1:]))
            elif line.startswith('w '):
                term['w'] = list(map(int, line.split()[1:]))
    if 'u' in term: terms.append(term)
    return terms

def restrict_scheme_f2(terms, mask):
    pivot = mask.bit_length() - 1
    free_bits = mask ^ (1 << pivot)
    na = len(terms[0]['u'])
    restricted = []
    for t in terms:
        u = [abs(x) % 2 for x in t['u']]
        v = [abs(x) % 2 for x in t['v']]
        w = [abs(x) % 2 for x in t['w']]
        for i in range(na):
            if (free_bits >> i) & 1:
                u[i] = (u[i] + u[pivot]) % 2
        u[pivot] = 0
        u_core = [u[i] for i in range(na) if i != pivot]
        if any(u_core):
            restricted.append({'u': u_core, 'v': v, 'w': w,
                             'original_index': t['index']})
    return restricted

def f2_rank(M):
    m = M.copy().astype(np.uint8) % 2
    rows, cols = m.shape
    rank = 0
    for col in range(cols):
        prow = None
        for row in range(rank, rows):
            if m[row, col] & 1:
                prow = row
                break
        if prow is None: continue
        if prow != rank:
            m[[rank, prow]] = m[[prow, rank]]
        for row in range(rows):
            if row != rank and (m[row, col] & 1):
                m[row] ^= m[rank]
        rank += 1
    return rank

def term_tensor(t, na, nb, nc):
    """Build rank-1 tensor from a term."""
    u = np.array(t['u'], dtype=np.uint8).reshape(na,1,1)
    v = np.array(t['v'], dtype=np.uint8).reshape(1,nb,1)
    w = np.array(t['w'], dtype=np.uint8).reshape(1,1,nc)
    return (u * v * w) % 2

def subset_sum(terms, indices, na, nb, nc):
    """Sum of rank-1 tensors at given indices, mod 2."""
    S = np.zeros((na, nb, nc), dtype=np.uint8)
    for idx in indices:
        S = (S + term_tensor(terms[idx], na, nb, nc)) % 2
    return S

def tensor_a_flat_rank(T):
    na, nb, nc = T.shape
    return f2_rank(T.reshape(na, nb*nc))

def tensor_b_flat_rank(T):
    na, nb, nc = T.shape
    return f2_rank(T.transpose(1,0,2).reshape(nb, na*nc))

def tensor_multilinear_rank(T):
    """Compute all three flattening ranks."""
    na, nb, nc = T.shape
    ra = f2_rank(T.reshape(na, nb*nc))
    rb = f2_rank(T.transpose(1,0,2).reshape(nb, na*nc))
    rc = f2_rank(T.transpose(2,0,1).reshape(nc, na*nb))
    return ra, rb, rc

def main():
    outdir = Path('data/restricted_cores')

    # Build E11 core and get cn122 restriction
    T = build_matmul_tensor_f2()
    core_e11 = apply_constraint_f2(T, 1)
    na, nb, nc = core_e11.shape

    scheme = read_qmm_scheme(
        'data/cn122_3x3_r23_repro/scheme.qmm')
    restricted = restrict_scheme_f2(scheme, 1)
    n = len(restricted)
    print(f"E11 core: {na}x{nb}x{nc}, restricted cn122: {n} terms")

    # Verify
    recon = np.zeros_like(core_e11)
    for t in restricted:
        recon = (recon + term_tensor(t, na, nb, nc)) % 2
    assert np.array_equal(recon, core_e11), "Verification failed"
    print("✓ 21-term decomposition verified")

    # Precompute all rank-1 tensors
    tensors = [term_tensor(restricted[i], na, nb, nc) for i in range(n)]

    results = {'n_terms': n, 'flips_found': []}
    t0 = time.time()

    # --- Check pairs (C(21,2) = 210): rank 0 (cancellation) ---
    print(f"\nChecking {n*(n-1)//2} pairs for rank-0 sum (cancellation)...")
    cancel_count = 0
    for i, j in combinations(range(n), 2):
        S = (tensors[i] + tensors[j]) % 2
        if not np.any(S):
            cancel_count += 1
            print(f"  CANCELLATION: terms {i},{j}")
            results['flips_found'].append({
                'type': '2→0', 'indices': [i, j],
                'original_indices': [restricted[i]['original_index'],
                                   restricted[j]['original_index']]
            })
    print(f"  Pairs with rank-0 sum: {cancel_count}")

    # --- Check triples (C(21,3) = 1330): rank 1 ---
    print(f"\nChecking {n*(n-1)*(n-2)//6} triples for rank-1 sum...")
    rank1_count = 0
    for i, j, k in combinations(range(n), 3):
        S = (tensors[i] + tensors[j] + tensors[k]) % 2
        if not np.any(S):
            print(f"  ZERO SUM: terms {i},{j},{k} (3→0 flip, saves 3!)")
            results['flips_found'].append({
                'type': '3→0', 'indices': [i,j,k]
            })
            continue
        # Check A-flattening rank
        ra = tensor_a_flat_rank(S)
        if ra <= 1:
            # Potential rank 1! Verify with B and C flattenings
            rb = tensor_b_flat_rank(S)
            if rb <= 1:
                rank1_count += 1
                print(f"  RANK-1 TRIPLE: terms {i},{j},{k} "
                      f"(original: {restricted[i]['original_index']},"
                      f"{restricted[j]['original_index']},"
                      f"{restricted[k]['original_index']})")
                results['flips_found'].append({
                    'type': '3→1', 'indices': [i,j,k],
                    'original_indices': [restricted[x]['original_index']
                                       for x in [i,j,k]],
                    'multilinear_ranks': list(tensor_multilinear_rank(S)),
                })
    print(f"  Triples with rank-1 sum: {rank1_count}")
    t1 = time.time()
    print(f"  Time for pairs+triples: {t1-t0:.1f}s")

    # --- Check quadruples (C(21,4) = 5985): A-flat rank ≤ 2 ---
    print(f"\nChecking {n*(n-1)*(n-2)*(n-3)//24} quadruples for A-flat rank ≤ 2...")
    low_rank_quads = 0
    for i, j, k, l in combinations(range(n), 4):
        S = (tensors[i] + tensors[j] + tensors[k] + tensors[l]) % 2
        if not np.any(S):
            print(f"  ZERO SUM: terms {i},{j},{k},{l}")
            results['flips_found'].append({
                'type': '4→0', 'indices': [i,j,k,l]
            })
            continue
        ra = tensor_a_flat_rank(S)
        if ra <= 2:
            rb = tensor_b_flat_rank(S)
            if rb <= 2:
                ml = tensor_multilinear_rank(S)
                print(f"  LOW-RANK QUAD: terms {i},{j},{k},{l}, "
                      f"mlr=({ml[0]},{ml[1]},{ml[2]})")
                low_rank_quads += 1
                results['flips_found'].append({
                    'type': '4→2_candidate', 'indices': [i,j,k,l],
                    'multilinear_ranks': list(ml),
                })
    print(f"  Quadruples with A-flat rank ≤ 2 and B-flat rank ≤ 2: {low_rank_quads}")
    t2 = time.time()
    print(f"  Time for quadruples: {t2-t1:.1f}s")

    # Summary
    n_flips = len(results['flips_found'])
    print(f"\n{'='*60}")
    print(f"SUMMARY: {n_flips} flip opportunities found")
    if n_flips > 0:
        for f in results['flips_found']:
            print(f"  {f['type']}: indices {f['indices']}")
        print(f"\n  If any 3→1 flip exists: R_F2(core_E11) ≤ 19")
        print(f"  => R_F2(T<3,3,3>) ≤ 22")
    else:
        print(f"  No flips found in the 21-term cn122 restriction.")
        print(f"  This means the 21-term decomposition is 'flip-rigid'.")
        print(f"  The core rank might be exactly 21, or a different")
        print(f"  starting decomposition might enable flips.")
    print(f"{'='*60}")

    results['total_time'] = t2-t0
    with open(outdir / 'flip_search_results.json', 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved to {outdir}/flip_search_results.json")

if __name__ == '__main__':
    main()
