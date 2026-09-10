#!/usr/bin/env python3
"""analysis: Linear B-search with exact C-completion for rank-22 over F2.

Mathematical foundation:
  For fixed A-masks a_t and proposed B-masks b_t, form 
    K = [a_1⊗b_1 | ... | a_r⊗b_r]   (81 × r matrix over F2)
    D = flattening of T_{333}          (81 × 9 target)
  C exists iff every column of D lies in col(K).
  If so, C is obtained by solving K @ C^T = D (linear over F2).

This script:
  1. Loads the verified rank-23 scheme, reduces to F2
  2. For each of the 23 deletions, computes K and defect
  3. Searches for targeted B modifications to cover the residual
  4. If defect = 0, solves for C and verifies all 729 Brent equations
"""
from __future__ import annotations
import json, time, sys, hashlib, argparse
from pathlib import Path
import numpy as np

def build_t333_f2():
    """3x3 matrix multiplication tensor over F2, flattened to 81x9 matrix D.
    D[alpha*9+beta, gamma] = T[alpha,beta,gamma] where T[3i+j, 3j+k, 3i+k]=1."""
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T

def tensor_to_D(T):
    """Flatten T[s,b,c] into D[s*9+b, c] = T[s,b,c]."""
    return T.reshape(81, 9).copy()

def parse_qmm_scheme_f2(path):
    """Parse QMM scheme file, reduce to F2 (mod 2 of absolute values)."""
    text = Path(path).read_text()
    lines = text.strip().split('\n')
    terms = []
    current = {}
    for line in lines:
        line = line.strip()
        if line.startswith('term'):
            if current:
                terms.append(current)
            current = {}
        elif line.startswith('u '):
            vals = [abs(int(x)) % 2 for x in line.split()[1:]]
            current['u'] = vals
        elif line.startswith('v '):
            vals = [abs(int(x)) % 2 for x in line.split()[1:]]
            current['v'] = vals
        elif line.startswith('w '):
            vals = [abs(int(x)) % 2 for x in line.split()[1:]]
            current['w'] = vals
    if current:
        terms.append(current)
    # Convert to 9-bit masks
    A, B, C = [], [], []
    for t in terms:
        amask = sum(t['u'][i] << i for i in range(9))
        bmask = sum(t['v'][i] << i for i in range(9))
        cmask = sum(t['w'][i] << i for i in range(9))
        A.append(amask)
        B.append(bmask)
        C.append(cmask)
    return A, B, C

def verify_decomposition_f2(A, B, C):
    """Check all 729 Brent equations over F2. Returns number of failures."""
    T = build_t333_f2()
    R = np.zeros((9,9,9), dtype=np.uint8)
    for a, b, c in zip(A, B, C):
        for s in range(9):
            if not ((a >> s) & 1): continue
            for i in range(9):
                if not ((b >> i) & 1): continue
                for j in range(9):
                    if (c >> j) & 1:
                        R[s,i,j] ^= 1
    return int(np.sum(R ^ T))

def mask_to_vec(mask, bits=9):
    """Convert a bitmask to a numpy F2 vector."""
    return np.array([(mask >> i) & 1 for i in range(bits)], dtype=np.uint8)

def vec_to_mask(v):
    """Convert F2 vector back to bitmask."""
    return int(sum(int(v[i]) << i for i in range(len(v))))

def build_K_matrix(A, B):
    """Build K = [a_1⊗b_1 | ... | a_r⊗b_r] as 81×r matrix over F2."""
    r = len(A)
    K = np.zeros((81, r), dtype=np.uint8)
    for t in range(r):
        a_vec = mask_to_vec(A[t])
        b_vec = mask_to_vec(B[t])
        col = np.outer(a_vec, b_vec).ravel()  # 81-vector: a⊗b
        K[:, t] = col
    return K

def gf2_rref(M_in):
    """Row-reduce M over F2. Returns (rref, pivot_cols, rank)."""
    M = M_in.copy().astype(np.uint8)
    rows, cols = M.shape
    pivot_cols = []
    r = 0
    for c in range(cols):
        # Find pivot
        found = -1
        for i in range(r, rows):
            if M[i, c]:
                found = i; break
        if found < 0:
            continue
        # Swap
        M[[r, found]] = M[[found, r]]
        # Eliminate
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        pivot_cols.append(c)
        r += 1
    return M, pivot_cols, r

def gf2_column_rank(K):
    """Rank of K over F2 (= column rank = row rank of K^T)."""
    _, _, rank = gf2_rref(K.T.copy())
    return rank

def gf2_in_column_space(K, v):
    """Check if vector v is in the column space of K over F2.
    Augment K with v and check if rank increases."""
    r0 = gf2_column_rank(K)
    K_aug = np.hstack([K, v.reshape(-1, 1)])
    r1 = gf2_column_rank(K_aug)
    return r1 == r0

def gf2_completion_defect(K, D):
    """Count how many columns of D are NOT in col(K). Returns (defect, missing_cols)."""
    missing = []
    for c in range(D.shape[1]):
        if not gf2_in_column_space(K, D[:, c]):
            missing.append(c)
    return len(missing), missing

def gf2_solve(K, d):
    """Solve K @ x = d over F2. Returns x or None if no solution.
    K is m×n, d is m-vector."""
    m, n = K.shape
    # Augment: [K | d]
    Aug = np.zeros((m, n + 1), dtype=np.uint8)
    Aug[:, :n] = K
    Aug[:, n] = d
    _, pivots, rank = gf2_rref(Aug)
    # Check consistency: if pivot in the last column, no solution
    if n in pivots:
        return None
    # Read solution (one particular solution)
    rref = Aug.copy()
    _, _, _ = gf2_rref(rref)
    x = np.zeros(n, dtype=np.uint8)
    rref2, pivots2, _ = gf2_rref(Aug)
    for i, pc in enumerate(pivots2):
        if pc < n:
            x[pc] = rref2[i, n]
    return x

def gf2_solve_multi(K, D):
    """Solve K @ X = D over F2 where D is m×k. Returns X (n×k) or None."""
    n = K.shape[1]
    k = D.shape[1]
    X = np.zeros((n, k), dtype=np.uint8)
    for c in range(k):
        sol = gf2_solve(K, D[:, c])
        if sol is None:
            return None
        X[:, c] = sol
    return X

def deletion_analysis(A23, B23, C23):
    """For each deletion of one term, analyze the K matrix and defect."""
    T = build_t333_f2()
    D = tensor_to_D(T)
    results = []
    for t0 in range(23):
        A22 = [A23[t] for t in range(23) if t != t0]
        B22 = [B23[t] for t in range(23) if t != t0]
        C22 = [C23[t] for t in range(23) if t != t0]
        K = build_K_matrix(A22, B22)
        rank_K = gf2_column_rank(K)
        defect, missing = gf2_completion_defect(K, D)
        
        # Check: if defect = 0, solve for C
        new_C = None
        brent_diff = None
        if defect == 0:
            # K @ C'^T = D, so C'^T = solve(K, D)
            CT = gf2_solve_multi(K, D)
            if CT is not None:
                new_C = [vec_to_mask(CT[t]) for t in range(22)]
                brent_diff = verify_decomposition_f2(A22, B22, new_C)
        
        results.append({
            'deleted_term': t0,
            'deleted_A': A23[t0],
            'deleted_B': B23[t0],
            'deleted_C': C23[t0],
            'rank_K': rank_K,
            'defect': defect,
            'missing_D_cols': missing,
            'C_solved': new_C is not None,
            'brent_diff': brent_diff,
        })
    return results

def residual_direction(A22, B22, D, K):
    """For a defect-1 case, find the single missing direction in F2^81."""
    # The residual is the unique D-column not in col(K)
    # Actually there could be multiple missing columns sharing the same missing direction
    r0 = gf2_column_rank(K)
    missing_dir = None
    for c in range(9):
        if not gf2_in_column_space(K, D[:, c]):
            # Find the component of D[:,c] not in col(K)
            # Project: solve K @ x ≈ D[:,c] in the least-squares sense over F2
            # The residual is D[:,c] - K @ x_partial
            # Actually over F2: the residual mod col(K) is the unique coset representative
            # We can find it by augmenting K with D[:,c] and reading the new pivot row
            K_aug = np.hstack([K, D[:, c:c+1]])
            _, pivots, _ = gf2_rref(K_aug.T.copy())
            # The new pivot is the row that becomes independent
            # Easier: just compute the coset
            if missing_dir is None:
                missing_dir = D[:, c].copy()
            break
    return missing_dir

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--scheme', type=Path, required=True,
                    help='Path to QMM scheme file')
    ap.add_argument('--outdir', type=Path, required=True)
    args = ap.parse_args()
    
    t0 = time.time()
    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)
    
    # 1. Parse and verify rank-23 scheme over F2
    A23, B23, C23 = parse_qmm_scheme_f2(args.scheme)
    diff23 = verify_decomposition_f2(A23, B23, C23)
    print(f"Rank-23 scheme: {len(A23)} terms, F2 verification diff = {diff23}")
    
    if diff23 != 0:
        print("ERROR: rank-23 scheme does not verify over F2!")
        return
    
    # 2. Deletion analysis
    del_results = deletion_analysis(A23, B23, C23)
    
    # Summarize
    defect_hist = {}
    defect0_terms = []
    defect1_terms = []
    for r in del_results:
        d = r['defect']
        defect_hist[d] = defect_hist.get(d, 0) + 1
        if d == 0:
            defect0_terms.append(r['deleted_term'])
        elif d == 1:
            defect1_terms.append(r['deleted_term'])
    
    print(f"\nDeletion defect histogram: {defect_hist}")
    print(f"Defect-0 terms (direct C-completion): {defect0_terms}")
    print(f"Defect-1 terms: {defect1_terms}")
    
    # Check defect-0 completions
    for r in del_results:
        if r['C_solved']:
            print(f"  term {r['deleted_term']}: C solved, brent_diff = {r['brent_diff']}")
    
    out = {
        'schema': 'deletion_linear_completion_v1',
        'scheme_path': str(args.scheme),
        'rank23_terms': 23,
        'f2_verification_diff': diff23,
        'A_masks': A23,
        'B_masks': B23,
        'C_masks': C23,
        'defect_histogram': {str(k): v for k, v in sorted(defect_hist.items())},
        'defect0_deleted_terms': defect0_terms,
        'defect1_deleted_terms': defect1_terms,
        'deletion_details': del_results,
        'elapsed_sec': time.time() - t0,
    }
    
    opath = outdir / 'deletion_linear_completion.json'
    opath.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved: {opath}")
    print(json.dumps({
        'defect_hist': out['defect_histogram'],
        'defect0_count': len(defect0_terms),
        'defect1_count': len(defect1_terms),
        'elapsed_sec': out['elapsed_sec'],
    }, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
