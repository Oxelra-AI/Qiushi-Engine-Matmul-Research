#!/usr/bin/env python3
"""Enhanced trace filter with nullspace conditions for full T<3,3,3>.

For tight rank-r contraction M_lambda with rank r < 9:
  - LEFT null vectors n: n^T X_t = 0 for active terms t (9 eqs per pair)
  - RIGHT null vectors m: X_t m = 0 for active terms t (9 eqs per pair)

This is strictly stronger than the basic trace filter (which only uses
tr(G X_t) = 1).  For rank-3 contractions it adds ~324 equations per
contraction; for rank-6 contractions ~324 per contraction.
"""
from __future__ import annotations
import argparse, json, os, sys, time
from collections import Counter
from pathlib import Path
from typing import List, Sequence
import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from pivot_fixed_full_wang import parse_multiset_arg
from quotient_tight_trace_filter import mat_rank, generalized_inverse, row_to_int, consistent


def build_t333():
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T


def gf2_nullspace(M):
    """Compute GF(2) null space of M (rows that annihilate M^T).
    Returns list of 9-bit integers representing null vectors."""
    M = M.copy().astype(np.uint8) % 2
    rows, cols = M.shape
    # Augment with identity to track row operations
    aug = np.zeros((rows, rows + cols), dtype=np.uint8)
    aug[:, :cols] = M
    for i in range(rows):
        aug[i, cols + i] = 1
    
    # Row reduce
    rank = 0
    for c in range(cols):
        pivot = None
        for r in range(rank, rows):
            if aug[r, c]:
                pivot = r; break
        if pivot is None: continue
        if pivot != rank:
            aug[[rank, pivot]] = aug[[pivot, rank]]
        for r in range(rows):
            if r != rank and aug[r, c]:
                aug[r] ^= aug[rank]
        rank += 1
    
    # Null space: rows with zero leading part
    null_vecs = []
    for r in range(rank, rows):
        if np.any(aug[r, :cols]):
            continue  # shouldn't happen after proper reduction
        v = aug[r, cols:]
        if np.any(v):
            null_vecs.append(v)
    return null_vecs, rank


def lambda_matrix(T, lam):
    M = np.zeros((9,9), dtype=np.uint8)
    for s in range(9):
        if (int(lam) >> s) & 1:
            M ^= T[s]
    return M


def build_tensor_rows(T, support):
    nvars = 81 * len(support)
    rows, rhs = [], []
    for s in range(9):
        active = [t for t, a in enumerate(support) if (int(a) >> s) & 1]
        for b in range(9):
            for c in range(9):
                x = 0
                for t in active:
                    x |= 1 << (81*t + 9*b + c)
                rows.append(x)
                rhs.append(int(T[s,b,c]))
    return rows, rhs


def build_trace_rows(support, T, tight_data, nvars):
    """Build trace equations tr(G X_t) = 1 for tight contractions.
    
    tr(GX) = sum_{i,j} G[i,j] X[j,i].  Variable X_t[row,col] is at
    position 81*t + 9*row + col.  So the coefficient of X_t[b,c] is G[c,b].
    """
    rows, rhs = [], []
    for rec in tight_data:
        G = rec['G']
        for t in rec['active_terms']:
            x = 0
            for b in range(9):
                for c in range(9):
                    if G[c, b] & 1:  # transposed: tr(GX) uses G[col,row]
                        x |= 1 << (81*t + 9*b + c)
            rows.append(x)
            rhs.append(1)
    return rows, rhs


def build_nullspace_rows(support, T, tight_data, nvars):
    """Build nullspace equations for tight contractions with rank < 9."""
    rows, rhs = [], []
    for rec in tight_data:
        M = rec['M']
        rank = rec['rank']
        if rank >= 9:
            continue  # Full rank, no null space
        
        # LEFT null space of M: n^T M = 0 → n^T X_t = 0 for active t
        # gf2_nullspace(M) returns left null vectors: c s.t. c^T M = 0
        left_null, _ = gf2_nullspace(M)
        
        for n_vec in left_null:
            for t in rec['active_terms']:
                for c in range(9):
                    x = 0
                    for b in range(9):
                        if n_vec[b] & 1:
                            x |= 1 << (81*t + 9*b + c)
                    if x:  # Only add non-trivial equation
                        rows.append(x)
                        rhs.append(0)
        
        # RIGHT null space of M: M m = 0 → X_t m = 0 for active t
        # gf2_nullspace(M.T) returns left null of M^T = right null of M
        right_null, _ = gf2_nullspace(M.T)
        
        for m_vec in right_null:
            for t in rec['active_terms']:
                for b in range(9):
                    x = 0
                    for c in range(9):
                        if m_vec[c] & 1:
                            x |= 1 << (81*t + 9*b + c)
                    if x:
                        rows.append(x)
                        rhs.append(0)
    
    return rows, rhs


def analyze_enhanced(support: List[int]) -> dict:
    t0 = time.time()
    T = build_t333()
    nvars = 81 * len(support)
    
    # Tensor equations
    base_rows, base_rhs = build_tensor_rows(T, support)
    base_ok, base_rank, base_aug = consistent(base_rows, base_rhs, nvars)
    
    # Find tight contractions
    tight_data = []
    for lam in range(1, 512):
        active = [t for t, a in enumerate(support) if ((int(lam) & int(a)).bit_count() & 1)]
        M = lambda_matrix(T, lam)
        rank = mat_rank(M)
        if len(active) == rank and rank > 0:
            G, r2, _P, _Q, _D = generalized_inverse(M)
            tight_data.append({
                'lambda': lam, 'rank': rank, 'active_terms': active, 
                'G': G, 'M': M
            })
    
    # Basic trace equations
    trace_rows, trace_rhs = build_trace_rows(support, T, tight_data, nvars)
    basic_rows = base_rows + trace_rows
    basic_rhs = base_rhs + trace_rhs
    basic_ok, basic_rank, basic_aug = consistent(basic_rows, basic_rhs, nvars)
    
    # Enhanced: add nullspace equations
    null_rows, null_rhs = build_nullspace_rows(support, T, tight_data, nvars)
    enhanced_rows = basic_rows + null_rows
    enhanced_rhs = basic_rhs + null_rhs
    enhanced_ok, enhanced_rank, enhanced_aug = consistent(enhanced_rows, enhanced_rhs, nvars)
    
    rank_hist = Counter(int(rec['rank']) for rec in tight_data)
    
    # Count null equations by contraction rank
    null_by_rank = Counter()
    for rec in tight_data:
        if rec['rank'] < 9:
            M = rec['M']
            left_null, _ = gf2_nullspace(M.T)
            right_null, _ = gf2_nullspace(M)
            n_active = len(rec['active_terms'])
            null_by_rank[rec['rank']] += (len(left_null) + len(right_null)) * n_active * 9
    
    result = {
        'schema': 'enhanced_trace_filter_v1',
        'support': [int(a) for a in support],
        'support_size': len(support),
        'variables': nvars,
        'tensor_equations': len(base_rows),
        'tensor_consistent': base_ok,
        'tensor_rank_aug': [base_rank, base_aug],
        'tight_count': len(tight_data),
        'tight_rank_hist': dict(sorted((int(k),int(v)) for k,v in rank_hist.items())),
        'trace_equations': len(trace_rows),
        'basic_total_equations': len(basic_rows),
        'basic_consistent': basic_ok,
        'basic_rank_aug': [basic_rank, basic_aug],
        'nullspace_equations': len(null_rows),
        'null_equations_by_contraction_rank': dict(sorted((int(k),int(v)) for k,v in null_by_rank.items())),
        'enhanced_total_equations': len(enhanced_rows),
        'enhanced_consistent': enhanced_ok,
        'enhanced_rank_aug': [enhanced_rank, enhanced_aug],
        'elapsed_sec': time.time() - t0,
    }
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--multiset', required=True)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    
    support = parse_multiset_arg(args.multiset)
    result = analyze_enhanced(support)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    
    print(json.dumps({k: v for k, v in result.items() 
                      if k not in ('support',)}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
