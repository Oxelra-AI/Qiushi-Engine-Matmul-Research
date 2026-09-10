#!/usr/bin/env python3
"""analysis: Targeted single-B-modification search for defect-1 deletions.

For each defect-1 deletion from rank-23:
  - K = [a_1⊗b_1 | ... | a_22⊗b_22] has rank covering 8 of 9 D-columns
  - One D-column d_γ is NOT in col(K)
  - Search: modify one B_t to B_t ⊕ δ so that a_t⊗δ covers the missing direction
  
For term t, replacing B_t → B_t ⊕ δ changes K_t to a_t⊗(b_t⊕δ).
The new column space adds a_t⊗δ to old col(K).
We need d_γ ∈ span{col(K) ∪ {a_t⊗δ}} for some δ ∈ F₂⁹.

Equivalent: d_γ + a_t⊗δ ∈ col(K), i.e., project d_γ-a_t⊗δ onto the quotient 
F₂^81/col(K) and check if it's zero.

Over all 22 terms × 512 deltas: fast exhaustive search.
When found, solve for C linearly and verify all 729 Brent equations.
"""
from __future__ import annotations
import json, time, sys, argparse, itertools
from pathlib import Path
import numpy as np

# Reuse from linear_completion
sys.path.insert(0, str(Path(__file__).resolve().parent))
from linear_completion import (
    build_t333_f2, tensor_to_D, parse_qmm_scheme_f2, verify_decomposition_f2,
    mask_to_vec, vec_to_mask, build_K_matrix, gf2_column_rank,
    gf2_in_column_space, gf2_solve_multi, gf2_rref
)

def find_missing_col(K, D):
    """Return the index of the first D-column not in col(K), or None."""
    for c in range(D.shape[1]):
        if not gf2_in_column_space(K, D[:, c]):
            return c
    return None

def gf2_quotient_basis(K):
    """Compute a basis for the quotient F₂^81 / col(K).
    Returns (Q, pivots) where Q is the complement projection matrix."""
    # Row-reduce K^T to find pivot rows = basis of col(K)
    KT = K.T.copy()
    m, n = KT.shape  # m = #columns of K, n = 81
    _, pivot_rows, rank = gf2_rref(KT)
    # The non-pivot rows of F₂^81 give a quotient projection
    all_rows = set(range(n))
    non_pivot = sorted(all_rows - set(pivot_rows))
    return non_pivot, rank

def single_b_modification_search(A22, B22, K, D, missing_col):
    """Search over all terms t and deltas δ ∈ F₂⁹ for a single B modification
    that covers the missing D-column."""
    d = D[:, missing_col].copy()  # The missing direction (81-vector)
    
    results = []
    for t in range(len(A22)):
        a_t = mask_to_vec(A22[t])
        if A22[t] == 0:
            continue
        for delta_mask in range(1, 512):  # delta ≠ 0
            delta = mask_to_vec(delta_mask)
            # a_t ⊗ delta
            shift = np.outer(a_t, delta).ravel().astype(np.uint8)
            # Check if d + shift ∈ col(K)
            target = (d + shift) % 2
            if gf2_in_column_space(K, target):
                new_B = list(B22)
                new_B[t] = B22[t] ^ delta_mask
                results.append({
                    'term_modified': t,
                    'delta_mask': delta_mask,
                    'old_B': B22[t],
                    'new_B': B22[t] ^ delta_mask,
                    'A_mask': A22[t],
                })
    return results

def multi_b_modification_search(A22, B22, K, D, missing_col, max_terms=2):
    """Search over pairs of B modifications."""
    d = D[:, missing_col].copy()
    r = len(A22)
    results = []
    
    # First try single modifications (already done above but also collected here)
    for t in range(r):
        if A22[t] == 0: continue
        a_t = mask_to_vec(A22[t])
        for dm in range(1, 512):
            delta = mask_to_vec(dm)
            shift = np.outer(a_t, delta).ravel().astype(np.uint8)
            target = (d + shift) % 2
            if gf2_in_column_space(K, target):
                results.append({'terms': [(t, dm)], 'type': 'single'})
    
    if results or max_terms < 2:
        return results
    
    # Try pairs: modify terms t1, t2 with deltas d1, d2
    # a_{t1}⊗d1 + a_{t2}⊗d2 must cover the missing direction
    # This is 22*22*512*512/2 ≈ 29M, too many for brute force
    # Instead, use the quotient: project everything to F₂^81/col(K)
    # The quotient has dimension 81 - rank(K)
    
    # First compute the quotient projection of d
    non_pivots, rank = gf2_quotient_basis(K)
    codim = len(non_pivots)
    print(f"  Codimension of col(K): {codim}")
    
    if codim == 0:
        return results  # No defect, shouldn't happen
    
    # Project d onto quotient coordinates
    # Use the non-pivot coordinates directly
    d_proj = d[non_pivots]
    
    # For each term, precompute all quotient projections of a_t⊗δ
    term_projections = {}  # (t, dm) -> quotient vector
    for t in range(r):
        if A22[t] == 0: continue
        a_t = mask_to_vec(A22[t])
        for dm in range(1, 512):
            delta = mask_to_vec(dm)
            shift = np.outer(a_t, delta).ravel().astype(np.uint8)
            proj = shift[non_pivots]
            key = tuple(int(x) for x in proj)
            if key not in term_projections:
                term_projections[key] = []
            term_projections[key].append((t, dm))
    
    # For pairs: need proj(a_{t1}⊗d1) + proj(a_{t2}⊗d2) = d_proj
    # Group by quotient projection, find complementary pairs
    d_proj_key = tuple(int(x) for x in d_proj)
    
    for key1, sources1 in term_projections.items():
        # Need key2 = d_proj - key1
        key2 = tuple((d_proj_key[i] - key1[i]) % 2 for i in range(codim))
        if key2 in term_projections:
            for s1 in sources1[:3]:  # Limit output
                for s2 in term_projections[key2][:3]:
                    if s1[0] != s2[0]:  # Different terms
                        results.append({'terms': [s1, s2], 'type': 'pair'})
                        if len(results) > 100:
                            return results
    
    return results


def complete_and_verify(A22, B22_modified, D):
    """Given modified B, build K, solve for C, verify."""
    K = build_K_matrix(A22, B22_modified)
    rank = gf2_column_rank(K)
    defect, missing = gf2_in_column_space_all(K, D)
    if defect > 0:
        return None, defect
    CT = gf2_solve_multi(K, D)
    if CT is None:
        return None, -1
    C22 = [vec_to_mask(CT[t]) for t in range(len(A22))]
    diff = verify_decomposition_f2(A22, B22_modified, C22)
    return C22, diff

def gf2_in_column_space_all(K, D):
    """Check all D-columns. Returns (defect, missing_list)."""
    missing = []
    for c in range(D.shape[1]):
        if not gf2_in_column_space(K, D[:, c]):
            missing.append(c)
    return len(missing), missing


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--scheme', type=Path, required=True)
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--max-modify', type=int, default=2, help='Max terms to modify')
    args = ap.parse_args()
    
    t0 = time.time()
    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)
    
    A23, B23, C23 = parse_qmm_scheme_f2(args.scheme)
    T = build_t333_f2()
    D = tensor_to_D(T)
    
    all_results = []
    
    for del_term in range(23):
        A22 = [A23[t] for t in range(23) if t != del_term]
        B22 = [B23[t] for t in range(23) if t != del_term]
        K = build_K_matrix(A22, B22)
        rank_K = gf2_column_rank(K)
        missing_col = find_missing_col(K, D)
        
        if missing_col is None:
            defect = 0
        else:
            # Count total defect
            defect, missing_cols = gf2_in_column_space_all(K, D)
        
        if defect != 1:
            all_results.append({
                'deleted_term': del_term,
                'defect': defect,
                'rank_K': rank_K,
                'single_mods': 0,
                'found_completion': False,
            })
            continue
        
        print(f"\n=== Deletion {del_term}: defect=1, missing D-col={missing_col}, rank(K)={rank_K} ===")
        
        # Single-modification search
        mods = single_b_modification_search(A22, B22, K, D, missing_col)
        print(f"  Single B-modifications found: {len(mods)}")
        
        completions = []
        for m in mods[:20]:  # Test first 20
            B_new = list(B22)
            B_new[m['term_modified']] = m['new_B']
            C22, diff = complete_and_verify(A22, B_new, D)
            if diff == 0:
                completions.append({
                    'term_modified': m['term_modified'],
                    'delta_mask': m['delta_mask'],
                    'old_B': m['old_B'],
                    'new_B': m['new_B'],
                    'A22': A22,
                    'B22': B_new,
                    'C22': C22,
                    'brent_diff': diff,
                })
                print(f"  *** RANK-22 DECOMPOSITION FOUND! del={del_term}, mod term={m['term_modified']}, delta={m['delta_mask']}, brent_diff={diff} ***")
        
        if not mods and args.max_modify >= 2:
            print(f"  Trying pair modifications...")
            pair_mods = multi_b_modification_search(A22, B22, K, D, missing_col, max_terms=2)
            print(f"  Pair modifications found: {len(pair_mods)}")
            for pm in pair_mods[:5]:
                B_new = list(B22)
                for t_idx, dm in pm['terms']:
                    B_new[t_idx] = B22[t_idx] ^ dm
                C22, diff = complete_and_verify(A22, B_new, D)
                if diff == 0:
                    completions.append({
                        'terms_modified': pm['terms'],
                        'A22': A22,
                        'B22': B_new,
                        'C22': C22,
                        'brent_diff': diff,
                    })
                    print(f"  *** RANK-22 DECOMPOSITION FOUND via pair! del={del_term}, mods={pm['terms']}, brent_diff={diff} ***")
        
        all_results.append({
            'deleted_term': del_term,
            'defect': defect,
            'rank_K': rank_K,
            'missing_D_col': missing_col,
            'single_mods': len(mods),
            'completions_found': len(completions),
            'found_completion': len(completions) > 0,
            'first_completion': completions[0] if completions else None,
        })
    
    # Summary
    found_any = any(r.get('found_completion', False) for r in all_results)
    summary = {
        'schema': 'targeted_b_search_v1',
        'rank23_terms': 23,
        'total_deletions': 23,
        'defect1_count': sum(1 for r in all_results if r.get('defect') == 1),
        'found_rank22': found_any,
        'deletion_results': all_results,
        'elapsed_sec': time.time() - t0,
    }
    
    opath = outdir / 'targeted_b_search.json'
    opath.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved: {opath}")
    print(f"Found rank-22: {found_any}")
    print(f"Elapsed: {time.time()-t0:.2f}s")

if __name__ == '__main__':
    main()
