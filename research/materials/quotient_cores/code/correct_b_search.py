#!/usr/bin/env python3
"""analysis: Correct single-B modification search with full K-rebuild verification.

The previous search had a bug: checking d + a_t⊗δ ∈ col(K_old) doesn't account
for the fact that modifying column t changes the column space. The correct check:
build K_new = K with column t replaced by a_t⊗(b_t⊕δ), then verify ALL 9 D-columns
are in col(K_new).

This script also implements a broader approach: for each deletion, search over all
possible single-B modifications and verify completions.
"""
from __future__ import annotations
import json, time, sys, argparse
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from linear_completion import (
    build_t333_f2, tensor_to_D, parse_qmm_scheme_f2, verify_decomposition_f2,
    mask_to_vec, vec_to_mask, gf2_rref, gf2_solve_multi
)


def build_K_column(a_mask, b_mask):
    """Build a_t ⊗ b_t as 81-vector over F2."""
    a = np.array([(a_mask >> i) & 1 for i in range(9)], dtype=np.uint8)
    b = np.array([(b_mask >> i) & 1 for i in range(9)], dtype=np.uint8)
    return np.outer(a, b).ravel()


def gf2_column_space_contains_D(K, D):
    """Check whether all columns of D are in col(K) over F2.
    Returns (True/False, rank_K, defect_count)."""
    r = K.shape[1]
    # Augment K with D columns
    K_D = np.hstack([K, D])
    _, _, rank_aug = gf2_rref(K_D.T.copy())
    _, _, rank_K = gf2_rref(K.T.copy())
    defect = rank_aug - rank_K
    return defect == 0, rank_K, defect


def search_single_b_mod(A22, B22, D, report_every=200):
    """For each term t and each delta ∈ F2^9, replace B_t → B_t⊕δ,
    rebuild K, check if col(K_new) ⊃ col(D)."""
    r = len(A22)
    
    # Precompute base K columns
    base_cols = []
    for t in range(r):
        base_cols.append(build_K_column(A22[t], B22[t]))
    K_base = np.column_stack(base_cols)
    
    found = []
    checked = 0
    
    for t in range(r):
        if A22[t] == 0:
            continue
        for delta in range(1, 512):  # Skip delta=0 (no change)
            new_b = B22[t] ^ delta
            # Build new K with column t replaced
            new_col = build_K_column(A22[t], new_b)
            K_new = K_base.copy()
            K_new[:, t] = new_col
            
            ok, rank_K, defect = gf2_column_space_contains_D(K_new, D)
            checked += 1
            
            if ok:
                found.append({
                    'term': t,
                    'delta': delta,
                    'old_B': B22[t],
                    'new_B': new_b,
                    'rank_K': rank_K,
                })
            
            if checked % report_every == 0:
                print(f"  checked {checked}, found {len(found)}", flush=True)
    
    return found, checked


def complete_from_K(K, D, A22, B22_new):
    """Given K with col(K) ⊃ col(D), solve for C and verify."""
    CT = gf2_solve_multi(K, D)
    if CT is None:
        return None, -1
    C22 = [vec_to_mask(CT[t]) for t in range(len(A22))]
    diff = verify_decomposition_f2(A22, B22_new, C22)
    return C22, diff


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--scheme', type=Path, required=True)
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--deletions', type=str, default='defect1',
                    help='Comma-separated term indices, or "defect1" for auto-detect')
    args = ap.parse_args()
    
    t0 = time.time()
    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)
    
    A23, B23, C23 = parse_qmm_scheme_f2(args.scheme)
    T = build_t333_f2()
    D = tensor_to_D(T)
    
    # Identify defect-1 deletions
    defect1_terms = []
    if args.deletions == 'defect1':
        for del_t in range(23):
            A22 = [A23[t] for t in range(23) if t != del_t]
            B22 = [B23[t] for t in range(23) if t != del_t]
            K = np.column_stack([build_K_column(A22[i], B22[i]) for i in range(22)])
            ok, _, defect = gf2_column_space_contains_D(K, D)
            if defect == 1:
                defect1_terms.append(del_t)
        print(f"Defect-1 deletions: {defect1_terms}")
    else:
        defect1_terms = [int(x) for x in args.deletions.split(',')]
    
    all_completions = []
    
    for del_t in defect1_terms:
        A22 = [A23[t] for t in range(23) if t != del_t]
        B22 = [B23[t] for t in range(23) if t != del_t]
        
        print(f"\n=== Deletion {del_t}: searching single-B modifications ===")
        t1 = time.time()
        
        found, checked = search_single_b_mod(A22, B22, D)
        
        print(f"  Checked: {checked}, covering modifications found: {len(found)}")
        print(f"  Time: {time.time()-t1:.2f}s")
        
        # For each covering modification, complete and verify
        for m in found:
            B_new = list(B22)
            B_new[m['term']] = m['new_B']
            K_new = np.column_stack([build_K_column(A22[i], B_new[i]) for i in range(22)])
            C22, diff = complete_from_K(K_new, D, A22, B_new)
            
            if diff == 0:
                print(f"  *** VERIFIED RANK-22 DECOMPOSITION! del={del_t}, mod term={m['term']}, "
                      f"delta={m['delta']}, brent_diff=0 ***")
                
                # Save the decomposition
                decomp = {
                    'schema': 'rank22_decomposition_f2_v1',
                    'rank': 22,
                    'field': 'F2',
                    'dimensions': [3,3,3],
                    'A_masks': A22,
                    'B_masks': B_new,
                    'C_masks': C22,
                    'brent_verification': diff,
                    'construction': {
                        'method': 'deletion_single_B_modification',
                        'deleted_rank23_term': del_t,
                        'modified_term_in_22': m['term'],
                        'delta_B': m['delta'],
                        'original_B': m['old_B'],
                        'new_B': m['new_B'],
                    },
                }
                dpath = outdir / f'rank22_del{del_t}_mod{m["term"]}_d{m["delta"]}.json'
                dpath.write_text(json.dumps(decomp, indent=2, sort_keys=True) + '\n')
                all_completions.append(decomp)
            else:
                m['brent_diff'] = diff
                m['C_solved'] = C22 is not None
        
        # If no single-B works, report
        if not any(True for m in found if m.get('brent_diff', -1) == 0 or 
                   (m not in [c.get('construction', {}) for c in all_completions])):
            verified = [m for m in found if 'brent_diff' in m and m['brent_diff'] == 0]
            failed = [m for m in found if 'brent_diff' in m and m['brent_diff'] > 0]
            if failed:
                print(f"  Note: {len(found)} mods cover D, but {len(failed)} failed Brent verification")
                print(f"  Brent diffs: {[m['brent_diff'] for m in failed[:10]]}")
    
    summary = {
        'schema': 'correct_b_search_v1',
        'defect1_deletions': defect1_terms,
        'total_completions': len(all_completions),
        'found_rank22': len(all_completions) > 0,
        'elapsed_sec': time.time() - t0,
    }
    
    opath = outdir / 'correct_b_search_summary.json'
    opath.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved: {opath}")
    print(f"Total verified rank-22 decompositions: {len(all_completions)}")

if __name__ == '__main__':
    main()
