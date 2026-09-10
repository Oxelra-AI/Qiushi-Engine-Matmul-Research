#!/usr/bin/env python3
"""Detailed analysis of restricted decompositions of multiple rank-23
schemes into the three Wang codim-1 cores, with focus on finding
shorter decompositions that might yield R_F2(T) <= 22.
"""
import numpy as np
import json
from pathlib import Path
from collections import Counter

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
    return result, pivot

def extract_core(T_full, pivot):
    indices = [i for i in range(T_full.shape[0]) if i != pivot]
    return T_full[indices], indices

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

def f2_rank(M):
    m = M.copy().astype(np.uint8) % 2
    rows, cols = m.shape
    rank = 0
    for col in range(cols):
        pivot_row = None
        for row in range(rank, rows):
            if m[row, col] & 1:
                pivot_row = row
                break
        if pivot_row is None:
            continue
        if pivot_row != rank:
            m[[rank, pivot_row]] = m[[pivot_row, rank]]
        for row in range(rows):
            if row != rank and (m[row, col] & 1):
                m[row] ^= m[rank]
        rank += 1
    return rank

def restrict_scheme_f2(terms, mask):
    pivot = mask.bit_length() - 1
    free_bits = mask ^ (1 << pivot)
    na = len(terms[0]['u'])
    
    restricted = []
    vanished = []
    for t in terms:
        u = [abs(x) % 2 for x in t['u']]
        v = [abs(x) % 2 for x in t['v']]
        w = [abs(x) % 2 for x in t['w']]
        for i in range(na):
            if (free_bits >> i) & 1:
                u[i] = (u[i] + u[pivot]) % 2
        u[pivot] = 0
        u_core = tuple(u[i] for i in range(na) if i != pivot)
        if any(u_core):
            restricted.append({
                'u': list(u_core), 'v': v, 'w': w,
                'original_index': t['index']
            })
        else:
            vanished.append(t['index'])
    return restricted, vanished

def analyze_restricted_decomp(restricted_terms, core, core_name):
    """Detailed analysis of a restricted decomposition."""
    na, nb, nc = core.shape
    
    # Check correctness
    recon = np.zeros_like(core)
    for t in restricted_terms:
        u = np.array(t['u'], dtype=np.uint8).reshape(na,1,1)
        v = np.array(t['v'], dtype=np.uint8).reshape(1,nb,1)
        w = np.array(t['w'], dtype=np.uint8).reshape(1,1,nc)
        recon = (recon + u*v*w) % 2
    correct = np.array_equal(recon, core)
    
    # A-factor analysis
    a_factors = [tuple(t['u']) for t in restricted_terms]
    a_counter = Counter(a_factors)
    
    # Group terms by A-factor
    groups = {}
    for t in restricted_terms:
        key = tuple(t['u'])
        if key not in groups:
            groups[key] = []
        groups[key].append(t)
    
    # For duplicate A-factors: check if B⊗C matrices cancel
    cancellation_info = []
    for a_key, group in groups.items():
        if len(group) >= 2:
            # Sum of v⊗w matrices
            bc_sum = np.zeros((nb, nc), dtype=np.uint8)
            for t in group:
                v = np.array(t['v'], dtype=np.uint8).reshape(nb,1)
                w = np.array(t['w'], dtype=np.uint8).reshape(1,nc)
                bc_sum = (bc_sum + v*w) % 2
            bc_rank = f2_rank(bc_sum)
            cancellation_info.append({
                'a_factor': list(a_key),
                'a_weight': sum(a_key),
                'count': len(group),
                'bc_sum_rank': bc_rank,
                'original_indices': [t['original_index'] for t in group],
            })
    
    # Term weight statistics
    weights = []
    for t in restricted_terms:
        uw = sum(t['u'])
        vw = sum(t['v'])
        ww = sum(t['w'])
        weights.append({
            'original_index': t['original_index'],
            'u_weight': uw, 'v_weight': vw, 'w_weight': ww,
            'total_weight': uw + vw + ww,
        })
    
    # A-factor span rank
    A_mat = np.array([t['u'] for t in restricted_terms], dtype=np.uint8)
    a_span_rank = f2_rank(A_mat)
    
    # V-factor and W-factor span ranks
    V_mat = np.array([t['v'] for t in restricted_terms], dtype=np.uint8)
    W_mat = np.array([t['w'] for t in restricted_terms], dtype=np.uint8)
    v_span_rank = f2_rank(V_mat)
    w_span_rank = f2_rank(W_mat)
    
    return {
        'core_name': core_name,
        'verified': correct,
        'raw_length': len(restricted_terms),
        'unique_a_factors': len(a_counter),
        'a_factor_multiplicities': {str(k): v for k, v in a_counter.items() if v > 1},
        'a_span_rank': a_span_rank,
        'v_span_rank': v_span_rank, 
        'w_span_rank': w_span_rank,
        'cancellation_analysis': cancellation_info,
        'weight_stats': sorted(weights, key=lambda x: x['total_weight']),
    }

def check_improvability(restricted_terms, core, r_target):
    """Check if we can reduce the decomposition to r_target terms
    by removing pairs that share A-factor and whose B⊗C contribution
    can be absorbed elsewhere."""
    na, nb, nc = core.shape
    a_factors = [tuple(t['u']) for t in restricted_terms]
    a_counter = Counter(a_factors)
    
    # Effective length after canceling exact duplicates
    triples = [(tuple(t['u']), tuple(t['v']), tuple(t['w'])) 
               for t in restricted_terms]
    triple_counter = Counter(triples)
    effective_length = sum(v % 2 for v in triple_counter.values())
    
    return {
        'raw_length': len(restricted_terms),
        'effective_length_after_cancellation': effective_length,
        'target_length': r_target,
        'gap': effective_length - r_target,
        'duplicate_triples': sum(1 for v in triple_counter.values() if v > 1),
    }

def main():
    outdir = Path('data/restricted_cores')
    T = build_matmul_tensor_f2()
    
    masks = [
        {'mask': 1,  'label': 'E11', 'name': 'mask_001_E11'},
        {'mask': 10, 'label': 'E12+E21', 'name': 'mask_010_E12_E21'},
        {'mask': 84, 'label': 'E13+E22+E31', 'name': 'mask_084_E13_E22_E31'},
    ]
    
    # All available rank-23 schemes
    schemes = {
        'cn122': 'data/cn122_3x3_r23_repro/scheme.qmm',
        'serendipitous_8d34': 'data/fmm_r23_schemes/serendipitous_8d34.qmm',
        'naive_c88': 'data/fmm_r23_schemes/naive_c88.qmm',
    }
    
    all_results = {}
    
    for mi, minfo in enumerate(masks):
        mask = minfo['mask']
        T_restr, pivot = apply_constraint_f2(T, mask)
        core, _ = extract_core(T_restr, pivot)
        
        print(f"\n{'='*70}")
        print(f"CORE: {minfo['label']} (mask {mask})")
        print(f"{'='*70}")
        
        core_results = {}
        best_length = 999
        best_scheme = None
        
        for sname, spath in schemes.items():
            spath = Path(spath)
            if not spath.exists():
                print(f"  {sname}: file not found, skipping")
                continue
            
            terms = read_qmm_scheme(spath)
            restricted, vanished = restrict_scheme_f2(terms, mask)
            
            analysis = analyze_restricted_decomp(restricted, core, minfo['label'])
            improve = check_improvability(restricted, core, 19)
            
            eff_len = improve['effective_length_after_cancellation']
            if eff_len < best_length:
                best_length = eff_len
                best_scheme = sname
            
            print(f"\n  {sname}:")
            print(f"    Vanished: {len(vanished)} terms")
            print(f"    Surviving: {len(restricted)} raw, {eff_len} effective")
            print(f"    A-span rank: {analysis['a_span_rank']}/{core.shape[0]}")
            print(f"    V-span rank: {analysis['v_span_rank']}/9")
            print(f"    W-span rank: {analysis['w_span_rank']}/9")
            if analysis['a_factor_multiplicities']:
                print(f"    Duplicate A-factors: {analysis['a_factor_multiplicities']}")
            if analysis['cancellation_analysis']:
                for ci in analysis['cancellation_analysis']:
                    print(f"    Shared A={ci['a_factor']}: {ci['count']} terms, "
                          f"B⊗C sum rank={ci['bc_sum_rank']}")
            print(f"    Gap to rank 19: {improve['gap']}")
            
            core_results[sname] = {
                'vanished': vanished,
                'raw_length': len(restricted),
                'effective_length': eff_len,
                'analysis': analysis,
                'improvability': improve,
            }
        
        print(f"\n  *** Best scheme for {minfo['label']}: {best_scheme} "
              f"(effective length {best_length})")
        
        all_results[minfo['name']] = {
            'label': minfo['label'],
            'mask': mask,
            'best_scheme': best_scheme,
            'best_length': best_length,
            'schemes': core_results,
        }
    
    with open(outdir / 'restriction_analysis.json', 'w') as f:
        json.dump(all_results, f, indent=2, default=str)
    
    print(f"\n{'='*70}")
    print(f"SUMMARY: Best restricted lengths across all schemes")
    print(f"{'='*70}")
    for name, res in all_results.items():
        print(f"  {res['label']}: best = {res['best_length']} "
              f"(from {res['best_scheme']}), Wang LB = 19")
        print(f"    => Gap to rank-22 route: {res['best_length'] - 19}")
    
    print(f"\nResults saved to {outdir}/restriction_analysis.json")

if __name__ == '__main__':
    main()
