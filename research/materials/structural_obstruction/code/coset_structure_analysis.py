#!/usr/bin/env python3
"""Coset structure analysis for R(T333) >= 21.

Structural theorem: if R_F2(T333) = 20, the ≥4 rank-≥2 A-factors all lie in a 
single coset of u⊗F_2^3 (or F_2^3⊗v^T). This script:
1. Verifies the pairwise rank-1 sum theorem
2. Enumerates all coset types (u=e1 WLOG)
3. Matches dim-3 and dim-4 spans to Wang cert orbits
4. Checks closures against Wang LB values
"""
import json, sys, os, time, argparse
import numpy as np
from collections import Counter, defaultdict

def int_to_mat(x):
    """9-bit integer → 3×3 F2 matrix."""
    return np.array([[(x >> (3*i+j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8)

def mat_to_int(M):
    """3×3 F2 matrix → 9-bit integer."""
    v = 0
    for i in range(3):
        for j in range(3):
            if M[i,j] & 1:
                v |= 1 << (3*i+j)
    return v

def gf2_rank(M):
    """Rank of matrix over F2 using Gaussian elimination."""
    A = M.copy() % 2
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        # Find pivot
        pivot = None
        for rr in range(r, rows):
            if A[rr, c]:
                pivot = rr
                break
        if pivot is None:
            continue
        if pivot != r:
            A[[r, pivot]] = A[[pivot, r]]
        for rr in range(rows):
            if rr != r and A[rr, c]:
                A[rr] = (A[rr] + A[r]) % 2
        r += 1
    return r

def mat_rank_f2(x):
    """Rank of 3×3 F2 matrix given as 9-bit integer."""
    return gf2_rank(int_to_mat(x))

def gf2_matmul(A, B):
    """Matrix multiply over F2."""
    return (A @ B) % 2

def apply_action(A, B, x):
    """Apply (A,B) ∈ GL3×GL3 to 3×3 matrix x: A x B^T (over F2)."""
    M = int_to_mat(x)
    return mat_to_int(gf2_matmul(gf2_matmul(A, M), B.T))

def generate_gl3f2():
    """Generate all 168 elements of GL3(F2)."""
    matrices = []
    for a in range(512):
        M = int_to_mat(a)
        if gf2_rank(M) == 3:
            matrices.append(M)
    return matrices

def subspace_from_basis(basis_ints):
    """Given basis vectors (as integers), enumerate all nonzero elements of span."""
    d = len(basis_ints)
    elements = set()
    for mask in range(1, 1 << d):
        v = 0
        for i in range(d):
            if mask & (1 << i):
                v ^= basis_ints[i]
        if v > 0:
            elements.add(v)
    return frozenset(elements)

def subspace_from_constraints(constraint_values):
    """Given constraint vectors (dual basis), compute the subspace (nullspace)."""
    n = 9  # dimension of F2^{3x3}
    k = len(constraint_values)
    # Build constraint matrix
    C = np.zeros((k, n), dtype=np.uint8)
    for i, cv in enumerate(constraint_values):
        for j in range(n):
            C[i, j] = (cv >> j) & 1
    # Compute nullspace over F2
    # Use RREF to find pivot and free variables
    A = C.copy()
    rows, cols = A.shape
    pivots = []
    r = 0
    for c in range(cols):
        pivot = None
        for rr in range(r, rows):
            if A[rr, c]:
                pivot = rr
                break
        if pivot is None:
            continue
        if pivot != r:
            A[[r, pivot]] = A[[pivot, r]]
        for rr in range(rows):
            if rr != r and A[rr, c]:
                A[rr] = (A[rr] + A[r]) % 2
        pivots.append(c)
        r += 1
    # Free variables
    free = [c for c in range(cols) if c not in pivots]
    # Build basis of nullspace
    basis = []
    for f in free:
        v = np.zeros(cols, dtype=np.uint8)
        v[f] = 1
        for i, p in enumerate(pivots):
            v[p] = A[i, f]
        basis.append(v)
    # Convert to integers
    basis_ints = []
    for v in basis:
        x = 0
        for j in range(n):
            if v[j]:
                x |= 1 << j
        basis_ints.append(x)
    return subspace_from_basis(basis_ints), basis_ints

def rank_signature(elements):
    """Compute (count_rank1, count_rank2, count_rank3) for a set of nonzero elements."""
    sig = [0, 0, 0, 0]
    for x in elements:
        r = mat_rank_f2(x)
        sig[r] += 1
    return tuple(sig[1:])  # (rank1, rank2, rank3)

def main():
    t0 = time.time()
    parser = argparse.ArgumentParser()
    parser.add_argument("--cert", default="data/wang_f2_lb20/cert_profile.json")
    parser.add_argument("--out", default="data/coset_analysis/coset_structure_analysis.json")
    args = parser.parse_args()
    
    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    
    # Precompute all matrix ranks
    rank_cache = {}
    for x in range(512):
        rank_cache[x] = mat_rank_f2(x)
    
    print("Generating GL3(F2)...")
    gl3 = generate_gl3f2()
    print(f"  |GL3(F2)| = {len(gl3)}")
    assert len(gl3) == 168
    
    # ===== Phase 1: Load cert and build orbit lookup =====
    print("\nLoading Wang certificate profile...")
    cert = json.load(open(args.cert))
    
    # Build orbit lookup: dim -> list of (cert_index, lb, elements_frozenset, rank_sig)
    orbit_lookup = defaultdict(list)
    # Process all orbits from first_orbits (which contains all 496 entries)
    all_orbits = cert['first_orbits']
    for entry in all_orbits:
        idx = entry['index']
        lb = entry['rank_lower_bound']
        cc = entry['constraint_count']
        dim = 9 - cc
        cv = entry['constraint_values']
        if cc == 0:
            continue  # dim 9, skip
        elements, basis = subspace_from_constraints(cv)
        sig = rank_signature(elements)
        orbit_lookup[dim].append({
            'cert_index': idx,
            'lb': lb,
            'elements': elements,
            'rank_sig': sig,
            'constraint_values': cv,
        })
    
    # Print dim-3 and dim-4 statistics
    for d in [3, 4]:
        orbits = orbit_lookup[d]
        lb_dist = Counter(o['lb'] for o in orbits)
        print(f"  Dim {d}: {len(orbits)} orbits, LB distribution: {dict(sorted(lb_dist.items()))}")
    
    # ===== Phase 2: Verify structural theorem =====
    print("\n===== Verifying pairwise rank-1 sum theorem =====")
    # For orbits 478-491 (dim-2), check rank patterns
    dim2_orbits = orbit_lookup[2]
    print(f"  {len(dim2_orbits)} dim-2 orbits")
    
    # Orbits with ≥2 rank-≥2 elements and LB ≤ 18
    relevant_lb_le18 = []
    for o in dim2_orbits:
        n_high = o['rank_sig'][1] + o['rank_sig'][2]  # rank2 + rank3
        if n_high >= 2 and o['lb'] <= 18:
            relevant_lb_le18.append(o)
            print(f"    idx={o['cert_index']} lb={o['lb']} rank_sig={o['rank_sig']} "
                  f"(rank1={o['rank_sig'][0]}, rank2={o['rank_sig'][1]}, rank3={o['rank_sig'][2]})")
    
    # Verify: for each such orbit, the unique rank-1 element is the sum of the 2 rank-≥2 elements
    print("\n  Verifying rank-1 uniqueness in relevant dim-2 orbits with LB≤18:")
    for o in relevant_lb_le18:
        elements = list(o['elements'])
        rank1_elts = [x for x in elements if rank_cache[x] == 1]
        rankge2_elts = [x for x in elements if rank_cache[x] >= 2]
        # Check: the single rank-1 element should be XOR of the two rank-≥2 elements
        if len(rank1_elts) == 1 and len(rankge2_elts) == 2:
            xor_val = rankge2_elts[0] ^ rankge2_elts[1]
            ok = (xor_val == rank1_elts[0])
            print(f"    idx={o['cert_index']}: rank1={rank1_elts}, rankge2={rankge2_elts}, "
                  f"XOR={xor_val}, match={ok}")
        else:
            print(f"    idx={o['cert_index']}: unexpected pattern: "
                  f"rank1={len(rank1_elts)}, rankge2={len(rankge2_elts)}")
    
    # Also check: orbits with ≥2 rank-≥2 elements and LB = 19
    relevant_lb19 = []
    for o in dim2_orbits:
        n_high = o['rank_sig'][1] + o['rank_sig'][2]
        if n_high >= 2 and o['lb'] >= 19:
            relevant_lb19.append(o)
    print(f"\n  Relevant dim-2 orbits with LB≥19 (already closed): {len(relevant_lb19)}")
    for o in relevant_lb19:
        print(f"    idx={o['cert_index']} lb={o['lb']} rank_sig={o['rank_sig']}")
    
    # ===== Phase 3: Enumerate column-type cosets =====
    print("\n===== Enumerating column-type cosets (u=e1) =====")
    # u = e1 = [1,0,0]^T, integer = 1 (bit 0)
    # Coset: p + e1 ⊗ F2^3 = {p + e1 v^T : v in F2^3}
    # e1 v^T has bits only in positions 0,1,2 (first row)
    # e1 e1^T = 1, e1 e2^T = 2, e1 e3^T = 4
    
    first_row_masks = list(range(8))  # 0..7 = all 3-bit patterns in positions 0-2
    
    # Lower block B is encoded in bits 3-8. There are 64 possibilities.
    coset_results = []
    for lower_block in range(64):
        # The base element p has lower block shifted to bits 3-8
        # For each first_row value, we get a coset element
        p_base = lower_block << 3  # lower block with zero first row
        
        coset_elements = []
        for fr in first_row_masks:
            elem = p_base | fr
            coset_elements.append(elem)
        
        # Rank distribution
        ranks = [rank_cache[x] for x in coset_elements]
        rank_dist = Counter(ranks)
        n_rankge2 = sum(1 for r in ranks if r >= 2)
        
        # Lower block rank
        B_mat = int_to_mat(p_base)[1:, :]  # rows 1,2 of the matrix
        lb_rank = gf2_rank(B_mat)
        
        coset_info = {
            'lower_block': lower_block,
            'lower_block_rank': int(lb_rank),
            'n_rankge2': n_rankge2,
            'rank_dist': {str(k): v for k, v in sorted(rank_dist.items())},
            'elements': coset_elements,
        }
        
        if n_rankge2 >= 4:
            # Compute 4-dim span S = <p> + e1 ⊗ F2^3
            # Basis: p_base (with any nonzero first row) and e1⊗e1^T, e1⊗e2^T, e1⊗e3^T
            # Actually, span = {all 16 elements: 0, coset elements (8), e1⊗F2^3 (7, nonzero)}
            # Wait: S = <p_base> + <1,2,4> where 1,2,4 are e1e1^T, e1e2^T, e1e3^T
            # Need: p_base not in <1,2,4> (which means lower block nonzero)
            if p_base == 0:
                # Lower block is zero, span is just e1⊗F2^3 = <1,2,4>, dim 3
                span_dim = 3
                span_elements = subspace_from_basis([1, 2, 4])
            else:
                span_dim = 4  # p_base has nonzero lower block
                span_elements = subspace_from_basis([p_base, 1, 2, 4])
            
            coset_info['span_dim'] = span_dim
            coset_info['span_size'] = len(span_elements)
            coset_info['span_rank_sig'] = rank_signature(span_elements)
        
        coset_results.append(coset_info)
    
    # Summarize
    feasible_cosets = [c for c in coset_results if c['n_rankge2'] >= 4]
    print(f"  Total cosets: 64")
    print(f"  Cosets with ≥4 rank-≥2 elements: {len(feasible_cosets)}")
    
    lb_rank_dist = Counter(c['lower_block_rank'] for c in feasible_cosets)
    print(f"  Lower block rank distribution: {dict(sorted(lb_rank_dist.items()))}")
    
    # ===== Phase 4: Match spans to Wang cert orbits =====
    print("\n===== Matching spans to Wang cert orbits =====")
    
    # Build action lookup: for each group element, how does it transform a 9-bit integer?
    # Precompute all transformations
    print("  Precomputing group action on F2^9...")
    action_table = []  # action_table[g_idx][x] = (A,B)·x
    for i, A in enumerate(gl3):
        for j, B in enumerate(gl3):
            # Only need to compute action on specific elements
            pass
    # Actually, let's use a different approach: for each target subspace,
    # check if any (A,B) maps a cert representative to it
    
    # For efficiency, use rank_sig as first filter
    def find_orbit(target_elements, dim):
        """Find which cert orbit a subspace belongs to."""
        target_sig = rank_signature(target_elements)
        candidates = [o for o in orbit_lookup[dim] if o['rank_sig'] == target_sig]
        if not candidates:
            return None
        
        target_set = frozenset(target_elements)
        
        for o in candidates:
            cert_elements = list(o['elements'])
            # Try to find (A,B) mapping cert_elements to target_set
            # For efficiency, pick one cert element and try to map it to each target element
            # Then check consistency
            found = False
            for A in gl3:
                if found:
                    break
                for B in gl3:
                    # Transform all cert elements
                    image = set()
                    ok = True
                    for x in cert_elements:
                        y = apply_action(A, B, x)
                        if y not in target_set:
                            ok = False
                            break
                        image.add(y)
                    if ok and len(image) == len(cert_elements):
                        found = True
                        break
            if found:
                return o
        return None
    
    # Match dim-4 spans
    print("\n  Matching dim-4 coset spans to cert orbits...")
    dim4_matches = {}
    unique_dim4_spans = {}
    for c in feasible_cosets:
        if c.get('span_dim') != 4:
            continue
        span_key = frozenset(subspace_from_basis([c['lower_block'] << 3, 1, 2, 4]))
        if span_key in unique_dim4_spans:
            c['cert_match'] = unique_dim4_spans[span_key]
            continue
        
        match = find_orbit(span_key, 4)
        if match:
            c['cert_match'] = {'cert_index': match['cert_index'], 'lb': match['lb']}
            unique_dim4_spans[span_key] = c['cert_match']
            print(f"    lb={c['lower_block']:2d} rank(B)={c['lower_block_rank']} "
                  f"n_ge2={c['n_rankge2']} rank_sig={c['span_rank_sig']} "
                  f"→ cert idx={match['cert_index']} LB={match['lb']}")
        else:
            c['cert_match'] = None
            unique_dim4_spans[span_key] = None
            print(f"    lb={c['lower_block']:2d} rank(B)={c['lower_block_rank']} "
                  f"n_ge2={c['n_rankge2']} rank_sig={c['span_rank_sig']} → NO MATCH")
    
    # ===== Phase 5: Closure analysis =====
    print("\n===== Closure analysis =====")
    
    # For each coset with ≥4 rank-≥2 elements:
    # Case 1: dim L = 3 (span is 4-dim). Need LB(span) ≥ 21 - |H|.
    # Case 2: dim L = 2 (span is 3-dim, |H| = 4). Need LB(span) ≥ 17.
    # Case 3: dim L = 2 BUT additional rank-1 factors in span reduce remaining terms.
    
    # The key question: for which |H| values is the span's LB sufficient?
    print("\n  Dim-4 spans (dim L = 3):")
    for c in feasible_cosets:
        if c.get('span_dim') != 4:
            continue
        if c.get('cert_match') is None:
            status = "NO_MATCH"
        else:
            lb = c['cert_match']['lb']
            max_H = c['n_rankge2']  # maximum possible |H|
            # Additional rank-1 elements in span that could be killed
            span_key = frozenset(subspace_from_basis([c['lower_block'] << 3, 1, 2, 4]))
            n_rank1_in_span = sum(1 for x in span_key if rank_cache[x] == 1)
            
            # For each possible |H| from 4 to max_H:
            statuses = []
            for h in range(4, max_H + 1):
                # Additional killed rank-1 factors (up to n_rank1_in_span)
                for extra in range(0, n_rank1_in_span + 1):
                    remaining = 20 - h - extra
                    if remaining < lb:
                        statuses.append(f"|H|={h}+{extra}r1: {remaining}<{lb} CLOSED")
                        break
                else:
                    statuses.append(f"|H|={h}: {20-h}>={lb} OPEN")
            
            # Best case analysis (max killed)
            min_remaining = 20 - max_H - n_rank1_in_span
            if min_remaining < lb:
                status = f"CLOSED(best: {min_remaining}<{lb})"
            else:
                # Check if min |H| = 4 with no extra gives closure
                if 20 - 4 < lb:
                    status = f"CLOSED(base: {20-4}<{lb})"
                else:
                    status = f"OPEN(lb={lb}, max_H={max_H}, r1_in_span={n_rank1_in_span})"
            
            c['closure_status'] = status
            c['n_rank1_in_span'] = n_rank1_in_span
        
        print(f"    lb_idx={c['lower_block']:2d} rank(B)={c['lower_block_rank']} "
              f"n_ge2={c['n_rankge2']} match={c.get('cert_match')} "
              f"status={c.get('closure_status', 'N/A')}")
    
    # Count open vs closed
    dim4_open = [c for c in feasible_cosets if c.get('span_dim') == 4 and 'OPEN' in c.get('closure_status', '')]
    dim4_closed = [c for c in feasible_cosets if c.get('span_dim') == 4 and 'CLOSED' in c.get('closure_status', '')]
    print(f"\n  Summary: {len(dim4_closed)} closed, {len(dim4_open)} open")
    
    if dim4_open:
        print("\n  OPEN dim-4 cosets (need further analysis):")
        for c in dim4_open:
            print(f"    lb_idx={c['lower_block']:2d} rank(B)={c['lower_block_rank']} "
                  f"n_ge2={c['n_rankge2']} LB={c['cert_match']['lb'] if c.get('cert_match') else '?'}")
    
    elapsed = time.time() - t0
    
    result = {
        'schema': 'coset_structure_analysis_v1',
        'elapsed_sec': elapsed,
        'dim3_lb_dist': dict(sorted(Counter(o['lb'] for o in orbit_lookup[3]).items())),
        'dim4_lb_dist': dict(sorted(Counter(o['lb'] for o in orbit_lookup[4]).items())),
        'relevant_dim2_lb_le18': [{'idx': o['cert_index'], 'lb': o['lb'], 'rank_sig': o['rank_sig']} 
                                   for o in relevant_lb_le18],
        'total_feasible_cosets': len(feasible_cosets),
        'dim4_closed': len(dim4_closed),
        'dim4_open': len(dim4_open),
        'open_cosets': [{
            'lower_block': c['lower_block'],
            'lower_block_rank': c['lower_block_rank'],
            'n_rankge2': c['n_rankge2'],
            'cert_match': c.get('cert_match'),
            'closure_status': c.get('closure_status'),
            'n_rank1_in_span': c.get('n_rank1_in_span'),
        } for c in dim4_open],
    }
    
    with open(args.out, 'w') as f:
        json.dump(result, f, indent=2, sort_keys=True)
    print(f"\nTotal time: {elapsed:.1f}s")
    print(f"Saved: {args.out}")

if __name__ == '__main__':
    main()
