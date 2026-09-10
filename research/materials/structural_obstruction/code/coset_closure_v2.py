#!/usr/bin/env python3
"""Coset structure verification and closure analysis for R(T333) >= 21.

Structural theorem: in any rank-20 decomposition, the ≥4 rank-≥2 A-factors
lie in a single coset p + u⊗F_2^3 (column type) or p + F_2^3⊗v^T (row type).
This script verifies the theorem, enumerates all coset types (u=e1 by GL symmetry),
looks up Wang LB values, and determines which configurations close.
"""
import json, sys, os, time, argparse, pickle
import numpy as np
from collections import Counter, defaultdict
from typing import List, Tuple, Dict, Sequence, FrozenSet

# ======== F2 matrix utilities ========
def gf2_rank(M):
    A = np.array(M, dtype=np.uint8).copy() % 2
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        pivot = None
        for rr in range(r, rows):
            if A[rr, c]:
                pivot = rr; break
        if pivot is None: continue
        if pivot != r: A[[r, pivot]] = A[[pivot, r]]
        for rr in range(rows):
            if rr != r and A[rr, c]: A[rr] = (A[rr] + A[r]) % 2
        r += 1
    return r

def mat_rank(x):
    """Rank of 3x3 F2 matrix encoded as 9-bit integer."""
    M = [[(x >> (3*i+j)) & 1 for j in range(3)] for i in range(3)]
    return gf2_rank(M)

# ======== Subspace utilities ========
def rref_basis(rows, nbits=9):
    basis = []
    for x0 in rows:
        x = int(x0)
        if x == 0: continue
        for rb in basis:
            p = rb.bit_length() - 1
            if (x >> p) & 1: x ^= rb
        if x == 0: continue
        p = x.bit_length() - 1
        for i, rb in enumerate(basis):
            if (rb >> p) & 1: basis[i] = rb ^ x
        basis.append(x)
        basis.sort(key=lambda z: z.bit_length(), reverse=True)
    return tuple(basis)

def pack_basis(basis_rref):
    x = 0
    for i, b in enumerate(basis_rref):
        x |= int(b) << (9 * i)
    return (x << 4) | len(basis_rref)

def span_elements(basis_ints):
    d = len(basis_ints)
    elts = set()
    for mask in range(1, 1 << d):
        v = 0
        for i in range(d):
            if mask & (1 << i): v ^= basis_ints[i]
        if v > 0: elts.add(v)
    return frozenset(elts)

def subspace_key(generators):
    """Compute the LUT key for the subspace spanned by generators."""
    rb = rref_basis(generators)
    return pack_basis(rb)

def in_span(v, rref):
    x = int(v)
    for rb in rref:
        p = rb.bit_length() - 1
        if (x >> p) & 1: x ^= rb
    return x == 0

# ======== Main analysis ========
def main():
    t0 = time.time()
    parser = argparse.ArgumentParser()
    parser.add_argument("--lut", default="data/wang_f2_lb20/wang_subspace_lut.pkl")
    parser.add_argument("--out", default="data/coset_analysis/coset_closure_v2.json")
    args = parser.parse_args()
    os.makedirs(os.path.dirname(args.out), exist_ok=True)

    # Precompute matrix ranks
    rank_cache = {x: mat_rank(x) for x in range(512)}

    # Load LUT
    print("Loading Wang LUT...")
    lut_data = pickle.load(open(args.lut, 'rb'))
    lut = lut_data['lut']
    print(f"  {len(lut)} entries")

    def wang_lb(generators):
        key = subspace_key(generators)
        if key in lut:
            return int(lut[key])
        return None

    # ===== Verify LUT access =====
    print("\nVerifying LUT access:")
    print(f"  Root (dim 0): LB = {wang_lb([])}")  # Should be 20
    print(f"  <E11> = <1>: LB = {wang_lb([1])}")  # Should be 19
    print(f"  <E12+E21> = <10>: LB = {wang_lb([10])}")  # Should be 19
    print(f"  <E13+E22+E31> = <84>: LB = {wang_lb([84])}")  # Should be 19

    # Check dim-2 orbit representatives from cert
    dim2_reps = {
        478: [1, 2], 479: [1, 10], 480: [1, 16], 481: [1, 20],
        482: [1, 84], 483: [1, 160], 484: [16, 84], 485: [10, 16],
        486: [10, 84], 487: [1, 146], 488: [10, 160], 489: [16, 160],
        490: [84, 160], 491: [10, 146]
    }
    print("\n  Dim-2 orbit LB values:")
    for idx in sorted(dim2_reps):
        lb = wang_lb(dim2_reps[idx])
        elts = span_elements(dim2_reps[idx])
        rs = tuple(sorted(rank_cache[x] for x in elts))
        print(f"    idx={idx}: basis={dim2_reps[idx]} LB={lb} ranks={rs}")

    # ===== Phase 1: Verify structural theorem =====
    print("\n===== Phase 1: Verify structural theorem =====")
    # For dim-2 orbits with ≥2 rank-≥2 elements AND LB ≤ 18:
    # check that there is exactly 1 rank-1 element = XOR of the 2 rank-≥2 elements
    relevant_unresolved = []
    for idx, basis in dim2_reps.items():
        elts = span_elements(basis)
        r1 = [x for x in elts if rank_cache[x] == 1]
        rge2 = [x for x in elts if rank_cache[x] >= 2]
        lb = wang_lb(basis)
        if len(rge2) >= 2 and lb <= 18:
            xor_ok = (len(r1) == 1 and len(rge2) == 2 and (rge2[0] ^ rge2[1]) == r1[0])
            print(f"  idx={idx} LB={lb}: rank1={r1} rankge2={rge2} "
                  f"XOR_match={xor_ok}")
            relevant_unresolved.append(idx)

    # ===== Phase 2: Column-type coset enumeration =====
    print("\n===== Phase 2: Coset enumeration (u=e1) =====")
    # e1 = [1,0,0]^T, e1 v^T has bits only in positions 0,1,2
    # Coset: p + e1⊗F2^3 where p has lower block B (bits 3-8)

    coset_results = []
    for lower_block in range(64):
        if lower_block == 0: continue  # zero lower block gives <e1⊗F2^3>, dim 3 not 4
        p_base = lower_block << 3  # matrix with zero first row and lower block
        coset = [p_base | fr for fr in range(8)]
        ranks = [rank_cache[x] for x in coset]
        n_ge2 = sum(1 for r in ranks if r >= 2)
        B_mat = [[(p_base >> (3*i+j)) & 1 for j in range(3)] for i in range(1, 3)]
        lb_rank = gf2_rank(B_mat)

        if n_ge2 < 4: continue

        # Compute span = <p_base, 1, 2, 4>
        span_basis = rref_basis([p_base, 1, 2, 4])
        span_dim = len(span_basis)
        span_key = pack_basis(span_basis)
        span_lb = int(lut[span_key]) if span_key in lut else None
        span_elts = span_elements(span_basis)
        n_r1_in_span = sum(1 for x in span_elts if rank_cache[x] == 1)

        coset_results.append({
            'lower_block': lower_block,
            'lb_rank': int(lb_rank),
            'n_ge2': n_ge2,
            'span_dim': span_dim,
            'span_lb': span_lb,
            'n_r1_in_span': n_r1_in_span,
        })

    # Group by (lb_rank, span_lb) for summary
    by_type = defaultdict(list)
    for c in coset_results:
        by_type[(c['lb_rank'], c['span_lb'], c['n_ge2'])].append(c)

    print(f"\n  Total feasible cosets: {len(coset_results)}")
    print(f"\n  Summary by (lower_block_rank, Wang_LB, n_rankge2):")
    for (lbr, wlb, ng2), group in sorted(by_type.items()):
        # Closure check for dim L = 3 case:
        # Best case: max killed = n_ge2 + n_r1_in_span
        # Need: 20 - killed < wang_lb
        max_r1 = max(c['n_r1_in_span'] for c in group)
        min_remaining_maxkill = 20 - ng2 - max_r1
        min_remaining_minkill = 20 - 4  # at least 4 high-rank killed

        if wlb is not None:
            if min_remaining_minkill < wlb:
                status = f"CLOSED(even 4 killed: {min_remaining_minkill}<{wlb})"
            elif min_remaining_maxkill < wlb:
                status = f"CLOSED(max killed: {min_remaining_maxkill}<{wlb})"
            else:
                status = f"OPEN({min_remaining_maxkill}>={wlb})"
        else:
            status = "NO_LUT"

        print(f"    rank(B)={lbr} LB={wlb} n_ge2={ng2}: "
              f"{len(group)} cosets, r1_in_span≤{max_r1}, "
              f"status={status}")

    # ===== Phase 3: Also check dim L=2 case (3-dim spans) =====
    print("\n===== Phase 3: dim L=2 case (3-dim spans) =====")
    # For 4 high-rank elements in a coset with dim(differences) = 2,
    # span is 3-dim. Need LB(3-dim span) >= 17.
    # Enumerate all possible 3-dim spans from rank-≥2 subsets of size 4.

    dim3_span_lbs = Counter()
    dim3_examples = []
    for lower_block in range(64):
        if lower_block == 0: continue
        p_base = lower_block << 3
        coset = [p_base | fr for fr in range(8)]
        ge2_elts = [x for x in coset if rank_cache[x] >= 2]
        if len(ge2_elts) < 4: continue

        # All 4-element subsets of ge2 elements
        from itertools import combinations
        for quad in combinations(ge2_elts, 4):
            sb = rref_basis(quad)
            sd = len(sb)
            if sd == 3:
                sk = pack_basis(sb)
                lb = int(lut[sk]) if sk in lut else None
                dim3_span_lbs[lb] += 1
                if lb is not None and lb < 17:
                    dim3_examples.append({
                        'lb_idx': lower_block,
                        'quad': list(quad),
                        'span_lb': lb,
                        'span_basis': list(sb),
                    })

    print(f"  LB distribution of 3-dim spans from 4-element rank-≥2 quads:")
    for lb, cnt in sorted(dim3_span_lbs.items()):
        closed = "CLOSED" if lb is not None and lb >= 17 else "OPEN"
        print(f"    LB={lb}: {cnt} quads -> {closed}")

    if dim3_examples:
        print(f"\n  OPEN 3-dim spans with LB < 17:")
        for ex in dim3_examples[:10]:
            print(f"    lb_idx={ex['lb_idx']} quad={ex['quad']} LB={ex['span_lb']} basis={ex['span_basis']}")
    else:
        print(f"\n  ALL 3-dim spans from rank-≥2 quads have LB ≥ 17. ✓")

    # ===== Phase 4: Aggregate closure =====
    print("\n===== Phase 4: Aggregate closure =====")
    all_dim4_open = [c for c in coset_results if c['span_lb'] is not None and 20 - 4 >= c['span_lb']]
    all_dim4_closed = [c for c in coset_results if c['span_lb'] is not None and 20 - 4 < c['span_lb']]

    # For open dim-4, check if killing rank-1 factors in span helps
    truly_open = []
    for c in all_dim4_open:
        max_killed = c['n_ge2'] + c['n_r1_in_span']
        remaining = 20 - max_killed
        if remaining < c['span_lb']:
            all_dim4_closed.append(c)
        else:
            truly_open.append(c)

    dim3_closed = all(lb is not None and lb >= 17 for lb in dim3_span_lbs)

    print(f"  Dim-4 (dim L=3) cosets: {len(all_dim4_closed)} closed, {len(truly_open)} open")
    print(f"  Dim-3 (dim L=2) quads: all closed = {dim3_closed}")

    if truly_open:
        print(f"\n  Truly open dim-4 cosets:")
        for c in truly_open:
            print(f"    lb_idx={c['lower_block']} rank(B)={c['lb_rank']} n_ge2={c['n_ge2']} "
                  f"LB={c['span_lb']} r1_in_span={c['n_r1_in_span']}")

    elapsed = time.time() - t0
    result = {
        'schema': 'coset_closure_v2',
        'elapsed_sec': round(elapsed, 2),
        'dim3_all_closed': dim3_closed,
        'dim3_span_lb_dist': {str(k): v for k, v in sorted(dim3_span_lbs.items())},
        'dim4_closed_count': len(all_dim4_closed),
        'dim4_open_count': len(truly_open),
        'open_dim4': [{k: v for k, v in c.items()} for c in truly_open],
    }
    with open(args.out, 'w') as f:
        json.dump(result, f, indent=2, sort_keys=True)
    print(f"\nTotal: {elapsed:.1f}s -> {args.out}")

if __name__ == '__main__':
    main()
