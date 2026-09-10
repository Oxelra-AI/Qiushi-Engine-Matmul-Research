#!/usr/bin/env python3
"""analysis: rank-one growth analysis from W.

Key insight from T_{3,3,3}: elements of W=col(D) have rank = 3*rank(X)
where X is the corresponding 3x3 matrix.  Therefore:
- W contains 0 rank-one matrices (rank 1 is not a multiple of 3)
- W + <s> for any rank-one s has EXACTLY 1 rank-one ({s} itself):
  any other rank-one r in W+<s> satisfies r+s ∈ W, but r+s has rank ≤ 2,
  which contradicts min rank in W being 3.

This gives a PROVABLE growth constraint. For two rank-ones s1, s2:
W + <s1, s2> can have extra rank-ones only when s1 + s2 + w = rank-one for 
some rank-3 element w ∈ W.  The rank-3 elements of W correspond to rank-1 
3x3 matrices (49 over F_2: 7 nonzero row vectors × 7 nonzero column vectors).

This script:
1. Verifies the rank-3 constraint analytically
2. Enumerates all rank-3 elements of W (should be 49)
3. For random 22-dim W-extensions, counts rank-one content empirically
4. Computes the maximum provable rank-one count bound
"""
from __future__ import annotations
import json, sys, time, random
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
import residual_repair_geometry as rg
from rankone_lattice import rank_ones_in_span, rank_of_int_list
from linear_completion import build_t333_f2, tensor_to_D

OUTDIR = Path('data/rankone_lattice')


def mat9x9_rank_f2(v: int) -> int:
    """Rank of a 9x9 matrix over F2, packed as 81-bit integer."""
    rows = []
    for i in range(9):
        rows.append((v >> (9 * i)) & 0x1FF)
    piv = {}; r = 0
    for row in rows:
        x = row
        while x:
            p = x.bit_length() - 1
            if p in piv: x ^= piv[p]
            else: piv[p] = x; r += 1; break
    return r


def main():
    t0 = time.time()
    T = build_t333_f2()
    D = tensor_to_D(T)
    
    # Build W basis
    W_basis = []
    for c in range(9):
        v = 0
        for i in range(81):
            if D[i, c] & 1:
                v |= 1 << i
        W_basis.append(v)
    
    # 1. Verify: enumerate all nonzero elements of W, check rank is mult of 3
    print("=== W rank structure ===")
    rank_hist = Counter()
    for mask in range(1, 512):
        v = 0
        for i in range(9):
            if (mask >> i) & 1:
                v ^= W_basis[i]
        r = mat9x9_rank_f2(v)
        rank_hist[r] += 1
    print(f"W has {sum(rank_hist.values())} nonzero elements")
    print(f"Rank histogram: {dict(sorted(rank_hist.items()))}")
    all_mult_3 = all(r % 3 == 0 for r in rank_hist.keys())
    print(f"All ranks are multiples of 3: {all_mult_3}")
    rank3_count = rank_hist.get(3, 0)
    print(f"Rank-3 elements (correspond to rank-1 3x3 matrices): {rank3_count}")
    
    # 2. Verify rank-3 count matches 7*7=49 rank-1 3x3 matrices
    rank1_3x3 = 0
    for x in range(1, 8):
        for y in range(1, 8):
            rank1_3x3 += 1
    print(f"Expected rank-1 3x3 matrices: {rank1_3x3}")
    print(f"Match: {rank3_count == rank1_3x3}")
    
    # 3. Verify single-extension property: W + <s> has exactly 1 rank-one
    print("Direct single-extension count (5 random tests):")
    for trial in range(5):
        a = random.randint(1, 511)
        b = random.randint(1, 511)
        s = rg.vec_mask9_to_outer81(a, b)
        count = 0
        # Check all rank-one matrices in span(W, s)
        # v = w + c*s where w ∈ W, c ∈ {0,1}
        # c=0: v ∈ W, rank(v) ≥ 3, not rank-1
        # c=1: v = w + s, rank(v) = 1 iff w + s is rank-1
        for wmask in range(512):
            w = 0
            for i in range(9):
                if (wmask >> i) & 1:
                    w ^= W_basis[i]
            v = w ^ s
            if mat9x9_rank_f2(v) == 1:
                count += 1
        print(f"  a={a}, b={b}: rank-one count in W+<s> = {count}")
    
    # 4. Empirical: random 22-dim W-extensions
    print("\n=== Random 22-dim extensions (W + 13 rank-ones) ===")
    results = []
    for trial in range(10):
        basis = list(W_basis)
        terms = []
        attempts = 0
        while len(terms) < 13 and attempts < 1000:
            a = random.randint(1, 511)
            b = random.randint(1, 511)
            s = rg.vec_mask9_to_outer81(a, b)
            if rank_of_int_list(basis + [s]) > len(basis):
                basis.append(s)
                terms.append((a, b))
            attempts += 1
        if len(terms) < 13:
            continue
        from rankone_lattice import echelon_add, rank_ones_in_span as ro_scan
        tagged = {}
        for i, v in enumerate(basis):
            echelon_add(tagged, v, 1 << i)
        ro = ro_scan(tagged)
        ro_rank = rank_of_int_list([t for _a, _b, t in ro])
        print(f"  Trial {trial}: {len(ro)} rank-ones, "
              f"rank-one rank {ro_rank}, dim {len(tagged)}")
        results.append({
            'trial': trial,
            'dim': len(tagged),
            'rank_one_count': len(ro),
            'rank_one_rank': ro_rank,
            'terms': [[a, b] for a, b in terms[:5]],
        })
    
    out = {
        'W_rank_hist': dict(sorted(rank_hist.items())),
        'all_mult_3': all_mult_3,
        'rank3_count': rank3_count,
        'expected_rank1_3x3': rank1_3x3,
        'random_extensions': results,
        'elapsed_sec': time.time() - t0,
    }
    OUTDIR.mkdir(parents=True, exist_ok=True)
    op = OUTDIR / 'rankone_growth.json'
    op.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved: {op}")


def _build_echelon(vecs):
    basis = {}
    for v in vecs:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if p in basis: x ^= basis[p]
            else:
                for q in list(basis.keys()):
                    if (basis[q] >> p) & 1:
                        basis[q] ^= x
                basis[p] = x
                break
    return basis


if __name__ == '__main__':
    main()
