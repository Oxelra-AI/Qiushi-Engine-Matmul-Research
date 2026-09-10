#!/usr/bin/env python3
"""analysis: brute-force verification of one fiber test result.

For a specific d<k block, enumerate ALL possible k-tuples of rank-one 
quotient images and check whether any k of them span a k-dimensional 
space containing E.  This is intractable for full-size blocks (511^2 
quotient images), but we can compare the fiber test against a complete 
search over attainable QUOTIENT directions.

The fiber test reduces the problem to: does any subspace H of Q/E with 
dim(H) <= k-d have the property that attainable images in rho^{-1}(H) 
span rho^{-1}(H)?  For slack one, this means testing all 1-dim outside 
directions.  The brute force tests ALL k-tuples of distinct attainable 
quotient vectors.

For feasibility, we:
1. Collect all distinct (rem, tag) pairs from rank-one images
2. For each pair of attainable quotient vectors with independent 
   (rem+tag) coordinates, check if they span a 2-dim space containing E
3. Compare result with fiber test
"""
from __future__ import annotations
import json, sys, time
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
import residual_repair_geometry as rg
from free_ab_k_scan_corrected import canonical_reduce
from fiber_resolution import fiber_test

OUTDIR = Path('data/fiber_fixed')


def rank_of_ints(vals):
    piv = {}; r = 0
    for v in vals:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if p in piv: x ^= piv[p]
            else: piv[p] = x; r += 1; break
    return r


def main():
    t0 = time.time()
    sources = rg.load_sources()
    D_cols = rg.D_columns_as_ints()
    terms = sources['cn122_qmm']
    
    # Use the first d<k block from the k=3 scan
    # From the fiber control: block=(0, 12, 14, 21), d=2, k=3
    block = (0, 12, 14, 21)
    retained_idx = [i for i in range(23) if i not in block]
    retained_cols = [rg.vec_mask9_to_outer81(terms[i][0], terms[i][1])
                     for i in retained_idx]
    tagged, E_reps, rank_L, d = rg.build_quotient_basis(retained_cols, D_cols)
    print(f"Block {block}: rank_L={rank_L}, d={d}, k=3, slack={3-d}")
    
    # Run the fixed fiber test
    status_fiber, info_fiber, stats_fiber = fiber_test(tagged, d, 3)
    print(f"Fiber test: {status_fiber}, F0_size={stats_fiber['F0_size']}, "
          f"best_combined={stats_fiber.get('best_combined_rank')}")
    
    # Brute-force: collect all distinct (rem, tag) quotient vectors with reps
    qvecs: Dict[Tuple[int,int], Tuple[int,int]] = {}
    for a in range(1, 512):
        for b in range(1, 512):
            v = rg.vec_mask9_to_outer81(a, b)
            rem, tag = canonical_reduce(tagged, v)
            if (rem, tag) == (0, 0):
                continue
            key = (rem, tag)
            if key not in qvecs:
                qvecs[key] = (a, b)
    
    print(f"Distinct nonzero quotient vectors: {len(qvecs)}")
    
    # For d=2, k=3: we need 3 quotient vectors whose full (rem,tag)-coordinates
    # span a 3-dim space containing E (2-dim).
    # E basis vectors have rem=0 and tag=1<<i for the d=2 E-basis.
    
    # Extract E-basis tags
    E_tags = []
    for i in range(d):
        E_tags.append(1 << i)
    print(f"E-basis tags: {E_tags}")
    
    # We need: 3 independent quotient vectors (in full rem+tag coords)
    # such that E ⊂ span.  This means the 3 vectors must contain
    # the 2D E-subspace in their span.
    
    # Strategy: for each quotient vector v=(rem,tag), represent it as
    # a combined coordinate vector in (rem-bits, tag-bits) space.
    # We need 3 independent combined vectors whose span contains E.
    
    # Since exhaustive 3-tuple search over ~251K vectors is infeasible,
    # use the equivalent algebraic condition:
    # 1. At least 2 of the 3 vectors must have independent E-projections
    #    (tags modulo the outside component)
    # 2. Actually, use the EXACT algebraic characterization:
    #    - Pick a basis for E (2 vectors with rem=0)
    #    - Add one vector with rem≠0 (for the 3rd direction)
    #    - OR pick 3 vectors that span E plus 1 outside direction
    
    # Most efficient: separate into rem=0 and rem≠0 fibers,
    # then test exactly as the fiber test does, but VERIFY by
    # also checking all pairs from rem≠0.
    
    F0 = {tag: ab for (rem,tag), ab in qvecs.items() if rem == 0}
    Fz = defaultdict(dict)  # Fz[rem][tag] = (a,b)
    for (rem, tag), ab in qvecs.items():
        if rem != 0:
            Fz[rem][tag] = ab
    
    print(f"F0: {len(F0)} entries, rank {rank_of_ints(list(F0.keys()))}")
    print(f"Nonzero fibers: {len(Fz)}")
    
    # Check all nonzero fibers with tag=0 entries (the bug case)
    tag0_fibers = sum(1 for rem, fiber in Fz.items() if 0 in fiber)
    print(f"Fibers with tag=0 entry: {tag0_fibers}")
    
    # Exhaustive fiber-level check matching the algorithm
    # For each nonzero rem z, check if F0 ∪ {tag⊕t0 : tag ∈ Fz[z]} spans d
    best = rank_of_ints(list(F0.keys()))
    best_z = None
    tested = 0
    for rem in sorted(Fz.keys()):
        fiber = Fz[rem]
        if not fiber:
            continue
        tested += 1
        ref_tag = next(iter(fiber))
        diffs = set()
        for tag in fiber:
            diff = tag ^ ref_tag
            if diff:
                diffs.add(diff)
        combined = set(F0.keys()) | diffs
        r = rank_of_ints(list(combined))
        if r > best:
            best = r
            best_z = rem
    
    print(f"\nBrute-force fiber scan: {tested} fibers tested")
    print(f"Best combined E-rank: {best} (target d={d})")
    print(f"Best fiber rem: {best_z}")
    
    # Cross-check: does fiber test agree?
    match = (best < d and status_fiber == 'NO_FIBER_COVER') or \
            (best >= d and status_fiber in ('E_SPAN_OK', 'FIBER_OK'))
    print(f"\nFiber test agrees with brute force: {match}")
    
    out = {
        'block': list(block),
        'rank_L': rank_L, 'd': d, 'k': 3,
        'qvec_count': len(qvecs),
        'F0_count': len(F0), 'F0_rank': rank_of_ints(list(F0.keys())),
        'nonzero_fibers': len(Fz),
        'tag0_fibers': tag0_fibers,
        'brute_best_combined': best,
        'fiber_status': status_fiber,
        'match': match,
        'elapsed_sec': time.time() - t0,
    }
    OUTDIR.mkdir(parents=True, exist_ok=True)
    op = OUTDIR / 'brute_force_fiber_control.json'
    op.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved: {op}")

if __name__ == '__main__':
    main()
