#!/usr/bin/env python3
r"""Check the torsion-layer direct-sum lemma for finite-order weights.

For arbitrary finite-order diagonal De Groote weights, choose residue exponents
P_a,Q_b,R_c in {0,...,d-1}.  A multiplicative block is defined by congruence of
(P_a-Q_b, Q_b-R_c) modulo d.  Its additive sub-blocks are defined by equality
of the chosen integer differences.  The repaired proof needs two facts:

1. Different additive sub-blocks inside the same multiplicative block are
disjoint in the original a-, b-, and c-index sets, hence form an actual tensor
direct sum in the matrix-multiplication factor spaces U=(a,b), V=(b,c), W=(a,c).
2. Among these additive sub-blocks, at most one has all three actual tensor
factor dimensions > 2.  Therefore Ja'Ja'--Takche rank additivity can peel off
all small components (those with at least one factor dimension <=2).

This script exhaustively checks these combinatorial facts for normalized
P0=Q0=R0=0 patterns for d in a requested range.  It is not the proof, but a
compact evidence carrier guarding against indexing mistakes.
"""
from __future__ import annotations

import argparse
import itertools
import json
import time
from collections import Counter, defaultdict
from pathlib import Path

TRIPLES = [(a,b,c) for a in range(3) for b in range(3) for c in range(3)]


def factor_dims(block):
    U = {(a,b) for a,b,c in block}
    V = {(b,c) for a,b,c in block}
    W = {(a,c) for a,b,c in block}
    return (len(U), len(V), len(W))


def analyze_pattern(P,Q,R,d):
    mult = defaultdict(list)
    for a,b,c in TRIPLES:
        mult[((P[a]-Q[b]) % d, (Q[b]-R[c]) % d)].append((a,b,c))
    violations = []
    max_subblocks = 0
    max_large = 0
    subblock_count_hist = Counter()
    large_count_hist = Counter()
    small_dims_hist = Counter()
    for mlabel, members in mult.items():
        add = defaultdict(list)
        for a,b,c in members:
            add[(P[a]-Q[b], Q[b]-R[c])].append((a,b,c))
        subblocks = [tuple(sorted(v)) for v in add.values()]
        max_subblocks = max(max_subblocks, len(subblocks))
        subblock_count_hist[len(subblocks)] += 1
        # pairwise original-index disjointness between different additive subblocks
        for i in range(len(subblocks)):
            for j in range(i+1, len(subblocks)):
                Bi, Bj = subblocks[i], subblocks[j]
                Ai, Aj = {t[0] for t in Bi}, {t[0] for t in Bj}
                Bi_idx, Bj_idx = {t[1] for t in Bi}, {t[1] for t in Bj}
                Ci, Cj = {t[2] for t in Bi}, {t[2] for t in Bj}
                if Ai & Aj or Bi_idx & Bj_idx or Ci & Cj:
                    violations.append({
                        "type": "not_index_disjoint",
                        "d": d,
                        "P": P, "Q": Q, "R": R,
                        "mult_label": mlabel,
                        "block_i": Bi,
                        "block_j": Bj,
                        "shared_A": sorted(Ai & Aj),
                        "shared_B": sorted(Bi_idx & Bj_idx),
                        "shared_C": sorted(Ci & Cj),
                    })
        large = []
        for B in subblocks:
            dims = factor_dims(B)
            small_dims_hist[dims] += 1
            if min(dims) > 2:
                large.append((B,dims))
        max_large = max(max_large, len(large))
        large_count_hist[len(large)] += 1
        if len(large) > 1:
            violations.append({
                "type": "more_than_one_large_subblock",
                "d": d,
                "P": P, "Q": Q, "R": R,
                "mult_label": mlabel,
                "large_subblocks": [{"support": B, "dims": dims} for B,dims in large],
            })
    return violations, max_subblocks, max_large, subblock_count_hist, large_count_hist, small_dims_hist


def scan_d(d):
    t0=time.time()
    vals=range(d)
    total=d**6
    checked=0
    central=0
    violations=[]
    max_subblocks=0
    max_large=0
    sub_hist=Counter(); large_hist=Counter(); dims_hist=Counter()
    for p1,p2,q1,q2,r1,r2 in itertools.product(vals, repeat=6):
        P=(0,p1,p2); Q=(0,q1,q2); R=(0,r1,r2)
        if len(set(P))==1 and len(set(Q))==1 and len(set(R))==1:
            central += 1
            continue
        checked += 1
        v, ms, ml, sh, lh, dh = analyze_pattern(P,Q,R,d)
        if v:
            violations.extend(v[:3])
            # Keep scanning unnecessary after first failure; fail fast.
            break
        max_subblocks=max(max_subblocks,ms); max_large=max(max_large,ml)
        sub_hist.update(sh); large_hist.update(lh); dims_hist.update(dh)
    return {
        "d": d,
        "normalized_patterns_total": total,
        "normalized_central_skipped": central,
        "normalized_noncentral_checked": checked,
        "violations_found": len(violations),
        "first_violations": violations[:3],
        "max_additive_subblocks_per_multiplicative_block": max_subblocks,
        "max_large_subblocks_per_multiplicative_block": max_large,
        "subblock_count_histogram_over_multiplicative_blocks": {str(k): int(v) for k,v in sorted(sub_hist.items())},
        "large_subblock_count_histogram_over_multiplicative_blocks": {str(k): int(v) for k,v in sorted(large_hist.items())},
        "additive_subblock_factor_dims_histogram": {str(k): int(v) for k,v in sorted(dims_hist.items())},
        "elapsed_sec": time.time()-t0,
    }


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--dmax', type=int, default=8)
    ap.add_argument('--d', type=int, action='append')
    args=ap.parse_args()
    ds=args.d if args.d else list(range(2,args.dmax+1))
    results=[]
    for d in ds:
        rec=scan_d(d)
        results.append(rec)
        print(json.dumps({
            "d": d,
            "checked": rec["normalized_noncentral_checked"],
            "violations": rec["violations_found"],
            "max_subblocks": rec["max_additive_subblocks_per_multiplicative_block"],
            "max_large": rec["max_large_subblocks_per_multiplicative_block"],
            "elapsed_sec": rec["elapsed_sec"],
        }, sort_keys=True))
        if rec["violations_found"]:
            break
    out=Path(__file__).resolve().parents[1]/'data/d2_torsion_layers/torsion_direct_sum_lemma_check.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "purpose":"Exhaustive normalized checks for the finite-order torsion direct-sum/JT lemma on d values.",
        "interpretation":"No violations means additive subblocks inside each multiplicative block are actual direct-sum components and at most one component lacks a <=2-dimensional tensor factor, matching the repaired proof conditions.",
        "results":results,
    }, indent=2, sort_keys=True)+'\n')
    print('wrote', out)

if __name__=='__main__':
    main()
