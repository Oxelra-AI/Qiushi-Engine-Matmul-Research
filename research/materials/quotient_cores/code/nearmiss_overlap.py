#!/usr/bin/env python3
"""analysis: detailed overlap analysis for the near-miss support."""
import json, sys, numpy as np
from collections import Counter
from pathlib import Path

sys.path.insert(0, 'scripts')
from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2
from dual_basis_instrument import gf2_mat_inv

T_full = build_matmul_tensor_f2()
T_core = T_full[1:, :, :]
na = 8

S = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]

rk9_qs = []
weight_rank = {}
for q in range(1, 256):
    M = contraction_matrix(T_core, q)
    rk = mat_rank_f2(M)
    w = sum(1 for p in S if (p & q).bit_count() & 1)
    weight_rank[q] = (w, rk)
    if rk == 9:
        rk9_qs.append(q)

w_hist = Counter(weight_rank[q][0] for q in rk9_qs)
print(f"Rank-9 contractions: {len(rk9_qs)}")
print(f"Weight histogram (rank-9): {dict(sorted(w_hist.items()))}")
sat9 = [q for q in rk9_qs if weight_rank[q][0] == 9]
print(f"Saturated rank-9 (w=9): {len(sat9)}")

per_point = {p: sum(1 for q in rk9_qs if (p & q).bit_count() & 1) for p in S}
print(f"Per-point rank-9 participation counts: {Counter(per_point.values())}")

overlaps = []
for i, q1 in enumerate(sat9):
    for q2 in sat9[i+1:]:
        common = sum(1 for p in S if (p&q1).bit_count()&1 and (p&q2).bit_count()&1)
        M1_inv = gf2_mat_inv(contraction_matrix(T_core, q1))
        M2_inv = gf2_mat_inv(contraction_matrix(T_core, q2))
        N = (M1_inv + M2_inv) % 2
        N_rank = mat_rank_f2(N)
        db_bound = (18 - N_rank) // 2
        overlaps.append((q1, q2, common, N_rank, db_bound))

overlap_hist = Counter(o[2] for o in overlaps)
n_rank_hist = Counter(o[3] for o in overlaps)
violations = [(q1,q2,k,nr,db) for q1,q2,k,nr,db in overlaps if k > db]
tight = [(q1,q2,k,nr,db) for q1,q2,k,nr,db in overlaps if k == db]

print(f"\nSaturated pairs: {len(overlaps)}")
print(f"Overlap histogram: {dict(sorted(overlap_hist.items()))}")
print(f"N-rank histogram (among sat pairs): {dict(sorted(n_rank_hist.items()))}")
print(f"Violations of dual-basis bound: {len(violations)}")
print(f"Tight (overlap = bound): {len(tight)}")
print(f"Max overlap: {max(o[2] for o in overlaps) if overlaps else 0}")
for v in violations[:5]:
    print(f"  q1={v[0]}, q2={v[1]}, overlap={v[2]}, N_rank={v[3]}, bound={v[4]}")

# Total weight statistics
all_w = [weight_rank[q][0] for q in range(1,256)]
rk_w = {r: Counter(weight_rank[q][0] for q in range(1,256) if weight_rank[q][1]==r)
         for r in [3,6,9]}
for r in [3,6,9]:
    print(f"Rank {r} weight dist: {dict(sorted(rk_w[r].items()))}")

out = Path("data/dual_basis/nearmiss_overlap_detail.json")
json.dump({
    'support': S,
    'weight_hist_rk9': dict(sorted(w_hist.items())),
    'saturated_rk9': len(sat9),
    'pair_count': len(overlaps),
    'overlap_hist': {str(k):v for k,v in sorted(overlap_hist.items())},
    'n_rank_hist_sat': {str(k):v for k,v in sorted(n_rank_hist.items())},
    'violations': len(violations),
    'tight': len(tight),
}, out, indent=2)
print(f"\nSaved {out}")
