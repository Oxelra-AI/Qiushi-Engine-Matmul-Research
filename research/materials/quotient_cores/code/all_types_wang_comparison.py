#!/usr/bin/env python3
r"""analysis (part 2): Wang L(D⊥) comparison for ALL dual line rank types.

For each dual line D = span(q_1, q_2) with contraction ranks (r_1, r_2, r_3),
the 6D core subspace D⊥ lifts to a 7D full-tensor subspace with Wang lower
bound L.  The occupation bound  occ >= L  combined with individual contraction
capacities determines the tightest Wang-only constraint on color budgets.

If the Wang-derived constraints already imply every pencil-infeasible budget,
then pencil analysis adds no new support restriction for that rank type.
"""
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

WDIR = Path("research/research_record/workspace")
SCRIPTS = WDIR / "scripts"
ODIR = WDIR / "data" / "pencil_wang_comparison"
ODIR.mkdir(parents=True, exist_ok=True)

if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from wang_capacity_lazy import rref_basis, pack_basis, unpack_basis
from core_capacity_from_wang_lut import CoreQuotient, load_lut


def gf2_rank(M):
    A = np.array(M, dtype=np.uint8) % 2
    m, n = A.shape
    r = 0
    for col in range(n):
        piv = None
        for row in range(r, m):
            if A[row, col]:
                piv = row
                break
        if piv is None:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for row in range(m):
            if row != r and A[row, col]:
                A[row] ^= A[r]
        r += 1
    return r


def gf2_inner(a, b):
    return bin(a & b).count('1') % 2


def build_e11_core():
    T = np.zeros((8, 9, 9), dtype=np.uint8)
    idx = 0
    for i in range(3):
        for j in range(3):
            if i == 0 and j == 0:
                continue
            for k in range(3):
                T[idx, 3*j+k, 3*i+k] = 1
            idx += 1
    return T


def contraction_matrix(T, q):
    na = T.shape[0]
    M = np.zeros((T.shape[1], T.shape[2]), dtype=np.uint8)
    for j in range(na):
        if (q >> j) & 1:
            M = (M + T[j]) % 2
    return M


def compute_dperp_key9(q1, q2, core):
    """Compute the 9-bit LUT key for span(E11, lift(D⊥)) where D = span(q1,q2)."""
    basis = []
    for p in range(1, 256):
        if gf2_inner(p, q1) == 0 and gf2_inner(p, q2) == 0:
            b = list(rref_basis(basis + [p], n=8))
            if len(b) > len(basis):
                basis = b
                if len(basis) == 6:
                    break
    assert len(basis) == 6
    key8 = pack_basis(rref_basis(basis, n=8))
    return core.key9_from_key8(key8)


def main():
    t0 = time.time()
    T = build_e11_core()
    
    crank = {}
    for q in range(1, 256):
        crank[q] = gf2_rank(contraction_matrix(T, q))
    
    print(f"Contraction rank distribution: {dict(Counter(crank.values()))}")
    
    # Load LUT
    lut_path = WDIR / "data" / "wang_f2_lb20" / "wang_subspace_lut.pkl"
    lut, meta = load_lut(lut_path)
    core = CoreQuotient(1)
    print(f"LUT: {len(lut):,} entries")
    
    # Enumerate ALL dual lines
    all_lines = []
    seen = set()
    for q1 in range(1, 256):
        for q2 in range(q1+1, 256):
            q3 = q1 ^ q2
            if q3 == 0 or q3 <= q1:
                continue
            key = tuple(sorted([q1, q2, q3]))
            if key in seen:
                continue
            seen.add(key)
            all_lines.append((q1, q2, q3))
    
    print(f"Total dual lines: {len(all_lines)}")
    
    # For each line, compute rank type and L(D⊥)
    # Group by sorted rank type
    type_data = defaultdict(list)
    for q1, q2, q3 in all_lines:
        r1, r2, r3 = crank[q1], crank[q2], crank[q3]
        rtype = tuple(sorted([r1, r2, r3]))
        
        # Compute L(D⊥)
        key9 = compute_dperp_key9(q1, q2, core)
        L = lut.get(key9, -1)
        
        type_data[rtype].append({
            'line': [q1, q2, q3],
            'ranks': [r1, r2, r3],
            'L_Dperp': L,
        })
    
    # Summarize by rank type
    summary = {}
    for rtype in sorted(type_data.keys()):
        records = type_data[rtype]
        L_vals = [r['L_Dperp'] for r in records]
        L_dist = Counter(L_vals)
        
        min_L = min(L_vals)
        max_L = max(L_vals)
        
        # For each rank type, the maximum individual rank determines when
        # the pencil constraint (idempotent W) applies.
        # The tightest Wang bound: when the tightest rank-r contraction has
        # w = r (tight), occupation = c_10 + r >= L, so c_10 >= L - r.
        r_max = max(rtype)  # the tightest contraction
        r_min = min(rtype)  # rank of N after normalization by max
        
        # Pencil gives: c_10 >= r_min (when N^2=0 and W idempotent)
        # Wang gives: c_10 >= L - r_max (at tight w for the max-rank contraction)
        wang_c10_min = max(0, min_L - r_max)
        pencil_c10_min = r_min  # IF the pencil applies (N^2=0, etc.)
        pencil_redundant_at_min = wang_c10_min >= pencil_c10_min
        
        summary[str(rtype)] = {
            'count': len(records),
            'L_distribution': {str(k): v for k, v in sorted(L_dist.items())},
            'min_L': min_L,
            'max_L': max_L,
            'rank_type': list(rtype),
            'max_rank': r_max,
            'min_rank': r_min,
            'wang_c10_lower': wang_c10_min,
            'pencil_c10_lower_if_applicable': pencil_c10_min,
            'pencil_redundant_at_min_L': pencil_redundant_at_min,
        }
    
    print(f"\n{'Rank Type':>12s}  {'Count':>5s}  {'min L':>5s}  {'max L':>5s}  "
          f"{'Wang c10≥':>9s}  {'Pencil c10≥':>11s}  {'Redundant':>9s}")
    print("-" * 75)
    for rtype in sorted(summary.keys()):
        s = summary[rtype]
        print(f"{rtype:>12s}  {s['count']:5d}  {s['min_L']:5d}  {s['max_L']:5d}  "
              f"{s['wang_c10_lower']:9d}  {s['pencil_c10_lower_if_applicable']:11d}  "
              f"{'YES' if s['pencil_redundant_at_min_L'] else 'NO':>9s}")
    
    # Also show L distribution for types where pencil might add value
    print("\nDetailed L distributions for non-redundant types:")
    for rtype in sorted(summary.keys()):
        s = summary[rtype]
        if not s['pencil_redundant_at_min_L']:
            print(f"  {rtype}: L distribution = {s['L_distribution']}")
    
    results = {
        'total_dual_lines': len(all_lines),
        'rank_type_summary': summary,
        'elapsed_sec': time.time() - t0,
        'interpretation': (
            "Wang c10 lower bound = min_L(D⊥) - max_rank_in_type. "
            "Pencil c10 lower bound = min_rank_in_type (under N^2=0 assumption). "
            "Pencil is redundant when Wang already implies at least as tight a bound. "
            "The comparison is conservative: pencil may need N^2=0 which may not hold "
            "for all rank types; and non-idempotent W may reduce the pencil bound."
        ),
    }
    
    out = ODIR / "all_types_wang_comparison.json"
    with open(out, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nSaved: {out}")
    print(f"Elapsed: {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
