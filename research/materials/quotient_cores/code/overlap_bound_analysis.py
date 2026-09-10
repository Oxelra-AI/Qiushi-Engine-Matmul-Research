#!/usr/bin/env python3
r"""analysis: overlap bound analysis for rank-9 N-rank-9 contraction pairs.

The dual-basis constraint gives: for two rank-9 saturated contractions q1, q2,
if N = M1^{-1} + M2^{-1} has rank r, then
    |I_{q1} cap I_{q2}| <= floor((18-r)/2).

For a 19-point support with w(q1) = w(q2) = 9 (both saturated),
the overlap k = |I_{q1} cap I_{q2}| = (9+9-w(q1 xor q2))/2 = 9 - w(q3)/2,
where q3 = q1 xor q2.

Wang gives k+1 = occ(ker(q1) cap ker(q2)) <= 19-L(U), so k <= 18-L(U).

This script computes how many N-rank-9 pairs give STRICTLY stronger bounds
than Wang, and what the combined constraint system looks like.
"""
from __future__ import annotations

import argparse
import json
import pickle
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import numpy as np

import sys
SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    build_matmul_tensor_f2,
    contraction_matrix,
    mat_rank_f2,
)
from core_capacity_from_wang_lut import CoreQuotient
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis

ROOT = Path("research/research_record")
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"


def gf2_mat_inv(M: np.ndarray) -> Optional[np.ndarray]:
    n = M.shape[0]
    assert M.shape == (n, n)
    aug = []
    for i in range(n):
        row = 0
        for j in range(n):
            if int(M[i, j]) & 1:
                row |= 1 << j
        row |= 1 << (n + i)
        aug.append(row)
    for col in range(n):
        pivot = None
        for r in range(col, n):
            if (aug[r] >> col) & 1:
                pivot = r
                break
        if pivot is None:
            return None
        aug[col], aug[pivot] = aug[pivot], aug[col]
        for r in range(n):
            if r != col and (aug[r] >> col) & 1:
                aug[r] ^= aug[col]
    inv = np.zeros((n, n), dtype=np.uint8)
    for i in range(n):
        for j in range(n):
            if (aug[i] >> (n + j)) & 1:
                inv[i, j] = 1
    return inv


def gf2_rank(M: np.ndarray) -> int:
    return mat_rank_f2(M)


def load_lut() -> Dict[int, int]:
    with LUT_PATH.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path,
                        default=ROOT / 'workspace/data/dual_basis/overlap_bounds.json')
    args = parser.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()

    # Build core tensor
    T_full = build_matmul_tensor_f2()
    T_core = T_full[1:, :, :]  # E11 core
    na = 8

    # Compute all contractions
    contractions = {}
    for q in range(1, 1 << na):
        M = contraction_matrix(T_core, q)
        rk = gf2_rank(M)
        inv = gf2_mat_inv(M) if rk == 9 else None
        contractions[q] = {'M': M, 'rank': rk, 'M_inv': inv}

    rk9_qs = sorted(q for q, info in contractions.items() if info['rank'] == 9)
    print(f"Rank-9 contractions: {len(rk9_qs)}")

    # Load Wang LUT and build core quotient
    lut = load_lut()
    core = CoreQuotient(1)  # E11 pivot = 1

    # For each pair of rank-9 contractions, compute N-rank and compare with Wang
    pair_results = []
    strictly_stronger = 0
    wang_eq = 0
    wang_stronger = 0
    n_rank_hist = Counter()
    improvement_hist = Counter()  # (dual_basis_bound, wang_bound) -> count

    for i, q1 in enumerate(rk9_qs):
        for q2 in rk9_qs[i+1:]:
            M1_inv = contractions[q1]['M_inv']
            M2_inv = contractions[q2]['M_inv']
            N = (M1_inv + M2_inv) % 2
            N_rank = gf2_rank(N)
            n_rank_hist[N_rank] += 1

            # Dual-basis bound on overlap
            db_bound = (18 - N_rank) // 2

            # Wang bound: L for the primal 6-dim subspace U = ker(q1) cap ker(q2)
            # U is the annihilator of span(q1, q2) in the core A-space.
            # To look up in the LUT, we need the key for U in F_2^9 (full tensor A-space).
            # The core key for U: find the 6-dim subspace of F_2^8 annihilated by q1 and q2.
            # Then convert to F_2^9 key via the core quotient.

            # Compute the 6-dim primal subspace U = {p in F_2^8: q1(p)=0, q2(p)=0}
            # Actually, p ranges over 1..255 (nonzero elements of F_2^8).
            # Points in U: those with q1(p)=0 AND q2(p)=0
            u_points = []
            for p in range(1, 1 << na):
                inner1 = (p & q1).bit_count() & 1
                inner2 = (p & q2).bit_count() & 1
                if inner1 == 0 and inner2 == 0:
                    u_points.append(p)

            # Find the RREF key for this subspace in the core
            from fixed_A_saturation import rref_basis as rref_basis_fn
            u_basis8 = rref_basis_fn(u_points, 8)
            dim_u = len(u_basis8)

            # Convert to 9-dim key via core quotient
            key8 = 0
            for idx, b in enumerate(sorted(u_basis8)):
                key8 |= b << (4 + 16 * idx)
            key8 |= dim_u  # low 4 bits = dimension
            key9 = core.key9_from_key8(key8)
            L_U = lut.get(key9, None)

            if L_U is not None:
                wang_bound = 18 - L_U  # k <= 18 - L
                improvement_hist[(db_bound, wang_bound)] += 1
                if db_bound < wang_bound:
                    strictly_stronger += 1
                elif db_bound == wang_bound:
                    wang_eq += 1
                else:
                    wang_stronger += 1

                if N_rank >= 6 and db_bound < wang_bound:
                    q3 = q1 ^ q2
                    q3_rank = contractions.get(q3, {}).get('rank', None)
                    pair_results.append({
                        'q1': q1, 'q2': q2, 'q3': q3,
                        'N_rank': int(N_rank),
                        'db_bound': int(db_bound),
                        'wang_L': int(L_U),
                        'wang_bound': int(wang_bound),
                        'improvement': int(wang_bound - db_bound),
                        'q3_rank': q3_rank,
                    })
            else:
                # LUT miss (shouldn't happen for valid subspace)
                pass

    elapsed = time.time() - t0

    # Check the best near-miss support against new constraints
    best_support = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]
    violations_new = []
    total_new_constraints = 0
    for rec in pair_results:
        q1, q2 = rec['q1'], rec['q2']
        # Compute weights for this support
        w1 = sum(1 for p in best_support if (p & q1).bit_count() & 1)
        w2 = sum(1 for p in best_support if (p & q2).bit_count() & 1)
        q3 = q1 ^ q2
        w3 = sum(1 for p in best_support if (p & q3).bit_count() & 1)
        if w1 == 9 and w2 == 9:
            overlap = (18 - w3) // 2
            db_bound = rec['db_bound']
            total_new_constraints += 1
            if overlap > db_bound:
                violations_new.append({
                    'q1': q1, 'q2': q2,
                    'N_rank': rec['N_rank'],
                    'overlap': overlap,
                    'db_bound': db_bound,
                    'wang_bound': rec['wang_bound'],
                    'w3': w3,
                })

    # Also check ALL N-rank-9 pairs (not just those with strictly-stronger Wang)
    all_rk9_violations = []
    all_rk9_new_tested = 0
    for i, q1 in enumerate(rk9_qs):
        for q2 in rk9_qs[i+1:]:
            M1_inv = contractions[q1]['M_inv']
            M2_inv = contractions[q2]['M_inv']
            N = (M1_inv + M2_inv) % 2
            N_rank = gf2_rank(N)
            if N_rank < 9:
                continue

            # For this support, check saturation and overlap
            w1 = sum(1 for p in best_support if (p & q1).bit_count() & 1)
            w2 = sum(1 for p in best_support if (p & q2).bit_count() & 1)
            if w1 == 9 and w2 == 9:
                q3 = q1 ^ q2
                w3 = sum(1 for p in best_support if (p & q3).bit_count() & 1)
                overlap = (18 - w3) // 2
                all_rk9_new_tested += 1
                if overlap > 4:  # N-rank 9 bound
                    all_rk9_violations.append({
                        'q1': q1, 'q2': q2,
                        'overlap': overlap,
                        'w3': w3,
                    })

    result = {
        'schema': 'overlap_bound_analysis_v1',
        'elapsed_sec': round(elapsed, 3),
        'rank9_count': len(rk9_qs),
        'total_pairs': len(rk9_qs) * (len(rk9_qs) - 1) // 2,
        'N_rank_histogram': {str(k): v for k, v in sorted(n_rank_hist.items())},
        'general_overlap_bounds': {
            'N_rank_3': '(18-3)//2 = 7',
            'N_rank_6': '(18-6)//2 = 6',
            'N_rank_9': '(18-9)//2 = 4',
        },
        'wang_comparison': {
            'strictly_stronger_than_wang': strictly_stronger,
            'equal_to_wang': wang_eq,
            'weaker_than_wang': wang_stronger,
        },
        'improvement_histogram': {str(k): v for k, v in sorted(improvement_hist.items())},
        'strictly_stronger_details_count': len(pair_results),
        'strictly_stronger_sample': pair_results[:30],
        'near_miss_support': best_support,
        'near_miss_new_constraint_tests': total_new_constraints,
        'near_miss_new_violations': violations_new,
        'near_miss_rk9_pair_tests': all_rk9_new_tested,
        'near_miss_rk9_pair_violations': all_rk9_violations,
    }

    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(f"\nStrictly stronger: {strictly_stronger}/{len(rk9_qs)*(len(rk9_qs)-1)//2}")
    print(f"Equal: {wang_eq}, Wang stronger: {wang_stronger}")
    print(f"Near-miss violations from new constraints: {len(violations_new)}")
    print(f"Near-miss rk9 pair violations: {len(all_rk9_violations)} / {all_rk9_new_tested} tested")
    print(f"Saved {args.out}")


if __name__ == '__main__':
    main()
