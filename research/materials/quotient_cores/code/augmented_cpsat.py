#!/usr/bin/env python3
r"""analysis: augmented E11 core CP-SAT with dual-basis overlap constraints.

For every pair of rank-9 contractions q1, q2 with N = M1^{-1} + M2^{-1}
having rank r, IF both contractions are saturated (w(q1) = w(q2) = 9),
THEN their overlap k = |I_{q1} cap I_{q2}| <= floor((18-r)/2).

This gives 576 new conditional constraints for N-rank-9 pairs (bound k<=4)
and 1512 for N-rank-6 pairs (bound k<=6), of which 1676 are strictly
stronger than the corresponding Wang occupation rows.

The model uses the distinct 19-point Boolean support x_p for p in {1..255}
plus the full Wang occupation table and contraction lower bounds, augmented
with these dual-basis overlap constraints encoded as:
  w(q1) != 9 OR w(q2) != 9 OR common(q1,q2) <= db_bound
using CP-SAT OnlyEnforceIf reification.
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
from core_capacity_all_mip import enumerate_subspace_keys
from wang_capacity_lazy import (
    subspace_points_from_basis, unpack_basis, pack_basis, rref_basis,
)

from ortools.sat.python import cp_model

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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path,
                        default=ROOT / 'workspace/data/dual_basis/augmented_cpsat.json')
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--threshold-L', type=int, default=12,
                        help='Minimum L for Wang rows to include (12=complete)')
    parser.add_argument('--n-rank-min', type=int, default=9,
                        help='Minimum N-rank for dual-basis constraints (9=strongest only)')
    parser.add_argument('--workers', type=int, default=8)
    args = parser.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    # Build core tensor and contractions
    T_full = build_matmul_tensor_f2()
    T_core = T_full[1:, :, :]
    na = 8

    contractions = {}
    for q in range(1, 1 << na):
        M = contraction_matrix(T_core, q)
        rk = mat_rank_f2(M)
        inv = gf2_mat_inv(M) if rk == 9 else None
        contractions[q] = {'M': M, 'rank': rk, 'M_inv': inv}

    rk9_qs = sorted(q for q, info in contractions.items() if info['rank'] == 9)

    # Compute N-rank for all rank-9 pairs
    pair_data = []
    for i, q1 in enumerate(rk9_qs):
        for q2 in rk9_qs[i+1:]:
            M1_inv = contractions[q1]['M_inv']
            M2_inv = contractions[q2]['M_inv']
            N = (M1_inv + M2_inv) % 2
            N_rank = mat_rank_f2(N)
            if N_rank >= args.n_rank_min:
                db_bound = (18 - N_rank) // 2
                pair_data.append((q1, q2, N_rank, db_bound))

    print(f"Dual-basis pairs with N-rank >= {args.n_rank_min}: {len(pair_data)}")

    # Load LUT
    with LUT_PATH.open("rb") as f:
        payload = pickle.load(f)
    lut = {int(k): int(v) for k, v in payload["lut"].items()}
    core = CoreQuotient(1)

    # Enumerate all core subspaces
    print("Enumerating core subspaces...")
    keys8 = enumerate_subspace_keys(8)
    print(f"  dim 1: {sum(1 for k in keys8 if k & 0xF == 1)}")

    # Build the CP-SAT model
    model = cp_model.CpModel()

    # Boolean support variables: x[p] for p in 1..255
    x = {}
    for p in range(1, 256):
        x[p] = model.NewBoolVar(f'x_{p}')

    # Total = 19 (distinct points)
    model.Add(sum(x.values()) == 19)

    # Contraction weights
    w = {}
    for q in range(1, 256):
        pts_q = [p for p in range(1, 256) if (p & q).bit_count() & 1]
        w[q] = sum(x[p] for p in pts_q)

    # Wang occupation constraints
    wang_rows_added = 0
    wang_by_dim = Counter()
    s = 19  # rank parameter
    for key8 in keys8:
        key9 = core.key9_from_key8(key8)
        L = lut[key9]
        if L < args.threshold_L:
            continue
        cap = s - L
        if cap < 0:
            model.Add(sum(x.values()) == 0)  # impossible
            break
        dim = key8 & 0xF
        pts = subspace_points_from_basis(unpack_basis(key8))
        occ = sum(x[p] for p in pts if p in x)
        model.Add(occ <= cap)
        wang_rows_added += 1
        wang_by_dim[dim] += 1

    print(f"Wang rows (L>={args.threshold_L}): {wang_rows_added}")

    # Contraction lower bounds
    clb_added = 0
    for q in range(1, 256):
        rk = contractions[q]['rank']
        if rk > 0:
            model.Add(w[q] >= rk)
            clb_added += 1

    print(f"Contraction lower bounds: {clb_added}")

    # Dual-basis overlap constraints
    db_added = 0
    for q1, q2, N_rank, db_bound in pair_data:
        # Common points between q1 and q2: those where both q1(p)=1 and q2(p)=1
        common_pts = [p for p in range(1, 256)
                      if (p & q1).bit_count() & 1 and (p & q2).bit_count() & 1]
        common_var = sum(x[p] for p in common_pts)

        # Conditional constraint: IF w(q1)=9 AND w(q2)=9 THEN common <= db_bound
        # Encoding: we introduce Boolean indicators for saturation
        sat_q1 = model.NewBoolVar(f'sat_{q1}_{q2}_q1')
        sat_q2 = model.NewBoolVar(f'sat_{q1}_{q2}_q2')

        # sat_q1 = 1 iff w(q1) = 9
        model.Add(w[q1] == 9).OnlyEnforceIf(sat_q1)
        model.Add(w[q1] != 9).OnlyEnforceIf(sat_q1.Not())

        # sat_q2 = 1 iff w(q2) = 9
        model.Add(w[q2] == 9).OnlyEnforceIf(sat_q2)
        model.Add(w[q2] != 9).OnlyEnforceIf(sat_q2.Not())

        # If both saturated, then common <= db_bound
        both_sat = model.NewBoolVar(f'both_sat_{q1}_{q2}')
        model.AddBoolAnd([sat_q1, sat_q2]).OnlyEnforceIf(both_sat)
        model.AddBoolOr([sat_q1.Not(), sat_q2.Not()]).OnlyEnforceIf(both_sat.Not())

        model.Add(common_var <= db_bound).OnlyEnforceIf(both_sat)
        db_added += 1

    print(f"Dual-basis constraints: {db_added}")

    build_sec = time.time() - t0
    print(f"Build time: {build_sec:.1f}s")

    # Solve
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.timeout
    solver.parameters.num_workers = args.workers

    # Add hint from best known near-miss
    hint_support = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]
    for p in range(1, 256):
        model.AddHint(x[p], 1 if p in hint_support else 0)

    status = solver.Solve(model)
    status_name = solver.StatusName(status)
    solve_sec = solver.WallTime()

    print(f"Status: {status_name}, solve: {solve_sec:.1f}s")

    solution = None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        solution = sorted(p for p in range(1, 256) if solver.Value(x[p]))
        print(f"Solution support ({len(solution)} points): {solution}")
        # Quick violation scan
        viol_count = 0
        for key8 in keys8:
            key9 = core.key9_from_key8(key8)
            L = lut[key9]
            cap = s - L
            pts = subspace_points_from_basis(unpack_basis(key8))
            occ = sum(1 for p in pts if p in set(solution))
            if occ > cap:
                viol_count += 1
        print(f"Complete Wang violations: {viol_count}")

    result = {
        'schema': 'augmented_cpsat_v1',
        'elapsed_sec': round(time.time() - t0, 3),
        'build_sec': round(build_sec, 3),
        'solve_sec': round(solve_sec, 3),
        'status': status_name,
        'threshold_L': args.threshold_L,
        'n_rank_min': args.n_rank_min,
        'wang_rows': wang_rows_added,
        'wang_by_dim': {str(k): v for k, v in sorted(wang_by_dim.items())},
        'contraction_lower_bounds': clb_added,
        'dual_basis_constraints': db_added,
        'solution': solution,
    }

    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(f"Saved {args.out}")


if __name__ == '__main__':
    main()
