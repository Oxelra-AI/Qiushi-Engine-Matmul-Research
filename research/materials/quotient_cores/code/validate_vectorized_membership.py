#!/usr/bin/env python3
"""Stratified/random validation of vectorized Wang row membership.

Compares the highest-set-bit vectorized membership routine against exact
subspace enumeration on a sampled set of expanded Wang LUT rows and points.
"""
from __future__ import annotations

import argparse
import json
import pickle
import random
import sys
import time
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from precompute_skeleton_system import pack_bases_numpy, vectorized_membership  # noqa: E402
from wang_capacity_lazy import matrix_rank_of_mask, subspace_points_from_basis, unpack_basis  # noqa: E402


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--seed', type=int, default=23001)
    ap.add_argument('--random-rows', type=int, default=300)
    ap.add_argument('--random-hr-points', type=int, default=80)
    args = ap.parse_args()

    with args.lut.open('rb') as f:
        payload = pickle.load(f)
    lut = payload['lut']
    keys = list(lut.keys())
    n = len(keys)
    rng = random.Random(args.seed)

    by_dim: dict[int, list[int]] = {d: [] for d in range(10)}
    for idx, key in enumerate(keys):
        d = int(key) & 0xF
        if len(by_dim[d]) < 20:
            by_dim[d].append(idx)
        if all(len(v) >= 20 for v in by_dim.values()):
            break

    row_indices = {0, 1, 2, n - 3, n - 2, n - 1, n // 7, n // 3, n // 2, 2 * n // 3, 6 * n // 7}
    for lst in by_dim.values():
        row_indices.update(lst)
    row_indices.update(rng.sample(range(n), min(args.random_rows, n)))
    row_indices = sorted(row_indices)

    r1 = [p for p in range(1, 512) if matrix_rank_of_mask(p) == 1]
    hr = [p for p in range(1, 512) if matrix_rank_of_mask(p) > 1]
    special = [25, 26, 34, 52, 193, 194, 217, 218, 278, 304,
               19, 21, 23, 33, 41, 160, 274, 400, 402]
    points = sorted(set(r1 + rng.sample(hr, min(args.random_hr_points, len(hr))) + special))

    bases = np.zeros((len(row_indices), 9), dtype=np.uint16)
    for ii, idx in enumerate(row_indices):
        for j, v in enumerate(unpack_basis(int(keys[idx]))):
            bases[ii, j] = v

    mismatches = []
    comparisons = 0
    t0 = time.time()
    for p in points:
        fast = vectorized_membership(bases, int(p))
        for ii, idx in enumerate(row_indices):
            slow = int(p) in subspace_points_from_basis(unpack_basis(int(keys[idx])))
            if bool(fast[ii]) != bool(slow):
                mismatches.append({
                    'row_index': int(idx),
                    'key': int(keys[idx]),
                    'dim': int(keys[idx]) & 0xF,
                    'point': int(p),
                    'fast': bool(fast[ii]),
                    'slow': bool(slow),
                })
                if len(mismatches) >= 50:
                    break
            comparisons += 1
        if len(mismatches) >= 50:
            break

    row_dim_hist = {str(d): sum(1 for idx in row_indices if (int(keys[idx]) & 0xF) == d) for d in range(10)}
    res = {
        'seed': args.seed,
        'row_count': len(row_indices),
        'point_count': len(points),
        'comparisons': comparisons,
        'mismatch_count': len(mismatches),
        'mismatches_head': mismatches,
        'row_dim_hist': row_dim_hist,
        'elapsed_sec': time.time() - t0,
        'meaning': 'Corrected highest-set-bit vectorized membership compared against exact subspace enumeration on stratified/random Wang rows and points.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(res, indent=2, sort_keys=True) + '\n')
    print(json.dumps(res, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
