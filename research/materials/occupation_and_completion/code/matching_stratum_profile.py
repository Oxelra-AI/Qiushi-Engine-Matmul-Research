#!/usr/bin/env python3
"""Full-LUT residual profile for anchored matching strata.

For every whole matching representative from matching_strata.py, compute
how Wang occupation capacities change after fixing exactly those rank-1 points.
This exposes immediate rank-1-only contradictions and the size of the residual
higher-rank cardinality system without invoking CP-SAT.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from precompute_skeleton_system import pack_bases_numpy, vectorized_multi_membership  # noqa: E402
from wang_capacity_lazy import matrix_rank_of_mask  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def all_representatives(classification: dict) -> list[dict]:
    out = []
    for k_s, arr in classification['representatives_by_k'].items():
        for rec in arr:
            r = dict(rec)
            r['k'] = int(k_s)
            out.append(r)
    out.sort(key=lambda r: (r['k'], tuple(r['canonical'])))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--classification', type=Path, default=Path('data/matching_strata/anchored_matching_strata.json'))
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()

    t0 = time.time()
    classification = json.loads(args.classification.read_text())
    reps = all_representatives(classification)
    lut, lmeta = load_lut(args.lut)
    key_list = [int(k) for k in lut.keys()]
    dims = np.array([int(k) & 0xF for k in key_list], dtype=np.int16)
    lbs_arr = np.array([int(v) for v in lut.values()], dtype=np.int16)
    caps = int(args.rank) - lbs_arr
    total_points = (np.left_shift(np.ones_like(dims, dtype=np.int32), dims.astype(np.int32)) - 1).astype(np.int32)
    print(f'loaded LUT {len(lut):,}; packing bases...', flush=True)
    bases, _, _ = pack_bases_numpy(lut)
    rank1_pts = [p for p in range(1, 512) if matrix_rank_of_mask(p) == 1]
    print(f'computing all-rank1 row occupancy for {len(rank1_pts)} rank-1 points...', flush=True)
    all_r1_occ = vectorized_multi_membership(bases, rank1_pts).astype(np.int16)
    high_vars_in_row = total_points.astype(np.int32) - all_r1_occ.astype(np.int32)

    records = []
    by_k_status = Counter()
    for idx, rec in enumerate(reps):
        matching = [int(p) for p in rec['canonical']]
        occ = vectorized_multi_membership(bases, matching).astype(np.int16)
        residual = caps - occ
        bad = np.nonzero(residual < 0)[0]
        nonv = np.nonzero(high_vars_in_row > residual.astype(np.int32))[0]
        tight0 = np.nonzero(residual == 0)[0]
        low1 = np.nonzero(residual <= 1)[0]
        low2 = np.nonzero(residual <= 2)[0]
        by_dim_nonv = Counter(int(dims[i]) for i in nonv)
        by_dim_bad = Counter(int(dims[i]) for i in bad)
        by_dim_res0 = Counter(int(dims[i]) for i in tight0)
        target_hr = int(args.rank) - len(matching)
        rec_out = {
            'idx': idx,
            'k': len(matching),
            'canonical': matching,
            'enumerated_members': int(rec.get('enumerated_members', rec.get('orbit_image_count', 0))),
            'orbit_image_count': int(rec.get('orbit_image_count', 0)),
            'target_higher_rank_count': target_hr,
            'rank1_only_violation_count': int(len(bad)),
            'rank1_only_max_excess': int(max(((-int(residual[i])) for i in bad), default=0)),
            'rank1_only_bad_by_dim': dict(sorted(by_dim_bad.items())),
            'rank1_only_bad_head': [
                {'key': int(key_list[i]), 'dim': int(dims[i]), 'lb': int(lbs_arr[i]), 'cap_before_rank1': int(caps[i]), 'fixed_rank1_occupancy': int(occ[i]), 'excess': int(occ[i] - caps[i])}
                for i in list(bad[:30])
            ],
            'nonvacuous_high_constraint_count': int(len(nonv)),
            'nonvacuous_high_constraints_by_dim': dict(sorted(by_dim_nonv.items())),
            'residual_cap_zero_count': int(len(tight0)),
            'residual_cap_zero_by_dim': dict(sorted(by_dim_res0.items())),
            'residual_cap_le1_count': int(len(low1)),
            'residual_cap_le2_count': int(len(low2)),
            'min_residual_cap': int(residual.min()),
            'residual_cap_hist_head': {str(k): int(v) for k, v in sorted(Counter(int(x) for x in residual).items())[:20]},
        }
        rec_out['rank1_only_status'] = 'IMPOSSIBLE' if len(bad) else 'OK'
        by_k_status[(rec_out['k'], rec_out['rank1_only_status'])] += 1
        records.append(rec_out)
        print(f"[{idx+1:02d}/{len(reps)}] k={rec_out['k']} can={matching}: rank1-only {rec_out['rank1_only_status']}, nonv={rec_out['nonvacuous_high_constraint_count']:,}", flush=True)

    payload = {
        'problem': 'residual Wang capacity profiles for fixed anchored matching strata',
        'field': 'F2',
        'classification_path': str(args.classification),
        'rank_s': int(args.rank),
        'strata_count': len(records),
        'rank1_only_status_by_k': {f'k{k}_{s}': c for (k, s), c in sorted(by_k_status.items())},
        'records': records,
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'elapsed_sec': time.time() - t0,
        'meaning': 'Rank-1-only impossible strata are eliminated by fixed selected rank-1 points alone. Otherwise nonvacuous_high_constraint_count estimates the full fixed-matching high-rank cardinality system size.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'strata_count': len(records),
        'rank1_only_status_by_k': payload['rank1_only_status_by_k'],
        'elapsed_sec': payload['elapsed_sec'],
        'out': str(args.out),
    }, indent=2, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
