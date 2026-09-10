#!/usr/bin/env python3
"""Compare a rep10 row core with saved rep2/rep16 supports.

Two comparisons are useful:
1. actual-core rows: do saved supports violate the same subspaces that appear in
   the rep10 core?  These rows are part of the full Wang LUT for every support.
2. analogous row types: for each target support's fixed prefix, take all Wang
   rows through that prefix having the same (dimension, lower-bound) pairs as
   the rep10 core.  This asks whether the core's mathematical row types already
   fail to distinguish reps 2/16.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rep10_mus_core_cp import branch_points, collect_rows, parse_ints, row_summary  # noqa: E402
from wang_capacity_cnf_e11_fixed import parse_dims  # noqa: E402
from wang_capacity_lazy import in_rowspace, matrix_rank_of_mask, subspace_points_from_basis, unpack_basis  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def load_support(path: Path) -> list[int]:
    data = json.loads(path.read_text())
    if 'support' in data and data['support'] is not None:
        return [int(x) for x in data['support']]
    if 'nonzero_solution' in data:
        return [int(x) for x, v in data['nonzero_solution'].items() if int(v)]
    raise ValueError(f'no support in {path}')


def check_keys(keys: Sequence[int], lut: dict[int, int], support: Sequence[int], rank_s: int):
    supp = list(map(int, support))
    violations = []
    slack_hist = Counter(); occ_hist = Counter(); by_dim = Counter(); by_lb = Counter(); tight = 0
    for key in keys:
        key = int(key)
        lb = int(lut[key])
        cap = rank_s - lb
        basis = unpack_basis(key)
        occ = sum(1 for p in supp if in_rowspace(p, basis, n=9))
        slack = cap - occ
        slack_hist[slack] += 1; occ_hist[occ] += 1; by_dim[key & 0xF] += 1; by_lb[lb] += 1
        if slack == 0:
            tight += 1
        if slack < 0:
            violations.append({'key': key, 'dim': key & 0xF, 'lb': lb, 'cap': cap, 'occupancy': occ, 'excess': -slack, 'basis': list(basis)})
    violations.sort(key=lambda v: (v['excess'], v['lb'], v['occupancy'], -v['dim']), reverse=True)
    return {
        'rows_checked': len(keys),
        'rows_by_dim': dict(sorted(by_dim.items())),
        'rows_by_lb': dict(sorted(by_lb.items())),
        'violation_count': len(violations),
        'max_excess': 0 if not violations else max(v['excess'] for v in violations),
        'tight_count': tight,
        'slack_hist': dict(sorted(slack_hist.items())),
        'occupancy_hist': dict(sorted(occ_hist.items())),
        'violation_head': violations[:20],
    }


def analogous_keys(lut: dict[int, int], fixed: Sequence[int], groups: set[tuple[int, int]], rank_s: int):
    # Collect active non-vacuous rows through the target fixed prefix, then keep
    # the same (dim, lb) pairs as the source core.
    include_dims = set()
    through_dims = {d for d, _ in groups}
    fixed0, excluded, pts, idx = branch_points([p for p in fixed if p != 1], False)
    rows, meta = collect_rows(lut, rank_s=rank_s, fixed=fixed0, pts=pts, include_dims=include_dims, through_fixed_dims=through_dims)
    chosen = [r for r in rows if (int(r['dim']), int(r['lb'])) in groups]
    return [int(r['key']) for r in chosen], row_summary(chosen), meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--core', type=Path, required=True)
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--support', type=Path, action='append', required=True)
    ap.add_argument('--fixed', action='append', required=True, help='fixed prefix like 1,2; one per support')
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    if len(args.support) != len(args.fixed):
        raise ValueError('need one --fixed per --support')
    t0 = time.time()
    lut, lmeta = load_lut(args.lut)
    core = json.loads(args.core.read_text())
    core_keys = [int(k) for k in core['core_keys']]
    groups = {(int(k) & 0xF, int(lut[int(k)])) for k in core_keys}
    per = []
    for spath, fspec in zip(args.support, args.fixed):
        fixed = [int(x) for x in fspec.replace(';', ',').split(',') if x.strip()]
        support = load_support(spath)
        actual = check_keys(core_keys, lut, support, args.rank)
        akeys, asummary, ameta = analogous_keys(lut, fixed, groups, args.rank)
        analog = check_keys(akeys, lut, support, args.rank)
        per.append({
            'support_path': str(spath),
            'fixed': fixed,
            'support': support,
            'support_size': len(support),
            'support_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in support).items())),
            'support_rank1_count': sum(1 for p in support if matrix_rank_of_mask(p)==1),
            'actual_rep10_core_rows': actual,
            'analogous_through_fixed_row_summary': asummary,
            'analogous_collect_meta': ameta,
            'analogous_same_dim_lb_rows': analog,
        })
    payload = {
        'problem': 'compare rep10 row core with saved supports',
        'field': 'F2',
        'rank_s': args.rank,
        'core_path': str(args.core),
        'core_row_count': len(core_keys),
        'core_dim_lb_groups': sorted([list(g) for g in groups]),
        'core_summary': core.get('final_row_summary') or core.get('core_summary'),
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'comparisons': per,
        'total_elapsed_sec': time.time() - t0,
        'meaning': 'If supports satisfy analogous row types but violate actual rep10-core rows, the row types alone do not transfer; full Wang-table/coupled-slot information is needed.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    short = {'core_groups': payload['core_dim_lb_groups'], 'comparisons': []}
    for c in per:
        short['comparisons'].append({
            'support_path': c['support_path'],
            'fixed': c['fixed'],
            'support_rank_hist': c['support_rank_hist'],
            'actual_core_violations': c['actual_rep10_core_rows']['violation_count'],
            'actual_core_max_excess': c['actual_rep10_core_rows']['max_excess'],
            'analog_rows': c['analogous_same_dim_lb_rows']['rows_checked'],
            'analog_violations': c['analogous_same_dim_lb_rows']['violation_count'],
            'analog_tight_count': c['analogous_same_dim_lb_rows']['tight_count'],
        })
    print(json.dumps(short | {'out': str(args.out)}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
