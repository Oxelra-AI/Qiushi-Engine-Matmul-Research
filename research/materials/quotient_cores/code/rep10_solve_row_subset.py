#!/usr/bin/env python3
"""Solve selected dim/lb row subsets of the fixed-E11/rep10 Wang family by CP-SAT."""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rep10_mus_core_cp import branch_points, collect_rows, parse_ints, row_summary, solve_with_assumptions  # noqa: E402
from wang_capacity_cnf_e11_fixed import parse_dims  # noqa: E402
from wang_capacity_lazy import matrix_rank_of_mask  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def parse_group_specs(spec: str) -> set[tuple[int, int]]:
    out = set()
    for part in spec.replace(';', ',').split(','):
        part = part.strip()
        if not part:
            continue
        if ':' in part:
            d, lb = part.split(':', 1)
        elif '/' in part:
            d, lb = part.split('/', 1)
        elif '_lb' in part and part.startswith('d'):
            a, b = part[1:].split('_lb', 1)
            d, lb = a, b.split('_', 1)[0]
        else:
            raise ValueError(f'bad group spec {part!r}; use dim:lb')
        out.add((int(d), int(lb)))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', default='10')
    ap.add_argument('--exclude-second-orbits-before', action='store_true')
    ap.add_argument('--include-dims', default='1')
    ap.add_argument('--through-fixed-dims', default='4,6')
    ap.add_argument('--groups', required=True, help='comma-separated dim:lb entries, e.g. 4:17,6:12,6:15')
    ap.add_argument('--time-limit', type=float, default=600.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    t0 = time.time()
    lut, lmeta = load_lut(args.lut)
    fixed_extra = parse_ints(args.fixed_extra)
    fixed, excluded, pts, idx = branch_points(fixed_extra, args.exclude_second_orbits_before)
    all_rows, collect_meta = collect_rows(lut, rank_s=args.rank, fixed=fixed, pts=pts,
                                          include_dims=parse_dims(args.include_dims),
                                          through_fixed_dims=parse_dims(args.through_fixed_dims))
    want = parse_group_specs(args.groups)
    rows = [r for r in all_rows if (int(r['dim']), int(r['lb'])) in want]
    res = solve_with_assumptions(rows, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                 time_limit=args.time_limit, workers=args.workers, use_assumptions=False)
    payload = {
        'problem': 'rep10 fixed-E11 selected dim/lb row subset CP-SAT',
        'field': 'F2',
        'rank_s': args.rank,
        'fixed_points': fixed,
        'fixed_extra': fixed_extra,
        'groups': sorted([list(x) for x in want]),
        'include_dims': sorted(parse_dims(args.include_dims)),
        'through_fixed_dims': sorted(parse_dims(args.through_fixed_dims)),
        'row_summary': row_summary(rows),
        'result': {k: res[k] for k in ['status','elapsed_sec','solver_walltime','conflicts','branches']},
        'support': res.get('support'),
        'support_rank_hist': None if res.get('support') is None else dict(sorted(Counter(matrix_rank_of_mask(p) for p in res['support']).items())),
        'support_rank1_count': None if res.get('support') is None else sum(1 for p in res['support'] if matrix_rank_of_mask(p)==1),
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'collect_meta': collect_meta,
        'total_elapsed_sec': time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: payload[k] for k in ['groups','row_summary','result','support_rank_hist','support_rank1_count','out'] if k in payload} | {'out': str(args.out)}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
