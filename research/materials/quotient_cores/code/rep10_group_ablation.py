#!/usr/bin/env python3
"""Group-level ablation for the fixed-E11/rep10 Wang row family.

The goal is to replace the 14,478-row dim4+dim6 through-fixed rep10 formula by
much smaller scientifically interpretable row groups before CNF/DRAT replay.
A group here is a collection of Wang occupation rows, typically by dimension and
lower bound, kept or dropped as a unit.  The solver result is CP-SAT evidence;
formal use still requires a CNF encoding and independent DRAT verification.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Sequence

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


def group_key(row: dict, mode: str):
    if mode == 'dim':
        return f"d{row['dim']}"
    if mode == 'dim_lb':
        return f"d{row['dim']}_lb{row['lb']}_cap{row['cap_rem']}"
    if mode == 'dim_cap':
        return f"d{row['dim']}_cap{row['cap_rem']}"
    if mode == 'lb':
        return f"lb{row['lb']}_cap{row['cap_rem']}"
    raise ValueError(mode)


def solve_rows(rows: Sequence[dict], *, pts, idx, fixed, rank_s, time_limit, workers):
    res = solve_with_assumptions(rows, pts=pts, idx=idx, fixed=fixed, rank_s=rank_s,
                                 time_limit=time_limit, workers=workers, use_assumptions=False)
    return {k: res[k] for k in ['status', 'elapsed_sec', 'solver_walltime', 'conflicts', 'branches']}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', default='10')
    ap.add_argument('--exclude-second-orbits-before', action='store_true')
    ap.add_argument('--include-dims', default='1')
    ap.add_argument('--through-fixed-dims', default='4,6')
    ap.add_argument('--group-mode', default='dim_lb', choices=['dim','dim_lb','dim_cap','lb'])
    ap.add_argument('--time-limit', type=float, default=90.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--test-single-groups', action='store_true')
    ap.add_argument('--greedy-order', default='small_first', choices=['small_first','large_first','name'])
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()

    t0 = time.time()
    lut, lmeta = load_lut(args.lut)
    fixed_extra = parse_ints(args.fixed_extra)
    fixed, excluded, pts, idx = branch_points(fixed_extra, args.exclude_second_orbits_before)
    rows, collect_meta = collect_rows(lut, rank_s=args.rank, fixed=fixed, pts=pts,
                                      include_dims=parse_dims(args.include_dims),
                                      through_fixed_dims=parse_dims(args.through_fixed_dims))
    groups = defaultdict(list)
    for r in rows:
        groups[group_key(r, args.group_mode)].append(r)
    group_info = {g: row_summary(rs) for g, rs in groups.items()}

    all_res = solve_rows(rows, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                         time_limit=args.time_limit, workers=args.workers)
    single_results = {}
    if args.test_single_groups:
        for g in sorted(groups):
            single_results[g] = solve_rows(groups[g], pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                           time_limit=args.time_limit, workers=args.workers)
            print('single', g, single_results[g], flush=True)

    if args.greedy_order == 'small_first':
        order = sorted(groups, key=lambda g: (len(groups[g]), g))
    elif args.greedy_order == 'large_first':
        order = sorted(groups, key=lambda g: (-len(groups[g]), g))
    else:
        order = sorted(groups)

    active = set(groups)
    greedy_history = []
    for g in order:
        trial_groups = active - {g}
        trial_rows = [r for h in sorted(trial_groups) for r in groups[h]]
        res = solve_rows(trial_rows, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                         time_limit=args.time_limit, workers=args.workers)
        ent = {'try_remove': g, 'removed_row_count': len(groups[g]), 'trial_group_count': len(trial_groups),
               'trial_row_count': len(trial_rows), **res}
        if res['status'] == 'INFEASIBLE':
            active = trial_groups
            ent['decision'] = 'removed'
        else:
            ent['decision'] = 'kept'
        greedy_history.append(ent)
        print('greedy', ent, flush=True)

    final_rows = [r for h in sorted(active) for r in groups[h]]
    final_res = solve_rows(final_rows, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                           time_limit=args.time_limit, workers=args.workers)
    payload = {
        'problem': 'rep10 Wang row group ablation',
        'field': 'F2',
        'rank_s': args.rank,
        'fixed_points': fixed,
        'fixed_extra': fixed_extra,
        'exclude_second_orbits_before': args.exclude_second_orbits_before,
        'include_dims': sorted(parse_dims(args.include_dims)),
        'through_fixed_dims': sorted(parse_dims(args.through_fixed_dims)),
        'group_mode': args.group_mode,
        'variable_point_count': len(pts),
        'variable_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in pts).items())),
        'excluded_point_count': len(excluded),
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'collect_meta': collect_meta,
        'initial_row_summary': row_summary(rows),
        'group_count': len(groups),
        'group_info': group_info,
        'all_rows_result': all_res,
        'single_group_results': single_results,
        'greedy_order': order,
        'greedy_history': greedy_history,
        'active_groups': sorted(active),
        'final_row_summary': row_summary(final_rows),
        'final_result': final_res,
        'core_keys': [int(r['key']) for r in final_rows],
        'total_elapsed_sec': time.time() - t0,
        'meaning': 'CP-SAT row-group shrink evidence. Encode active core keys and DRAT-verify before proof use.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'all_rows_result': all_res,
        'active_groups': sorted(active),
        'final_row_summary': row_summary(final_rows),
        'final_result': final_res,
        'out': str(args.out),
        'total_elapsed_sec': payload['total_elapsed_sec'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
