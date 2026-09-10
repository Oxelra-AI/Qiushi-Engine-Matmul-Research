#!/usr/bin/env python3
"""Shrink a saved rep10 Wang row core from a JSON file.

Input JSON must contain `core_keys` (as produced by rep10_group_ablation.py or
rep10_mus_core_cp.py).  The script reconstructs the exact row semantics from the
Wang LUT, asks CP-SAT for a sufficient assumption core, optionally repeats, and
optionally does greedy deletion.  Outputs a new compact core JSON.
"""
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

from rep10_mus_core_cp import (  # noqa: E402
    branch_points,
    collect_rows,
    deletion_pass,
    parse_ints,
    representative_rows,
    row_summary,
    shrink_by_solver_core,
    solve_with_assumptions,
    write_core,
)
from wang_capacity_cnf_e11_fixed import parse_dims  # noqa: E402
from wang_capacity_lazy import matrix_rank_of_mask  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--in-core', type=Path, required=True)
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', default='10')
    ap.add_argument('--exclude-second-orbits-before', action='store_true')
    ap.add_argument('--include-dims', default='1')
    ap.add_argument('--through-fixed-dims', default='4,6')
    ap.add_argument('--time-limit', type=float, default=300.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--core-rounds', type=int, default=3)
    ap.add_argument('--deletion-passes', type=int, default=0)
    ap.add_argument('--deletion-block-size', type=int, default=1)
    ap.add_argument('--max-deletion-tests', type=int, default=None)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--preview-limit', type=int, default=80)
    args = ap.parse_args()

    t0 = time.time()
    payload_in = json.loads(args.in_core.read_text())
    seed_keys = {int(k) for k in payload_in['core_keys']}
    lut, lmeta = load_lut(args.lut)
    fixed_extra = parse_ints(args.fixed_extra)
    fixed, excluded, pts, idx = branch_points(fixed_extra, args.exclude_second_orbits_before)
    all_rows, collect_meta = collect_rows(lut, rank_s=args.rank, fixed=fixed, pts=pts,
                                          include_dims=parse_dims(args.include_dims),
                                          through_fixed_dims=parse_dims(args.through_fixed_dims))
    by_key = {int(r['key']): r for r in all_rows}
    missing = sorted(seed_keys - set(by_key))
    if missing:
        raise ValueError(f'{len(missing)} core keys are not active rows in selected family; first={missing[:5]}')
    rows = [by_key[k] for k in sorted(seed_keys)]
    core, hist = shrink_by_solver_core(rows, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                       time_limit=args.time_limit, workers=args.workers,
                                       rounds=args.core_rounds)
    deletion_history = []
    for p in range(args.deletion_passes):
        core, dh = deletion_pass(core, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                 time_limit=args.time_limit, workers=args.workers,
                                 block_size=args.deletion_block_size,
                                 max_tests=args.max_deletion_tests)
        core, hist2 = shrink_by_solver_core(core, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                            time_limit=args.time_limit, workers=args.workers,
                                            rounds=1)
        deletion_history.append({'pass': p+1, 'history': dh, 'post_core_history': hist2, 'rows_after': len(core)})
    final = solve_with_assumptions(core, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                   time_limit=args.time_limit, workers=args.workers, use_assumptions=False)
    meta = {
        'problem': 'rep10 saved-row-core CP-SAT shrink',
        'input_core': str(args.in_core),
        'input_core_row_count': len(rows),
        'field': 'F2',
        'rank_s': args.rank,
        'fixed_points': fixed,
        'fixed_extra': fixed_extra,
        'exclude_second_orbits_before': args.exclude_second_orbits_before,
        'include_dims': sorted(parse_dims(args.include_dims)),
        'through_fixed_dims': sorted(parse_dims(args.through_fixed_dims)),
        'variable_point_count': len(pts),
        'variable_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in pts).items())),
        'excluded_point_count': len(excluded),
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'selected_family_collect_meta': collect_meta,
        'initial_saved_core_summary': row_summary(rows),
        'core_solver_history': hist,
        'deletion_history': deletion_history,
        'final_check': {k: final[k] for k in ['status','elapsed_sec','solver_walltime','conflicts','branches']},
        'total_elapsed_sec': time.time() - t0,
        'meaning': 'Shrunk row-core candidate. CNF/DRAT verification is required before mathematical proof use.',
    }
    write_core(core, args.out, meta, args.preview_limit)
    print(json.dumps({
        'input_rows': len(rows),
        'core_rows': len(core),
        'core_history': hist,
        'deletion_passes': len(deletion_history),
        'core_summary': row_summary(core),
        'final_check': meta['final_check'],
        'out': str(args.out),
        'total_elapsed_sec': meta['total_elapsed_sec'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
