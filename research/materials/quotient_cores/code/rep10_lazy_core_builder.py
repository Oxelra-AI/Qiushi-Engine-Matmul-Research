#!/usr/bin/env python3
"""Lazy row-core builder for the fixed-E11/rep10 Wang support contradiction.

Starting from a tiny set of selected Wang rows, repeatedly solve the support
model, scan the candidate against a target row pool, and add violated rows (or
whole Stab(E11,rep10)-orbits of violated rows).  The result is a compact row set
that CP-SAT itself proves infeasible.  This is meant to expose the actual
combinatorial obstruction before CNF/DRAT replay.
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

from rep10_mus_core_cp import branch_points, collect_rows, parse_ints, row_summary, solve_with_assumptions  # noqa: E402
from rep10_solve_row_subset import parse_group_specs  # noqa: E402
from wang_capacity_cnf_e11_fixed import parse_dims  # noqa: E402
from wang_capacity_lazy import (  # noqa: E402
    in_rowspace,
    make_actions,
    matrix_rank_of_mask,
    transform_key,
    transform_mask,
    unpack_basis,
)


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def stabilizer_actions(fixed: Sequence[int]):
    return [img for img in make_actions() if all(transform_mask(int(p), img) == int(p) for p in fixed)]


def orbit_closure(seed_keys: set[int], pool_keys: set[int], fixed: Sequence[int]):
    actions = stabilizer_actions(fixed)
    closed = set(seed_keys)
    for key in list(seed_keys):
        basis = unpack_basis(int(key))
        for img in actions:
            k2 = int(transform_key(basis, img))
            if k2 in pool_keys:
                closed.add(k2)
    return closed


def parse_initial_keys(spec: str, pool_by_key: dict[int, dict]):
    if not spec.strip():
        return set()
    out = set()
    groups = parse_group_specs(spec)
    for k, r in pool_by_key.items():
        if (int(r['dim']), int(r['lb'])) in groups:
            out.add(k)
    return out


def support_violations(rows: Sequence[dict], support: Sequence[int]):
    supp = set(int(p) for p in support)
    viol = []
    for r in rows:
        occ = sum(1 for p in supp if in_rowspace(p, r['basis'], n=9))
        if occ > int(r['raw_cap']):
            v = {k: (list(val) if isinstance(val, tuple) else val) for k, val in r.items() if k != 'vars'}
            v['occupancy'] = occ
            v['excess'] = occ - int(r['raw_cap'])
            viol.append(v)
    viol.sort(key=lambda v: (v['excess'], v['lb'], v['occupancy'], -v['dim']), reverse=True)
    return viol


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', default='10')
    ap.add_argument('--include-dims', default='1')
    ap.add_argument('--through-fixed-dims', default='4,6')
    ap.add_argument('--target-groups', default='4:17,6:12,6:15')
    ap.add_argument('--initial-groups', default='')
    ap.add_argument('--orbit-close', action='store_true')
    ap.add_argument('--add-mode', choices=['all','first','topn'], default='all')
    ap.add_argument('--topn', type=int, default=20)
    ap.add_argument('--max-rounds', type=int, default=50)
    ap.add_argument('--time-limit', type=float, default=120.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()

    t0 = time.time()
    lut, lmeta = load_lut(args.lut)
    fixed_extra = parse_ints(args.fixed_extra)
    fixed, excluded, pts, idx = branch_points(fixed_extra, False)
    all_rows, collect_meta = collect_rows(lut, rank_s=args.rank, fixed=fixed, pts=pts,
                                          include_dims=parse_dims(args.include_dims),
                                          through_fixed_dims=parse_dims(args.through_fixed_dims))
    target_groups = parse_group_specs(args.target_groups)
    pool = [r for r in all_rows if (int(r['dim']), int(r['lb'])) in target_groups]
    pool_by_key = {int(r['key']): r for r in pool}
    active = parse_initial_keys(args.initial_groups, pool_by_key)
    if args.orbit_close and active:
        active = orbit_closure(active, set(pool_by_key), fixed)
    history = []
    status = None
    for rnd in range(1, args.max_rounds + 1):
        active_rows = [pool_by_key[k] for k in sorted(active)]
        res = solve_with_assumptions(active_rows, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                     time_limit=args.time_limit, workers=args.workers, use_assumptions=False)
        ent = {k: res[k] for k in ['status','elapsed_sec','solver_walltime','conflicts','branches']}
        ent['round'] = rnd
        ent['active_rows_before_scan'] = len(active)
        ent['active_summary'] = row_summary(active_rows)
        status = res['status']
        if res['status'] == 'INFEASIBLE':
            ent['decision'] = 'infeasible_core_found'
            history.append(ent)
            break
        if res['support'] is None:
            ent['decision'] = 'no_support_status'
            history.append(ent)
            break
        remaining_rows = [r for r in pool if int(r['key']) not in active]
        viol = support_violations(remaining_rows, res['support'])
        ent['support'] = res['support']
        ent['support_rank_hist'] = dict(sorted(Counter(matrix_rank_of_mask(p) for p in res['support']).items()))
        ent['support_rank1_count'] = sum(1 for p in res['support'] if matrix_rank_of_mask(p) == 1)
        ent['remaining_violation_count'] = len(viol)
        ent['violation_by_dim_lb'] = {f'{d},{lb}': c for (d, lb), c in sorted(Counter((v['dim'], v['lb']) for v in viol).items())}
        ent['violation_head'] = viol[:20]
        if not viol:
            ent['decision'] = 'target_pool_satisfied'
            history.append(ent)
            break
        if args.add_mode == 'first':
            add_keys = {int(viol[0]['key'])}
        elif args.add_mode == 'topn':
            add_keys = {int(v['key']) for v in viol[:args.topn]}
        else:
            add_keys = {int(v['key']) for v in viol}
        add_before = len(add_keys)
        if args.orbit_close:
            add_keys = orbit_closure(add_keys, set(pool_by_key), fixed)
        new_keys = add_keys - active
        active |= add_keys
        ent['added_seed_keys'] = add_before
        ent['added_after_orbit_close'] = len(add_keys)
        ent['new_active_rows'] = len(new_keys)
        ent['active_rows_after_add'] = len(active)
        ent['decision'] = 'added_violated_rows'
        history.append(ent)
        print(json.dumps({k: ent[k] for k in ['round','status','active_rows_before_scan','remaining_violation_count','violation_by_dim_lb','added_seed_keys','added_after_orbit_close','new_active_rows','active_rows_after_add','elapsed_sec']}, sort_keys=True), flush=True)
        if not new_keys:
            break
    final_rows = [pool_by_key[k] for k in sorted(active)]
    final_res = solve_with_assumptions(final_rows, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                       time_limit=max(args.time_limit, 120), workers=args.workers, use_assumptions=False)
    payload = {
        'problem': 'rep10 lazy violated-row core builder',
        'field': 'F2',
        'rank_s': args.rank,
        'fixed_points': fixed,
        'fixed_extra': fixed_extra,
        'target_groups': sorted([list(g) for g in target_groups]),
        'initial_groups': args.initial_groups,
        'orbit_close': args.orbit_close,
        'add_mode': args.add_mode,
        'topn': args.topn,
        'pool_summary': row_summary(pool),
        'collect_meta': collect_meta,
        'history': history,
        'final_row_summary': row_summary(final_rows),
        'final_check': {k: final_res[k] for k in ['status','elapsed_sec','solver_walltime','conflicts','branches']},
        'core_keys': [int(r['key']) for r in final_rows],
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'total_elapsed_sec': time.time() - t0,
        'meaning': 'Lazy CP-SAT violated-row core. Needs CNF/DRAT replay before proof use.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'rounds': len(history),
        'last_status': status,
        'final_row_summary': row_summary(final_rows),
        'final_check': payload['final_check'],
        'out': str(args.out),
        'total_elapsed_sec': payload['total_elapsed_sec'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
