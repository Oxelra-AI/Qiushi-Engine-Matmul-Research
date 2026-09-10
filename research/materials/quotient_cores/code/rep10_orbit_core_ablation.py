#!/usr/bin/env python3
"""Orbit-closed CP-SAT row deletion for the fixed-E11/rep10 Wang core.

Rows are grouped into orbits under the pointwise stabilizer of the fixed prefix
(default E11 and rep10).  A greedy deletion pass tries to remove whole blocks of
row-orbits while preserving CP-SAT infeasibility.  This gives a smaller,
stabilizer-closed row core for later proof-producing CNF replay and exposes the
row types actually used by the contradiction.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rep10_mus_core_cp import branch_points, collect_rows, parse_ints, row_summary, solve_with_assumptions  # noqa: E402
from rep10_solve_row_subset import parse_group_specs  # noqa: E402
from wang_capacity_cnf_e11_fixed import parse_dims  # noqa: E402
from wang_capacity_lazy import make_actions, matrix_rank_of_mask, transform_key, transform_mask, unpack_basis  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def stabilizer_actions(fixed: Sequence[int]):
    return [img for img in make_actions() if all(transform_mask(int(p), img) == int(p) for p in fixed)]


def make_row_orbits(rows: list[dict], fixed: Sequence[int]):
    by_key = {int(r['key']): r for r in rows}
    keys = set(by_key)
    actions = stabilizer_actions(fixed)
    unseen = set(keys)
    orbits = []
    while unseen:
        k0 = min(unseen)
        basis = unpack_basis(k0)
        imgs = {int(transform_key(basis, img)) for img in actions}
        missing = sorted(imgs - keys)
        if missing:
            # The selected row family should be invariant.  If it is not, close
            # only inside selected rows but record the issue.
            orb_keys = sorted(imgs & keys)
        else:
            orb_keys = sorted(imgs)
        unseen -= set(orb_keys)
        rs = [by_key[k] for k in orb_keys]
        sig = Counter((r['dim'], r['lb'], r['cap_rem'], r['var_count'], r['source']) for r in rs)
        orbits.append({
            'id': len(orbits),
            'keys': orb_keys,
            'row_count': len(orb_keys),
            'signature_hist': {str(k): v for k, v in sorted(sig.items())},
            'dim_hist': dict(sorted(Counter(r['dim'] for r in rs).items())),
            'lb_hist': dict(sorted(Counter(r['lb'] for r in rs).items())),
            'missing_images': len(missing),
        })
    return orbits, by_key, {'stab_size': len(actions), 'orbit_count': len(orbits), 'orbit_size_hist': dict(sorted(Counter(o['row_count'] for o in orbits).items())), 'missing_image_orbits': sum(1 for o in orbits if o['missing_images'])}


def rows_for(active_ids: set[int], orbits: list[dict], by_key: dict[int, dict]):
    out = []
    for i in sorted(active_ids):
        for k in orbits[i]['keys']:
            out.append(by_key[k])
    return out


def parse_block_sizes(spec: str) -> list[int]:
    return [int(x) for x in spec.replace(';', ',').split(',') if x.strip()]


def order_orbits(orbits: list[dict], mode: str) -> list[int]:
    if mode == 'large_first':
        return sorted(range(len(orbits)), key=lambda i: (-orbits[i]['row_count'], i))
    if mode == 'small_first':
        return sorted(range(len(orbits)), key=lambda i: (orbits[i]['row_count'], i))
    if mode == 'id':
        return list(range(len(orbits)))
    if mode == 'by_signature':
        return sorted(range(len(orbits)), key=lambda i: (json.dumps(orbits[i]['signature_hist'], sort_keys=True), orbits[i]['row_count'], i))
    raise ValueError(mode)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', default='10')
    ap.add_argument('--exclude-second-orbits-before', action='store_true')
    ap.add_argument('--include-dims', default='1')
    ap.add_argument('--through-fixed-dims', default='4,6')
    ap.add_argument('--groups', default='4:17,6:12,6:15')
    ap.add_argument('--time-limit', type=float, default=75.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--block-sizes', default='32,16,8')
    ap.add_argument('--max-tests-per-pass', type=int, default=None)
    ap.add_argument('--order', choices=['large_first','small_first','id','by_signature'], default='large_first')
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
    orbits, by_key, orbit_meta = make_row_orbits(rows, fixed)
    active = set(range(len(orbits)))
    base_rows = rows_for(active, orbits, by_key)
    base_res = solve_with_assumptions(base_rows, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                      time_limit=args.time_limit, workers=args.workers, use_assumptions=False)
    print('base', base_res['status'], 'rows', len(base_rows), 'orbits', len(active), flush=True)
    history = []
    for bsz in parse_block_sizes(args.block_sizes):
        order = [i for i in order_orbits(orbits, args.order) if i in active]
        pos = 0
        tests = 0
        pass_hist = []
        while pos < len(order):
            if args.max_tests_per_pass is not None and tests >= args.max_tests_per_pass:
                break
            block = [i for i in order[pos:pos+bsz] if i in active]
            if not block:
                pos += bsz
                continue
            trial = active - set(block)
            trial_rows = rows_for(trial, orbits, by_key)
            res = solve_with_assumptions(trial_rows, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                         time_limit=args.time_limit, workers=args.workers, use_assumptions=False)
            tests += 1
            ent = {
                'block_size_orbits': len(block),
                'block_row_count': sum(orbits[i]['row_count'] for i in block),
                'block_ids': block,
                'trial_orbits': len(trial),
                'trial_rows': len(trial_rows),
                'status': res['status'],
                'elapsed_sec': res['elapsed_sec'],
                'conflicts': res['conflicts'],
                'branches': res['branches'],
            }
            if res['status'] == 'INFEASIBLE':
                active = trial
                ent['decision'] = 'removed'
            else:
                ent['decision'] = 'kept'
            pass_hist.append(ent)
            print('pass', bsz, ent, flush=True)
            pos += bsz
        history.append({'block_size': bsz, 'tests': tests, 'history': pass_hist,
                        'active_orbits_after': len(active), 'active_rows_after': len(rows_for(active, orbits, by_key))})
    final_rows = rows_for(active, orbits, by_key)
    final_res = solve_with_assumptions(final_rows, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                       time_limit=max(args.time_limit, 120), workers=args.workers, use_assumptions=False)
    active_orbit_records = [orbits[i] for i in sorted(active)]
    payload = {
        'problem': 'rep10 fixed-E11 stabilizer-orbit row-core ablation',
        'field': 'F2',
        'rank_s': args.rank,
        'fixed_points': fixed,
        'fixed_extra': fixed_extra,
        'groups': sorted([list(x) for x in want]),
        'include_dims': sorted(parse_dims(args.include_dims)),
        'through_fixed_dims': sorted(parse_dims(args.through_fixed_dims)),
        'variable_point_count': len(pts),
        'variable_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in pts).items())),
        'excluded_point_count': len(excluded),
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'collect_meta': collect_meta,
        'initial_row_summary': row_summary(rows),
        'orbit_meta': orbit_meta,
        'base_result': {k: base_res[k] for k in ['status','elapsed_sec','solver_walltime','conflicts','branches']},
        'passes': history,
        'active_orbit_count': len(active),
        'active_orbits': active_orbit_records,
        'final_row_summary': row_summary(final_rows),
        'final_result': {k: final_res[k] for k in ['status','elapsed_sec','solver_walltime','conflicts','branches']},
        'core_keys': [int(r['key']) for r in final_rows],
        'total_elapsed_sec': time.time() - t0,
        'meaning': 'A stabilizer-closed row-core candidate found by CP-SAT deletion. CNF/DRAT verification is needed before formal proof use.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'base': payload['base_result'],
        'active_orbit_count': len(active),
        'final_row_summary': row_summary(final_rows),
        'final_result': payload['final_result'],
        'out': str(args.out),
        'total_elapsed_sec': payload['total_elapsed_sec'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
