#!/usr/bin/env python3
"""Exhaustive canonical pair enumeration among surviving HR points.

Enumerates ALL C(n,2) pairs among surviving points, groups by canonical
form under the branch stabilizer, and tests one representative per class.
This closes the gap in the orbit-rep pair survey.
"""
from __future__ import annotations

import argparse
import itertools
import json
import pickle
import sys
import time
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from skeleton_oracle_joint_pilot import (
    ExactKOracle, build_branch, canonical_set, orbit_image_count, load_lut,
)
from precompute_skeleton_system import (
    compute_stab_e11, pack_bases_numpy,
)
from wang_capacity_lazy import matrix_rank_of_mask


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path,
                    default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--survey', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--time-limit', type=float, default=20.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--do-triples', action='store_true')
    args = ap.parse_args()

    t_all = time.time()
    survey = json.loads(args.survey.read_text())
    rep = survey['branch_rep']
    phase1 = survey['phase1_summary']
    feasible_reps = phase1.get('surviving_reps') or phase1.get('survivor_reps') or sorted(
        phase1.get('feasible_reps', []) + phase1.get('unknown_reps', [])
    )

    print(f'Loading LUT...', flush=True)
    lut, meta = load_lut(args.lut)
    keys = list(lut.keys())
    bases, dims, lbs = pack_bases_numpy(lut)
    _, stab_e11 = compute_stab_e11()
    branch = build_branch(rep, stab_e11)

    # Get ALL surviving points
    surviving_pts = []
    for orb in branch['hr_orbits']:
        if int(orb['rep']) in feasible_reps:
            surviving_pts.extend(int(p) for p in orb['members'])
    surviving_pts = sorted(surviving_pts)
    surviving_set = set(surviving_pts)
    n = len(surviving_pts)
    print(f'Branch rep={rep}, k={args.k}, surviving HR points: {n}', flush=True)

    oracle = ExactKOracle(
        branch=branch, bases=bases, lbs=lbs, keys=keys, rank_s=20,
    )
    print(f'Oracle precompute: {oracle.precompute_sec:.1f}s', flush=True)

    # Enumerate ALL canonical pairs
    print(f'\n=== Enumerating all C({n},2)={n*(n-1)//2} pairs ===', flush=True)
    canonical_pairs = {}  # canonical -> first_example
    for p1, p2 in itertools.combinations(surviving_pts, 2):
        can = canonical_set([p1, p2], branch['stab_pair'])
        if can not in canonical_pairs:
            canonical_pairs[can] = (p1, p2)
    print(f'  {len(canonical_pairs)} canonical pair classes', flush=True)

    # Test each canonical pair
    pair_results = []
    infeas = feas = unk = 0
    for can, (p1, p2) in sorted(canonical_pairs.items()):
        res = oracle.query(list(can), args.k,
                           time_limit=args.time_limit,
                           workers=args.workers,
                           capture_support=True)
        status = res.get('status', 'ERROR')
        imgs = res.get('fixed_high_orbit_image_count', 0)
        entry = {
            'canonical': list(can),
            'example': [p1, p2],
            'status': status,
            'orbit_image_count': imgs,
            'build_sec': res.get('build_sec'),
            'solve_sec': res.get('solve_sec'),
        }
        if status in ('OPTIMAL', 'FEASIBLE'):
            entry['support_size'] = res.get('support_rank1_size')
            feas += 1
        elif status == 'INFEASIBLE':
            infeas += 1
        else:
            unk += 1
        pair_results.append(entry)
        sym = '✗' if status == 'INFEASIBLE' else (
            '✓' if status in ('OPTIMAL', 'FEASIBLE') else '?')
        print(f'  {list(can)}: {sym} {status} (imgs={imgs}, '
              f'{res.get("solve_sec",0):.1f}s)', flush=True)

    print(f'\nPair summary: {infeas} infeasible, {feas} feasible, '
          f'{unk} unknown out of {len(canonical_pairs)} classes', flush=True)

    # If ALL pairs infeasible, k is closed!
    if infeas == len(canonical_pairs) and feas == 0 and unk == 0:
        print(f'\n*** ALL PAIRS INFEASIBLE at k={args.k} for rep {rep} ***',
              flush=True)
        print(f'*** This means no triple of HR points is viable. ***',
              flush=True)
        print(f'*** k={args.k} is CLOSED for this branch (CP-SAT level). ***',
              flush=True)

    # Triple enumeration if requested
    triple_results = []
    if args.do_triples and feas > 0:
        print(f'\n=== Triple enumeration ===', flush=True)
        # Collect ALL forbidden pair orbit images
        forbidden_pairs = set()
        for r in pair_results:
            if r['status'] == 'INFEASIBLE':
                can = tuple(r['canonical'])
                from wang_capacity_lazy import transform_mask
                for g in branch['stab_pair']:
                    img = tuple(sorted(transform_mask(p, g) for p in can))
                    if all(p in surviving_set for p in img):
                        forbidden_pairs.add(img)

        print(f'  Forbidden pair images among surviving pts: '
              f'{len(forbidden_pairs)}', flush=True)

        tested_canonicals = set()
        inf_t = feas_t = unk_t = 0
        for tri in itertools.combinations(surviving_pts, 3):
            skip = False
            for i, j in itertools.combinations(range(3), 2):
                if tuple(sorted([tri[i], tri[j]])) in forbidden_pairs:
                    skip = True
                    break
            if skip:
                continue
            can = canonical_set(tri, branch['stab_pair'])
            if can in tested_canonicals:
                continue
            tested_canonicals.add(can)
            res = oracle.query(list(can), args.k,
                               time_limit=args.time_limit,
                               workers=args.workers,
                               capture_support=True)
            status = res.get('status', 'ERROR')
            entry = {
                'canonical': list(can),
                'status': status,
                'orbit_image_count': res.get('fixed_high_orbit_image_count'),
                'solve_sec': res.get('solve_sec'),
            }
            if status in ('OPTIMAL', 'FEASIBLE'):
                entry['support'] = res.get('support_all_with_fixed_high')
                feas_t += 1
            elif status == 'INFEASIBLE':
                inf_t += 1
            else:
                unk_t += 1
            triple_results.append(entry)
            if len(tested_canonicals) % 20 == 0:
                print(f'  {len(tested_canonicals)} triple orbits: '
                      f'{inf_t} inf, {feas_t} feas, {unk_t} unk',
                      flush=True)

        print(f'\n  Triple summary: {len(tested_canonicals)} tested, '
              f'{inf_t} inf, {feas_t} feas, {unk_t} unk', flush=True)

    elapsed = time.time() - t_all
    result = {
        'branch_rep': rep,
        'k': args.k,
        'surviving_pts_count': n,
        'canonical_pair_count': len(canonical_pairs),
        'pair_infeasible': infeas,
        'pair_feasible': feas,
        'pair_unknown': unk,
        'pair_results': pair_results,
        'all_pairs_infeasible': infeas == len(canonical_pairs) and feas == 0 and unk == 0,
        'triple_results': triple_results,
        'elapsed_sec': elapsed,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True,
                                    default=str) + '\n')
    print(f'\nSaved to {args.out} ({elapsed:.1f}s total)')


if __name__ == '__main__':
    main()
