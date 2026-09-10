#!/usr/bin/env python3
"""Quick pair survey among surviving orbit reps at a given k.

Takes the singleton survey output and tests all inter-orbit-rep pairs.
Also tests intra-orbit pairs for orbits with size >= 2.
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
    ExactKOracle,
    build_branch,
    canonical_set,
    orbit_image_count,
    load_lut,
)
from precompute_skeleton_system import (
    compute_stab_e11,
    pack_bases_numpy,
)
from wang_capacity_lazy import matrix_rank_of_mask


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path,
                    default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--survey', type=Path, required=True,
                    help='Path to singleton survey JSON')
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--time-limit', type=float, default=20.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--do-triples', action='store_true',
                    help='Also enumerate all surviving triples')
    args = ap.parse_args()

    t_all = time.time()
    survey = json.loads(args.survey.read_text())
    rep = survey['branch_rep']
    phase1 = survey['phase1_summary']
    feasible_reps = phase1.get('surviving_reps') or phase1.get('survivor_reps') or sorted(
        phase1.get('feasible_reps', []) + phase1.get('unknown_reps', [])
    )
    print(f'Branch rep={rep}, k={args.k}', flush=True)
    print(f'Feasible orbit reps at k={args.k}: {feasible_reps}', flush=True)

    # Get orbit members for each feasible rep
    orbit_members = {}
    for r in survey['phase1_results']:
        if r['orbit_rep'] in feasible_reps:
            orbit_members[r['orbit_rep']] = r['orbit_size']

    print(f'Total surviving HR points: '
          f'{sum(orbit_members.values())}', flush=True)

    print('\nLoading LUT...', flush=True)
    lut, meta = load_lut(args.lut)
    keys = list(lut.keys())
    bases, dims, lbs = pack_bases_numpy(lut)
    _, stab_e11 = compute_stab_e11()
    branch = build_branch(rep, stab_e11)

    # Get actual orbit members
    orbit_pts = {}
    for orb in branch['hr_orbits']:
        r = int(orb['rep'])
        if r in feasible_reps:
            orbit_pts[r] = sorted(int(p) for p in orb['members'])

    oracle = ExactKOracle(
        branch=branch, bases=bases, lbs=lbs, keys=keys, rank_s=20,
    )
    print(f'Oracle precompute: {oracle.precompute_sec:.1f}s', flush=True)

    # Phase 1: inter-orbit-rep pairs
    print(f'\n=== Pair tests (inter-orbit reps) ===', flush=True)
    pair_results = []
    pair_infeas_count = 0
    pair_feas_count = 0

    for i, j in itertools.combinations(range(len(feasible_reps)), 2):
        r1, r2 = feasible_reps[i], feasible_reps[j]
        res = oracle.query([r1, r2], args.k,
                           time_limit=args.time_limit,
                           workers=args.workers,
                           capture_support=True)
        status = res.get('status', 'ERROR')
        entry = {
            'pair': [r1, r2],
            'type': 'inter_orbit_rep',
            'status': status,
            'canonical': res.get('fixed_high_canonical'),
            'orbit_image_count': res.get('fixed_high_orbit_image_count'),
            'build_sec': res.get('build_sec'),
            'solve_sec': res.get('solve_sec'),
            'constraints_added': res.get('constraints_added'),
        }
        if status in ('OPTIMAL', 'FEASIBLE'):
            entry['support_size'] = res.get('support_rank1_size')
            pair_feas_count += 1
        elif status == 'INFEASIBLE':
            pair_infeas_count += 1
        pair_results.append(entry)
        sym = '✗' if status == 'INFEASIBLE' else ('✓' if status in ('OPTIMAL', 'FEASIBLE') else '?')
        print(f'  ({r1:3d}, {r2:3d}): {sym} {status} '
              f'(canon={res.get("fixed_high_canonical")}, '
              f'imgs={res.get("fixed_high_orbit_image_count")}, '
              f'{res.get("solve_sec",0):.1f}s)', flush=True)

    print(f'\nInter-orbit-rep pairs: {pair_infeas_count} infeasible, '
          f'{pair_feas_count} feasible, '
          f'{len(pair_results) - pair_infeas_count - pair_feas_count} other',
          flush=True)

    # Phase 2: intra-orbit pairs (for orbits with size >= 2)
    print(f'\n=== Intra-orbit pair tests ===', flush=True)
    intra_results = []
    for r, pts in orbit_pts.items():
        if len(pts) < 2:
            continue
        # Test just a few representative pairs
        tested_canonicals = set()
        for p1, p2 in itertools.combinations(pts, 2):
            can = canonical_set([p1, p2], branch['stab_pair'])
            if can in tested_canonicals:
                continue
            tested_canonicals.add(can)
            res = oracle.query([p1, p2], args.k,
                               time_limit=args.time_limit,
                               workers=args.workers,
                               capture_support=True)
            status = res.get('status', 'ERROR')
            entry = {
                'pair': [p1, p2],
                'type': 'intra_orbit',
                'orbit_rep': r,
                'status': status,
                'canonical': list(can),
                'orbit_image_count': res.get('fixed_high_orbit_image_count'),
                'build_sec': res.get('build_sec'),
                'solve_sec': res.get('solve_sec'),
            }
            if status in ('OPTIMAL', 'FEASIBLE'):
                entry['support_size'] = res.get('support_rank1_size')
            intra_results.append(entry)
            sym = '✗' if status == 'INFEASIBLE' else ('✓' if status in ('OPTIMAL', 'FEASIBLE') else '?')
            print(f'  orbit {r}: ({p1}, {p2}) {sym} {status} '
                  f'(canon={list(can)}, {res.get("solve_sec",0):.1f}s)',
                  flush=True)

    # Phase 3: triple enumeration (if requested and feasible)
    triple_results = []
    if args.do_triples:
        surviving_pts = sorted(set(p for pts in orbit_pts.values() for p in pts))
        print(f'\n=== Triple enumeration among {len(surviving_pts)} '
              f'surviving HR points ===', flush=True)

        # Collect all forbidden pairs
        forbidden_pairs = set()
        for r in pair_results + intra_results:
            if r['status'] == 'INFEASIBLE':
                can = tuple(r['canonical'])
                # Also add all orbit images
                for g in branch['stab_pair']:
                    from wang_capacity_lazy import transform_mask
                    img = tuple(sorted(transform_mask(p, g) for p in can))
                    forbidden_pairs.add(img)

        # Count forbidden from known constraints file
        try:
            fc = json.loads(Path('data/'
                                 'skeleton_joint_pilot/'
                                 'forbidden_high_constraints.json').read_text())
            for c in fc['constraints']:
                if c['branch_second_rep'] == rep:
                    for img in c['orbit_images']:
                        forbidden_pairs.add(tuple(sorted(img)))
        except Exception:
            pass

        print(f'  Total forbidden pair images: {len(forbidden_pairs)}', flush=True)

        # Enumerate canonical triples
        tested_canonicals = set()
        infeas_triples = 0
        feas_triples = 0
        unk_triples = 0
        total_tested = 0

        for tri in itertools.combinations(surviving_pts, 3):
            # Check if any pair is forbidden
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
            total_tested += 1

            res = oracle.query(list(can), args.k,
                               time_limit=args.time_limit,
                               workers=args.workers,
                               capture_support=True)
            status = res.get('status', 'ERROR')
            entry = {
                'triple': list(can),
                'status': status,
                'orbit_image_count': res.get('fixed_high_orbit_image_count'),
                'build_sec': res.get('build_sec'),
                'solve_sec': res.get('solve_sec'),
            }
            if status in ('OPTIMAL', 'FEASIBLE'):
                entry['support_all'] = res.get('support_all_with_fixed_high')
                feas_triples += 1
            elif status == 'INFEASIBLE':
                infeas_triples += 1
            else:
                unk_triples += 1
            triple_results.append(entry)

            if total_tested % 50 == 0:
                print(f'  tested {total_tested} triple orbits: '
                      f'{infeas_triples} infeas, {feas_triples} feas, '
                      f'{unk_triples} unk', flush=True)

        print(f'\n  Triple summary: {total_tested} orbits tested, '
              f'{infeas_triples} infeas, {feas_triples} feas, '
              f'{unk_triples} unknown', flush=True)

    elapsed = time.time() - t_all
    result = {
        'branch_rep': rep,
        'k': args.k,
        'feasible_orbit_reps': feasible_reps,
        'surviving_hr_count': sum(orbit_members.values()),
        'inter_orbit_pair_results': pair_results,
        'intra_orbit_pair_results': intra_results,
        'pair_summary': {
            'inter_infeasible': pair_infeas_count,
            'inter_feasible': pair_feas_count,
            'intra_infeasible': sum(1 for r in intra_results if r['status'] == 'INFEASIBLE'),
            'intra_feasible': sum(1 for r in intra_results if r['status'] in ('OPTIMAL', 'FEASIBLE')),
        },
        'triple_results': triple_results,
        'triple_summary': {
            'tested': len(triple_results),
            'infeasible': sum(1 for r in triple_results if r['status'] == 'INFEASIBLE'),
            'feasible': sum(1 for r in triple_results if r['status'] in ('OPTIMAL', 'FEASIBLE')),
            'unknown': sum(1 for r in triple_results if r['status'] not in ('INFEASIBLE', 'OPTIMAL', 'FEASIBLE')),
        } if triple_results else None,
        'elapsed_sec': elapsed,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True,
                                    default=str) + '\n')
    print(f'\nSaved to {args.out} ({elapsed:.1f}s total)')


if __name__ == '__main__':
    main()
