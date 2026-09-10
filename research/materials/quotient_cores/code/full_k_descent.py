#!/usr/bin/env python3
"""Full k-descent for a branch: test singletons and pairs at decreasing k.

For each k from k_max down to k_min:
1. Test all surviving singletons (fast, <1s per orbit)
2. If any survive, enumerate all canonical pairs
3. If all pairs infeasible, k is closed
4. Report the lowest k where all singletons/pairs are infeasible
"""
from __future__ import annotations

import argparse
import itertools
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

from general_singleton_pair_survey import (
    GeneralExactKOracle,
    build_branch_general,
)
from skeleton_oracle_joint_pilot import (
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
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--rep', type=int, required=True)
    ap.add_argument('--k-min', type=int, default=2)
    ap.add_argument('--k-max', type=int, default=17)
    ap.add_argument('--time-limit', type=float, default=15.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--max-pairs', type=int, default=2000,
                    help='Skip pair test if more canonical classes than this')
    args = ap.parse_args()

    t_all = time.time()
    print('Loading LUT...', flush=True)
    lut, meta = load_lut(args.lut)
    keys = list(lut.keys())
    bases, dims, lbs = pack_bases_numpy(lut)
    _, stab_e11 = compute_stab_e11()
    branch = build_branch_general(args.rep, stab_e11)

    print(f'Branch rep={args.rep} (rank-{branch["rep_rank"]}): '
          f'{len(branch["avail_hr"])} HR pts, '
          f'{len(branch["hr_orbits"])} orbits, '
          f'|stab|={len(branch["stab_pair"])}, '
          f'free_r1={len(branch["free_r1"])}', flush=True)

    oracle = GeneralExactKOracle(
        branch=branch, bases=bases, lbs=lbs, keys=keys, rank_s=20,
    )
    print(f'Oracle precompute: {oracle.precompute_sec:.1f}s, '
          f'{len(oracle.base_tight)} unique masks', flush=True)

    k_results = []

    for k in range(args.k_max, args.k_min - 1, -1):
        t_k = time.time()
        print(f'\n{"="*60}', flush=True)
        print(f'=== k={k} ===', flush=True)

        # Phase 1: singleton test
        infeasible_orbs = []
        feasible_orbs = []
        unknown_orbs = []
        singleton_results = []

        for orb in branch['hr_orbits']:
            rep_pt = int(orb['rep'])
            res = oracle.query([rep_pt], k,
                               time_limit=args.time_limit,
                               workers=args.workers,
                               capture_support=False)
            status = res.get('status', 'ERROR')
            if status == 'INFEASIBLE':
                infeasible_orbs.append(rep_pt)
            elif status in ('OPTIMAL', 'FEASIBLE'):
                feasible_orbs.append(rep_pt)
            else:
                unknown_orbs.append(rep_pt)
                feasible_orbs.append(rep_pt)  # conservative: include in survivors
            singleton_results.append({
                'orbit_rep': rep_pt,
                'orbit_size': int(orb['size']),
                'status': status,
                'solve_sec': res.get('solve_sec'),
            })

        eliminated = sum(o['size'] for o in branch['hr_orbits']
                        if int(o['rep']) in infeasible_orbs)
        surviving = len(branch['avail_hr']) - eliminated
        print(f'  Singletons: {len(infeasible_orbs)} inf, '
              f'{len(feasible_orbs)} surv '
              f'({eliminated}/{len(branch["avail_hr"])} eliminated, '
              f'{surviving} surviving)', flush=True)

        k_entry = {
            'k': k,
            'singleton_infeasible_orbs': infeasible_orbs,
            'singleton_feasible_orbs': feasible_orbs,
            'singleton_unknown_orbs': [o for o in unknown_orbs],
            'eliminated_pts': eliminated,
            'surviving_pts': surviving,
            'singleton_results': singleton_results,
        }

        if surviving == 0:
            k_entry['closed_by'] = 'singletons'
            k_entry['closed'] = True
            print(f'  *** k={k} CLOSED by singletons (0 surviving HR) ***',
                  flush=True)
        else:
            # Get surviving points
            surviving_pts = []
            for orb in branch['hr_orbits']:
                if int(orb['rep']) in feasible_orbs:
                    surviving_pts.extend(int(p) for p in orb['members'])
            surviving_pts = sorted(surviving_pts)

            # Enumerate canonical pairs
            canonical_pairs = {}
            for p1, p2 in itertools.combinations(surviving_pts, 2):
                can = canonical_set([p1, p2], branch['stab_pair'])
                if can not in canonical_pairs:
                    canonical_pairs[can] = (p1, p2)

            n_pairs = len(canonical_pairs)
            k_entry['canonical_pair_count'] = n_pairs
            print(f'  {n_pairs} canonical pair classes among '
                  f'{len(surviving_pts)} pts', flush=True)

            if n_pairs > args.max_pairs:
                k_entry['closed'] = False
                k_entry['closed_by'] = None
                k_entry['note'] = f'Too many pairs ({n_pairs} > {args.max_pairs}), skipped'
                print(f'  Skipping pair test (too many classes)', flush=True)
            else:
                # Phase 2: exhaustive pair test
                inf_p = feas_p = unk_p = 0
                pair_results = []
                first_feas = None
                for can, (p1, p2) in sorted(canonical_pairs.items()):
                    res = oracle.query(list(can), k,
                                       time_limit=args.time_limit,
                                       workers=args.workers,
                                       capture_support=(first_feas is None))
                    status = res.get('status', 'ERROR')
                    if status == 'INFEASIBLE':
                        inf_p += 1
                    elif status in ('OPTIMAL', 'FEASIBLE'):
                        feas_p += 1
                        if first_feas is None:
                            first_feas = {
                                'canonical': list(can),
                                'support': res.get('support_all'),
                            }
                    else:
                        unk_p += 1
                    pair_results.append({
                        'canonical': list(can),
                        'status': status,
                    })
                    if (inf_p + feas_p + unk_p) % 50 == 0:
                        print(f'    [{inf_p+feas_p+unk_p}/{n_pairs}] '
                              f'{inf_p} inf, {feas_p} feas, {unk_p} unk',
                              flush=True)

                k_entry['pair_infeasible'] = inf_p
                k_entry['pair_feasible'] = feas_p
                k_entry['pair_unknown'] = unk_p
                k_entry['pair_results'] = pair_results

                if feas_p == 0 and unk_p == 0:
                    k_entry['closed'] = True
                    k_entry['closed_by'] = 'pairs'
                    print(f'  *** k={k} CLOSED by pairs '
                          f'({inf_p} infeasible, 0 feasible) ***', flush=True)
                else:
                    k_entry['closed'] = False
                    k_entry['closed_by'] = None
                    k_entry['first_feasible_pair'] = first_feas
                    print(f'  k={k} NOT closed: {inf_p} inf, '
                          f'{feas_p} feas, {unk_p} unk', flush=True)
                    if first_feas:
                        print(f'    First feasible pair: {first_feas["canonical"]}',
                              flush=True)

        k_entry['elapsed_sec'] = time.time() - t_k
        k_results.append(k_entry)

        # If NOT closed, stop descending (lower k will be harder)
        if not k_entry.get('closed', False):
            print(f'\n  Stopping descent at k={k} (not closed)', flush=True)
            break

    elapsed = time.time() - t_all
    # Compute summary
    closed_levels = [r['k'] for r in k_results if r.get('closed')]
    open_levels = [r['k'] for r in k_results if not r.get('closed')]
    min_closed_k = min(closed_levels) if closed_levels else None

    result = {
        'branch_rep': args.rep,
        'rep_rank': branch['rep_rank'],
        'total_hr': len(branch['avail_hr']),
        'hr_orbits': len(branch['hr_orbits']),
        'stab_order': len(branch['stab_pair']),
        'free_r1': len(branch['free_r1']),
        'k_range_tested': [args.k_max, args.k_min],
        'closed_k_levels': closed_levels,
        'open_k_levels': open_levels,
        'min_closed_k': min_closed_k,
        'k_results': k_results,
        'summary': (
            f'All k>={min_closed_k} closed for rep {args.rep}. '
            f'k<{min_closed_k} not tested or open.'
            if min_closed_k else
            f'No k level closed for rep {args.rep}.'
        ),
        'elapsed_sec': elapsed,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True,
                                    default=str) + '\n')
    print(f'\n{"="*60}')
    print(f'SUMMARY for rep {args.rep}:')
    print(f'  Closed k levels: {closed_levels}')
    print(f'  Open k levels: {open_levels}')
    if min_closed_k:
        print(f'  All k >= {min_closed_k} are closed')
    print(f'Saved to {args.out} ({elapsed:.1f}s total)')


if __name__ == '__main__':
    main()
