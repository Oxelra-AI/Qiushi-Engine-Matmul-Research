#!/usr/bin/env python3
"""Singleton higher-rank feasibility survey at each rank-1 count.

For each higher-rank orbit representative under Stab(E11, rep),
test whether a SINGLE higher-rank point can appear in a Wang-admissible
support at each total rank-1 count k = 2, 3, ..., 17.

If singleton h is infeasible at rank-1 count k0, then by monotonicity
it is also infeasible at all k >= k0, and by extension:
- At k=k0, no triple/set containing h is viable
- At k=k0+1, etc., same

This gives a "max viable rank-1 count" per orbit, which is an extremely
powerful structural constraint for the master search.
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

from skeleton_oracle_joint_pilot import (
    ExactKOracle,
    build_branch,
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
    ap.add_argument('--rep', type=int, default=2)
    ap.add_argument('--k-min', type=int, default=2)
    ap.add_argument('--k-max', type=int, default=17)
    ap.add_argument('--time-limit', type=float, default=15.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--singleton-only', action='store_true',
                    help='Only test singletons, skip pair tests')
    args = ap.parse_args()

    t_all = time.time()
    print('Loading LUT...', flush=True)
    lut, meta = load_lut(args.lut)
    keys = list(lut.keys())
    print(f'  {len(lut):,} subspaces', flush=True)

    print('Packing bases...', flush=True)
    bases, dims, lbs = pack_bases_numpy(lut)
    print(f'  shape={bases.shape}', flush=True)

    _, stab_e11 = compute_stab_e11()
    branch = build_branch(args.rep, stab_e11)
    hr_orbits = branch['hr_orbits']
    print(f'\nBranch rep={args.rep}: {len(branch["avail_hr"])} HR points, '
          f'{len(hr_orbits)} orbits, stab order={len(branch["stab_pair"])}',
          flush=True)

    # For each k level, create an oracle
    # (the oracle precomputes rank-1 masks per k)
    orbit_results = []
    singleton_infeasible_at_k = {}  # orbit_rep -> min k where infeasible

    print(f'\n=== Singleton survey for rep {args.rep}, k={args.k_min}..{args.k_max} ===',
          flush=True)

    # Test in decreasing k order: if infeasible at k, skip all k' > k
    # Actually, monotonicity says: infeasible at k0 => infeasible at k >= k0
    # So test in INCREASING k: if feasible at k, skip testing k-1 (it's also feasible)
    # Wait, monotonicity: infeasible at smaller k => infeasible at larger k.
    # So if we find infeasible at k=5, we know it's infeasible at k=6,7,...,17.
    # We want the SMALLEST k where it becomes infeasible (= max viable k + 1).
    # Binary search would be optimal, but the oracle must be rebuilt per k.
    # Since we have 16 k-levels and 17 orbits, and each query is ~5s,
    # worst case is 16*17 = 272 queries ≈ 1360s.
    # But we can optimize: test k=17 first (the target level), then if infeasible
    # binary search downward for the transition point.

    # Strategy: test k=17 for all reps first (most important).
    # Then for infeasible ones, binary search for transition.
    # For feasible ones at k=17, done (they survive).

    k_target = args.k_max
    print(f'\n--- Phase 1: Test all {len(hr_orbits)} orbit reps at k={k_target} ---',
          flush=True)
    oracle_cache = {}

    def get_oracle(k):
        if k not in oracle_cache:
            oracle_cache[k] = ExactKOracle(
                branch=branch, bases=bases, lbs=lbs,
                keys=keys, rank_s=20,
            )
        return oracle_cache[k]

    # The oracle precomputes based on rank_s=20, not k.
    # The k is passed to query() as exact_rank1_count.
    # So we only need ONE oracle instance.
    oracle = ExactKOracle(
        branch=branch, bases=bases, lbs=lbs, keys=keys, rank_s=20,
    )
    print(f'  Oracle precompute: {oracle.precompute_sec:.1f}s, '
          f'{len(oracle.base_tight)} unique masks', flush=True)

    # Phase 1: test all orbit reps at k=17
    phase1_results = []
    infeasible_at_target = []
    feasible_at_target = []
    unknown_at_target = []

    for orb in hr_orbits:
        rep_pt = int(orb['rep'])
        t0 = time.time()
        res = oracle.query([rep_pt], k_target,
                           time_limit=args.time_limit, workers=args.workers,
                           capture_support=True)
        dt = time.time() - t0
        status = res.get('status', 'ERROR')
        item = {
            'orbit_rep': rep_pt,
            'orbit_size': int(orb['size']),
            'matrix_rank': matrix_rank_of_mask(rep_pt),
            'k': k_target,
            'status': status,
            'build_sec': res.get('build_sec'),
            'solve_sec': res.get('solve_sec'),
            'constraints_added': res.get('constraints_added'),
            'empty_constraints': res.get('empty_constraints'),
        }
        if status == 'INFEASIBLE':
            infeasible_at_target.append(rep_pt)
        elif status in ('OPTIMAL', 'FEASIBLE'):
            item['support_size'] = res.get('support_rank1_size')
            feasible_at_target.append(rep_pt)
        else:
            unknown_at_target.append(rep_pt)
        phase1_results.append(item)
        sym = '✗' if status == 'INFEASIBLE' else ('✓' if status in ('OPTIMAL', 'FEASIBLE') else '?')
        print(f'  orbit {rep_pt:3d} (size={orb["size"]:2d}, '
              f'matrank={matrix_rank_of_mask(rep_pt)}): '
              f'k={k_target} {sym} {status} ({dt:.1f}s)', flush=True)

    print(f'\n  Summary at k={k_target}: '
          f'{len(infeasible_at_target)} infeasible, '
          f'{len(feasible_at_target)} feasible, '
          f'{len(unknown_at_target)} unknown', flush=True)
    if infeasible_at_target:
        total_eliminated = sum(
            o['size'] for o in hr_orbits if int(o['rep']) in infeasible_at_target
        )
        print(f'  Total HR points eliminated by singleton at k={k_target}: '
              f'{total_eliminated}/{len(branch["avail_hr"])}', flush=True)

    # Phase 2: for infeasible orbit reps, binary search for transition point
    phase2_results = []
    if infeasible_at_target and args.k_min < k_target:
        print(f'\n--- Phase 2: Binary search for transition k '
              f'in [{args.k_min}, {k_target-1}] ---', flush=True)
        for rep_pt in infeasible_at_target:
            lo, hi = args.k_min, k_target - 1
            # We know: infeasible at k_target, want min infeasible k
            min_infeas_k = k_target
            while lo <= hi:
                mid = (lo + hi) // 2
                res = oracle.query([rep_pt], mid,
                                   time_limit=args.time_limit,
                                   workers=args.workers,
                                   capture_support=False)
                status = res.get('status', 'ERROR')
                if status == 'INFEASIBLE':
                    min_infeas_k = mid
                    hi = mid - 1
                elif status in ('OPTIMAL', 'FEASIBLE'):
                    lo = mid + 1
                else:
                    # UNKNOWN - can't determine, stop binary search
                    lo = mid + 1
            max_viable_k = min_infeas_k - 1
            entry = {
                'orbit_rep': rep_pt,
                'min_infeasible_k': min_infeas_k,
                'max_viable_k': max_viable_k,
                'interpretation': (
                    f'Any support in this branch containing a point from orbit '
                    f'{rep_pt} must have rank-1 count <= {max_viable_k}.'
                ),
            }
            phase2_results.append(entry)
            print(f'  orbit {rep_pt:3d}: infeasible at k>={min_infeas_k}, '
                  f'max viable k={max_viable_k}', flush=True)

    # Phase 3: for feasible orbit reps at k=17, test pairs
    phase3_results = []
    if not args.singleton_only and len(feasible_at_target) >= 2:
        print(f'\n--- Phase 3: Pair tests among {len(feasible_at_target)} '
              f'feasible orbit reps at k={k_target} ---', flush=True)
        import itertools
        pair_count = 0
        pair_infeas = 0
        for i, j in itertools.combinations(range(len(feasible_at_target)), 2):
            p1, p2 = feasible_at_target[i], feasible_at_target[j]
            res = oracle.query([p1, p2], k_target,
                               time_limit=args.time_limit,
                               workers=args.workers,
                               capture_support=True)
            status = res.get('status', 'ERROR')
            entry = {
                'pair': [p1, p2],
                'status': status,
                'canonical': res.get('fixed_high_canonical'),
                'orbit_image_count': res.get('fixed_high_orbit_image_count'),
                'build_sec': res.get('build_sec'),
                'solve_sec': res.get('solve_sec'),
            }
            if status in ('OPTIMAL', 'FEASIBLE'):
                entry['support_size'] = res.get('support_rank1_size')
            phase3_results.append(entry)
            pair_count += 1
            if status == 'INFEASIBLE':
                pair_infeas += 1
            sym = '✗' if status == 'INFEASIBLE' else (
                '✓' if status in ('OPTIMAL', 'FEASIBLE') else '?')
            print(f'  pair ({p1}, {p2}): {sym} {status} '
                  f'({res.get("solve_sec", 0):.1f}s)', flush=True)

        print(f'\n  Pair summary at k={k_target}: '
              f'{pair_infeas}/{pair_count} infeasible', flush=True)

    elapsed = time.time() - t_all
    result = {
        'problem': 'Singleton HR feasibility survey',
        'branch_rep': args.rep,
        'k_range': [args.k_min, args.k_max],
        'stab_pair_order': len(branch['stab_pair']),
        'total_hr_points': len(branch['avail_hr']),
        'hr_orbit_count': len(hr_orbits),
        'phase1_target_k': k_target,
        'phase1_results': phase1_results,
        'phase1_summary': {
            'infeasible_reps': infeasible_at_target,
            'feasible_reps': feasible_at_target,
            'unknown_reps': unknown_at_target,
            'surviving_reps': sorted(feasible_at_target + unknown_at_target),
            'infeasible_count': len(infeasible_at_target),
            'feasible_count': len(feasible_at_target),
            'unknown_count': len(unknown_at_target),
            'points_eliminated': sum(
                o['size'] for o in hr_orbits
                if int(o['rep']) in infeasible_at_target
            ),
        },
        'phase2_transition_results': phase2_results,
        'phase3_pair_results': phase3_results,
        'elapsed_sec': elapsed,
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True,
                                    default=str) + '\n')
    print(f'\nSaved to {args.out} ({elapsed:.1f}s total)')


if __name__ == '__main__':
    main()
