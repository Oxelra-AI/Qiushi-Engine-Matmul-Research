#!/usr/bin/env python3
"""Singleton→pair hierarchy for branches with rank-2 second points.

For rep10 (E12+E21, rank-2), the oracle needs modified treatment:
- fixed_rank1 = [E11] only (rep10 is NOT rank-1)
- rep10 is permanently added to fixed_high in every query
- free_r1 excludes E11 and excluded points but NOT rep10
- The skeleton oracle then tests rank-1 completion as before

The singleton and pair infeasibility tests transfer to rep10 via
the same monotonicity arguments.
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

from precompute_skeleton_system import (
    E11,
    compute_orbits,
    compute_stab_e11,
    compute_stab_pair,
    pack_bases_numpy,
    precompute_base,
    rank1_points,
    vectorized_multi_membership,
)
from skeleton_oracle_joint_pilot import (
    ExactKOracle,
    build_tight_with_witness,
    canonical_set,
    orbit_image_count,
    load_lut,
)
from wang_capacity_lazy import (
    matrix_rank_of_mask,
    subspace_points_from_basis,
    transform_mask,
    unpack_basis,
)


def build_branch_general(rep: int, stab_e11):
    """Build branch for any rep (rank-1 or rank-2/3 second point)."""
    mat_rank = matrix_rank_of_mask(rep)
    e11_orbits = compute_orbits(stab_e11, range(2, 512))
    excluded: set[int] = set()
    found = False
    for orb in e11_orbits:
        if orb['rep'] == rep:
            found = True
            break
        excluded.update(int(p) for p in orb['members'])
    if not found:
        raise ValueError(f'rep {rep} not found in Stab(E11) orbits')
    excluded.discard(E11)
    excluded.discard(rep)

    r1_all = rank1_points()
    if mat_rank == 1:
        fixed_rank1 = [E11, rep]
        fixed_hr_permanent = []
    else:
        fixed_rank1 = [E11]
        fixed_hr_permanent = [rep]

    fixed_set = set(fixed_rank1 + fixed_hr_permanent)
    free_r1 = [p for p in r1_all if p not in fixed_set and p not in excluded]
    avail_all = [p for p in range(1, 512) if p not in fixed_set and p not in excluded]
    avail_hr = [p for p in avail_all if matrix_rank_of_mask(p) > 1]
    stab_pair = compute_stab_pair(stab_e11, rep)
    hr_orbits = compute_orbits(stab_pair, avail_hr)
    orbit_label = {}
    for orb in hr_orbits:
        for p in orb['members']:
            orbit_label[int(p)] = int(orb['rep'])

    return {
        'rep': rep,
        'rep_rank': mat_rank,
        'fixed_rank1': fixed_rank1,
        'fixed_hr_permanent': fixed_hr_permanent,
        'excluded': excluded,
        'free_r1': free_r1,
        'avail_hr': avail_hr,
        'stab_pair': stab_pair,
        'hr_orbits': hr_orbits,
        'orbit_label': orbit_label,
    }


class GeneralExactKOracle:
    """Oracle that handles both rank-1 and higher-rank permanent fixtures."""

    def __init__(self, *, branch, bases, lbs, keys, rank_s):
        self.branch = branch
        self.bases = bases
        self.lbs = lbs
        self.keys = keys
        self.rank_s = rank_s
        self.free_r1 = branch['free_r1']
        self.fixed_rank1 = branch['fixed_rank1']
        self.fixed_hr_permanent = branch['fixed_hr_permanent']
        t0 = time.time()
        # Precompute base with fixed rank-1 AND permanent HR points
        all_fixed = self.fixed_rank1 + self.fixed_hr_permanent
        self.r1_masks, self.base_caps = precompute_base(
            bases, lbs, all_fixed, self.free_r1, rank_s
        )
        self.base_tight, self.base_witness = build_tight_with_witness(
            self.r1_masks, self.base_caps, keys, lbs
        )
        self.precompute_sec = time.time() - t0

    def query(self, additional_high, exact_rank1_count, *,
              time_limit, workers, capture_support=True):
        from ortools.sat.python import cp_model
        t0 = time.time()
        additional_high = sorted(int(p) for p in additional_high)
        if len(set(additional_high)) != len(additional_high):
            return {'status': 'INVALID_DUPLICATE_HIGH_POINTS', 'additional_high': additional_high}
        overlap_perm = sorted(set(additional_high) & set(self.fixed_hr_permanent))
        if overlap_perm:
            return {'status': 'INVALID_HIGH_POINTS', 'reason': 'additional_high_overlaps_fixed_hr_permanent', 'bad': overlap_perm}
        bad = [p for p in additional_high if p not in set(self.branch['avail_hr'])]
        if bad:
            return {'status': 'INVALID_HIGH_POINTS', 'bad': bad}
        # free_needed = exact_rank1_count - number_of_rank1_fixed
        free_needed = int(exact_rank1_count) - len(self.fixed_rank1)
        if free_needed < 0 or free_needed > len(self.free_r1):
            return {'status': 'PARAMETER_OUT_OF_RANGE', 'reason': 'rank1_count_bounds', 'free_needed': int(free_needed)}

        if additional_high:
            hr_count = vectorized_multi_membership(self.bases, additional_high)
            adjusted_caps = self.base_caps - hr_count.astype(np.int16)
        else:
            adjusted_caps = self.base_caps

        # Build tight dict
        adjusted_tight = dict(self.base_tight)
        if additional_high:
            affected = np.where(hr_count > 0)[0]
            for i in affected:
                m = int(self.r1_masks[i])
                c = int(adjusted_caps[i])
                old = adjusted_tight.get(m)
                if old is None or c < old:
                    adjusted_tight[m] = c

        model = cp_model.CpModel()
        x = [model.NewBoolVar(f'x_{p}') for p in self.free_r1]
        model.Add(sum(x) == free_needed)
        constraints_added = 0
        empty_constraints = 0
        for mask, cap in adjusted_tight.items():
            bc = int(mask).bit_count()
            if bc > cap:
                if cap < 0:
                    model.AddBoolOr([])
                    empty_constraints += 1
                else:
                    inds = [i for i in range(len(self.free_r1))
                            if (int(mask) >> i) & 1]
                    model.Add(sum(x[i] for i in inds) <= cap)
                constraints_added += 1

        build_sec = time.time() - t0
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(time_limit)
        solver.parameters.num_search_workers = int(workers)
        t1 = time.time()
        st = solver.Solve(model)
        solve_sec = time.time() - t1
        status = solver.StatusName(st)

        support_rank1 = None
        if capture_support and status in ('OPTIMAL', 'FEASIBLE'):
            support_free = [self.free_r1[i] for i in range(len(self.free_r1))
                           if solver.Value(x[i])]
            support_rank1 = sorted(self.fixed_rank1 + support_free)

        all_high = sorted(self.fixed_hr_permanent + additional_high)
        return {
            'status': status,
            'additional_high': additional_high,
            'all_fixed_high': all_high,
            'exact_rank1_count': int(exact_rank1_count),
            'free_needed': int(free_needed),
            'constraints_added': constraints_added,
            'empty_constraints': empty_constraints,
            'build_sec': build_sec,
            'solve_sec': solve_sec,
            'support_rank1': support_rank1,
            'support_all': (sorted(support_rank1 + all_high)
                           if support_rank1 else None),
        }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path,
                    default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--rep', type=int, default=10)
    ap.add_argument('--k-max', type=int, default=17)
    ap.add_argument('--time-limit', type=float, default=15.0)
    ap.add_argument('--workers', type=int, default=8)
    args = ap.parse_args()

    t_all = time.time()
    print('Loading LUT...', flush=True)
    lut, meta = load_lut(args.lut)
    keys = list(lut.keys())
    bases, dims, lbs = pack_bases_numpy(lut)
    print(f'  {len(lut):,} subspaces', flush=True)

    _, stab_e11 = compute_stab_e11()
    branch = build_branch_general(args.rep, stab_e11)
    print(f'\nBranch rep={args.rep} (rank-{branch["rep_rank"]}):',
          flush=True)
    print(f'  fixed_rank1={branch["fixed_rank1"]}, '
          f'fixed_hr_perm={branch["fixed_hr_permanent"]}', flush=True)
    print(f'  free_r1={len(branch["free_r1"])}, '
          f'avail_hr={len(branch["avail_hr"])}, '
          f'orbits={len(branch["hr_orbits"])}, '
          f'stab_order={len(branch["stab_pair"])}', flush=True)

    oracle = GeneralExactKOracle(
        branch=branch, bases=bases, lbs=lbs, keys=keys, rank_s=20,
    )
    print(f'  Oracle precompute: {oracle.precompute_sec:.1f}s, '
          f'{len(oracle.base_tight)} unique masks', flush=True)

    # Phase 1: singleton test at k_max
    k = args.k_max
    print(f'\n=== Singleton survey at k={k} ===', flush=True)
    infeasible_reps = []
    feasible_reps = []
    unknown_reps = []
    results = []

    for orb in branch['hr_orbits']:
        rep_pt = int(orb['rep'])
        res = oracle.query([rep_pt], k,
                           time_limit=args.time_limit,
                           workers=args.workers,
                           capture_support=True)
        status = res.get('status', 'ERROR')
        item = {
            'orbit_rep': rep_pt,
            'orbit_size': int(orb['size']),
            'matrix_rank': matrix_rank_of_mask(rep_pt),
            'k': k,
            'status': status,
            'solve_sec': res.get('solve_sec'),
            'constraints_added': res.get('constraints_added'),
            'empty_constraints': res.get('empty_constraints'),
        }
        if status == 'INFEASIBLE':
            infeasible_reps.append(rep_pt)
        elif status in ('OPTIMAL', 'FEASIBLE'):
            feasible_reps.append(rep_pt)
            item['support_size'] = len(res.get('support_all', []) or [])
        else:
            unknown_reps.append(rep_pt)
        results.append(item)
        sym = '✗' if status == 'INFEASIBLE' else (
            '✓' if status in ('OPTIMAL', 'FEASIBLE') else '?')
        print(f'  orbit {rep_pt:3d} (size={orb["size"]:2d}, '
              f'matrank={matrix_rank_of_mask(rep_pt)}): '
              f'{sym} {status} ({res.get("solve_sec", 0):.1f}s)', flush=True)

    total_eliminated = sum(
        o['size'] for o in branch['hr_orbits']
        if int(o['rep']) in infeasible_reps
    )
    total_surviving = len(branch['avail_hr']) - total_eliminated
    survivor_reps = sorted(feasible_reps + unknown_reps)
    print(f'\nSingleton summary at k={k}: '
          f'{len(infeasible_reps)} infeasible, '
          f'{len(feasible_reps)} feasible, '
          f'{len(unknown_reps)} unknown',flush=True)
    print(f'HR points eliminated: {total_eliminated}/{len(branch["avail_hr"])}',
          flush=True)
    print(f'Surviving HR points: {total_surviving}', flush=True)

    # Phase 2: exhaustive canonical pairs among surviving points
    surviving_pts = []
    for orb in branch['hr_orbits']:
        if int(orb['rep']) in survivor_reps:
            surviving_pts.extend(int(p) for p in orb['members'])
    surviving_pts = sorted(surviving_pts)
    n = len(surviving_pts)

    pair_results = []
    if n >= 2:
        print(f'\n=== Exhaustive canonical pairs among {n} surviving pts ===',
              flush=True)
        canonical_pairs = {}
        for p1, p2 in itertools.combinations(surviving_pts, 2):
            can = canonical_set([p1, p2], branch['stab_pair'])
            if can not in canonical_pairs:
                canonical_pairs[can] = (p1, p2)
        print(f'  {len(canonical_pairs)} canonical pair classes', flush=True)

        infeas_pairs = feas_pairs = unk_pairs = 0
        for can, (p1, p2) in sorted(canonical_pairs.items()):
            res = oracle.query(list(can), k,
                               time_limit=args.time_limit,
                               workers=args.workers,
                               capture_support=True)
            status = res.get('status', 'ERROR')
            entry = {
                'canonical': list(can),
                'status': status,
                'orbit_image_count': orbit_image_count(can, branch['stab_pair']),
                'solve_sec': res.get('solve_sec'),
            }
            if status == 'INFEASIBLE':
                infeas_pairs += 1
            elif status in ('OPTIMAL', 'FEASIBLE'):
                feas_pairs += 1
                entry['support'] = res.get('support_all')
            else:
                unk_pairs += 1
            pair_results.append(entry)
            sym = '✗' if status == 'INFEASIBLE' else (
                '✓' if status in ('OPTIMAL', 'FEASIBLE') else '?')
            if len(pair_results) % 20 == 0 or status != 'INFEASIBLE':
                print(f'  {list(can)}: {sym} {status} ({res.get("solve_sec",0):.1f}s) '
                      f'[{infeas_pairs} inf, {feas_pairs} feas, {unk_pairs} unk '
                      f'/ {len(pair_results)} total]', flush=True)

        print(f'\nPair summary: {infeas_pairs} inf, {feas_pairs} feas, '
              f'{unk_pairs} unk out of {len(canonical_pairs)}', flush=True)
        if infeas_pairs == len(canonical_pairs):
            print(f'\n*** ALL PAIRS INFEASIBLE at k={k} for rep {args.rep} ***',
                  flush=True)

    elapsed = time.time() - t_all
    output = {
        'branch_rep': args.rep,
        'rep_rank': branch['rep_rank'],
        'k': k,
        'total_hr': len(branch['avail_hr']),
        'hr_orbits': len(branch['hr_orbits']),
        'stab_order': len(branch['stab_pair']),
        'free_r1_count': len(branch['free_r1']),
        'singleton_results': results,
        'singleton_summary': {
            'infeasible_reps': infeasible_reps,
            'feasible_reps': feasible_reps,
            'unknown_reps': unknown_reps,
            'survivor_reps': survivor_reps,
            'eliminated': total_eliminated,
            'surviving': total_surviving,
        },
        'surviving_pts': surviving_pts,
        'pair_results': pair_results,
        'pair_summary': {
            'canonical_count': len(pair_results),
            'infeasible': sum(1 for r in pair_results if r['status'] == 'INFEASIBLE'),
            'feasible': sum(1 for r in pair_results if r['status'] in ('OPTIMAL', 'FEASIBLE')),
            'unknown': sum(1 for r in pair_results if r['status'] not in ('INFEASIBLE', 'OPTIMAL', 'FEASIBLE')),
        },
        'all_pairs_infeasible': all(r['status'] == 'INFEASIBLE' for r in pair_results) if pair_results else False,
        'elapsed_sec': elapsed,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(output, indent=2, sort_keys=True,
                                    default=str) + '\n')
    print(f'\nSaved to {args.out} ({elapsed:.1f}s total)')


if __name__ == '__main__':
    main()
