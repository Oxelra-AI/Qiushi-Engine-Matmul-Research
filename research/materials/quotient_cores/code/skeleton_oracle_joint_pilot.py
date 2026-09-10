#!/usr/bin/env python3
"""Safe fixed-rank1-count Wang skeleton oracle and actual joint-orbit pilot.

This script repairs two pitfalls from analysis:

1. Fixed higher-rank subsets are tested at a fixed total rank-1 count k.
   Removing a high point from H while keeping k fixed gives a valid relaxation:
   if H0 is already infeasible, then any full higher-rank set containing H0 is
   infeasible at that same k, because additional high points can only subtract
   from residual Wang capacities.  The earlier auto rule k=20-|H| is not valid
   for extracting forbidden subsets.

2. Symmetry is applied to actual unordered sets under one common stabilizer
   element.  Single-point orbit labels are reported for structure, but they are
   not used as a classification of triples.

The oracle compresses the complete expanded Wang LUT to inequalities on the
remaining rank-1 variables after subtracting fixed rank-1 points and a fixed
higher-rank prefix.  It is still computational evidence unless converted to a
proof-producing CNF/DRAT object, but it is useful for finding family-level
forbidden high subsets and full-LUT admissible A-support candidates.
"""
from __future__ import annotations

import argparse
import itertools
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from precompute_skeleton_system import (  # noqa: E402
    E11,
    build_tight_dict,
    compute_orbits,
    compute_stab_e11,
    compute_stab_pair,
    pack_bases_numpy,
    precompute_base,
    rank1_points,
    vectorized_membership,
    vectorized_multi_membership,
)
from wang_capacity_lazy import (  # noqa: E402
    matrix_rank_of_mask,
    subspace_points_from_basis,
    transform_mask,
    unpack_basis,
)


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def build_tight_with_witness(r1_masks: np.ndarray, caps: np.ndarray, keys: Sequence[int], lbs: np.ndarray) -> tuple[dict[int, int], dict[int, dict]]:
    tight: dict[int, int] = {}
    witness: dict[int, dict] = {}
    for i in range(len(r1_masks)):
        m = int(r1_masks[i])
        c = int(caps[i])
        old = tight.get(m)
        if old is None or c < old:
            tight[m] = c
            witness[m] = {
                'row_index': int(i),
                'key': int(keys[i]),
                'dim': int(keys[i]) & 0xF,
                'lb': int(lbs[i]),
                'base_cap_after_fixed_rank1': c,
                'basis': list(unpack_basis(int(keys[i]))),
            }
    return tight, witness


def canonical_set(points: Sequence[int], group: Sequence[Sequence[int]]) -> tuple[int, ...]:
    return min(tuple(sorted(transform_mask(p, g) for p in points)) for g in group)


def orbit_image_count(points: Sequence[int], group: Sequence[Sequence[int]]) -> int:
    return len({tuple(sorted(transform_mask(p, g) for p in points)) for g in group})


def build_branch(rep: int, stab_e11: Sequence[Sequence[int]]):
    """Build fixed-E11 second-orbit branch data for rep 2 or 16."""
    if matrix_rank_of_mask(rep) != 1:
        raise ValueError(f'this pilot expects a rank-1 second representative; got rep={rep} rank={matrix_rank_of_mask(rep)}')
    e11_orbits = compute_orbits(stab_e11, range(2, 512))
    excluded: set[int] = set()
    found = False
    for orb in e11_orbits:
        if orb['rep'] == rep:
            found = True
            break
        excluded.update(int(p) for p in orb['members'])
    if not found:
        raise ValueError(f'rep {rep} is not a Stab(E11) orbit representative')
    excluded.discard(E11)
    excluded.discard(rep)
    fixed_rank1 = [E11, rep]
    fixed_set = set(fixed_rank1)
    r1_all = rank1_points()
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
        'fixed_rank1': fixed_rank1,
        'excluded': excluded,
        'free_r1': free_r1,
        'avail_hr': avail_hr,
        'stab_pair': stab_pair,
        'hr_orbits': hr_orbits,
        'orbit_label': orbit_label,
    }


def validate_vectorized_membership(keys: Sequence[int], bases: np.ndarray, branch: dict, extra_points: Sequence[int]) -> dict:
    """Compare vectorized membership with exact point enumeration on a small spread of rows."""
    n = len(keys)
    row_indices = sorted(set([0, 1, 2, 511, 43_435, 788_035, n // 5, n // 2, n - 2, n - 1]))
    pts = sorted(set(list(branch['fixed_rank1']) + list(extra_points) + branch['free_r1'][:12] + branch['avail_hr'][:8]))
    mismatches = []
    for p in pts:
        vec = vectorized_membership(bases[row_indices, :], int(p))
        for local_i, idx in enumerate(row_indices):
            slow = int(p) in subspace_points_from_basis(unpack_basis(int(keys[idx])))
            fast = bool(vec[local_i])
            if slow != fast:
                mismatches.append({'row_index': int(idx), 'key': int(keys[idx]), 'point': int(p), 'slow': slow, 'fast': fast})
                if len(mismatches) >= 20:
                    break
        if len(mismatches) >= 20:
            break
    return {
        'rows_tested': row_indices,
        'points_tested': pts,
        'comparison_count': len(row_indices) * len(pts),
        'mismatch_count': len(mismatches),
        'mismatches_head': mismatches,
    }


class ExactKOracle:
    def __init__(self, *, branch: dict, bases: np.ndarray, lbs: np.ndarray, keys: Sequence[int], rank_s: int):
        self.branch = branch
        self.bases = bases
        self.lbs = lbs
        self.keys = keys
        self.rank_s = rank_s
        self.free_r1 = branch['free_r1']
        self.fixed_rank1 = branch['fixed_rank1']
        t0 = time.time()
        self.r1_masks, self.base_caps = precompute_base(bases, lbs, self.fixed_rank1, self.free_r1, rank_s)
        self.base_tight, self.base_witness = build_tight_with_witness(self.r1_masks, self.base_caps, keys, lbs)
        self.precompute_sec = time.time() - t0

    def query(self, fixed_high: Sequence[int], exact_rank1_count: int, *, time_limit: float, workers: int, capture_support: bool = True) -> dict:
        from ortools.sat.python import cp_model
        t0 = time.time()
        fixed_high = sorted(int(p) for p in fixed_high)
        bad = [p for p in fixed_high if p not in set(self.branch['avail_hr'])]
        if bad:
            return {'status': 'INVALID_HIGH_POINTS', 'bad_high_points': bad, 'fixed_high': fixed_high}
        if len(set(fixed_high)) != len(fixed_high):
            return {'status': 'INVALID_DUPLICATE_HIGH_POINTS', 'fixed_high': fixed_high}
        free_needed = int(exact_rank1_count) - len(self.fixed_rank1)
        if free_needed < 0:
            return {'status': 'INFEASIBLE', 'reason': 'exact_rank1_count_less_than_fixed_rank1', 'fixed_high': fixed_high, 'exact_rank1_count': exact_rank1_count}
        if free_needed > len(self.free_r1):
            return {'status': 'INFEASIBLE', 'reason': 'not_enough_free_rank1', 'fixed_high': fixed_high, 'exact_rank1_count': exact_rank1_count}
        if fixed_high:
            hr_count = vectorized_multi_membership(self.bases, fixed_high)
            adjusted_caps = self.base_caps - hr_count.astype(np.int16)
        else:
            hr_count = np.zeros(len(self.base_caps), dtype=np.int8)
            adjusted_caps = self.base_caps
        adjusted_tight = dict(self.base_tight)
        adjusted_witness = dict(self.base_witness)
        if fixed_high:
            affected = np.where(hr_count > 0)[0]
            for i in affected:
                m = int(self.r1_masks[i])
                c = int(adjusted_caps[i])
                old = adjusted_tight.get(m)
                if old is None or c < old:
                    adjusted_tight[m] = c
                    adjusted_witness[m] = {
                        'row_index': int(i),
                        'key': int(self.keys[i]),
                        'dim': int(self.keys[i]) & 0xF,
                        'lb': int(self.lbs[i]),
                        'base_cap_after_fixed_rank1': int(self.base_caps[i]),
                        'fixed_high_in_row': int(hr_count[i]),
                        'residual_cap': c,
                        'basis': list(unpack_basis(int(self.keys[i]))),
                    }

        model = cp_model.CpModel()
        x = [model.NewBoolVar(f'x_{p}') for p in self.free_r1]
        model.Add(sum(x) == free_needed)
        constraints_added = 0
        empty_constraints = 0
        cap_hist = Counter()
        size_cap_hist = Counter()
        witness_head = []
        for mask, cap in adjusted_tight.items():
            bc = int(mask).bit_count()
            cap = int(cap)
            if bc > cap:
                cap_hist[cap] += 1
                size_cap_hist[(bc, cap)] += 1
                if len(witness_head) < 80:
                    w = dict(adjusted_witness.get(int(mask), {}))
                    w.update({'rank1_mask_size': bc, 'rank1_mask': int(mask), 'cap': cap})
                    witness_head.append(w)
                if cap < 0:
                    model.AddBoolOr([])
                    empty_constraints += 1
                    constraints_added += 1
                else:
                    inds = [i for i in range(len(self.free_r1)) if (int(mask) >> i) & 1]
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
        support_free = None
        support_rank1 = None
        if capture_support and status in ('OPTIMAL', 'FEASIBLE'):
            support_free = [self.free_r1[i] for i in range(len(self.free_r1)) if solver.Value(x[i])]
            support_rank1 = sorted(self.fixed_rank1 + support_free)
        return {
            'status': status,
            'status_code': int(st),
            'fixed_high': fixed_high,
            'fixed_high_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in fixed_high).items())),
            'fixed_high_single_orbit_labels': [self.branch['orbit_label'].get(p) for p in fixed_high],
            'fixed_high_canonical': list(canonical_set(fixed_high, self.branch['stab_pair'])) if fixed_high else [],
            'fixed_high_orbit_image_count': orbit_image_count(fixed_high, self.branch['stab_pair']) if fixed_high else 1,
            'exact_rank1_count': int(exact_rank1_count),
            'free_rank1_needed': int(free_needed),
            'constraints_added': int(constraints_added),
            'empty_constraints': int(empty_constraints),
            'cap_hist': dict(sorted(cap_hist.items())),
            'size_cap_hist_head': {f'{a},{b}': c for (a, b), c in list(sorted(size_cap_hist.items()))[:80]},
            'witness_head': witness_head,
            'build_sec': build_sec,
            'solve_sec': solve_sec,
            'solver_walltime': float(solver.WallTime()),
            'solver_conflicts': int(solver.NumConflicts()),
            'solver_branches': int(solver.NumBranches()),
            'support_rank1': support_rank1,
            'support_rank1_size': None if support_rank1 is None else len(support_rank1),
            'support_all_with_fixed_high': None if support_rank1 is None else sorted(support_rank1 + fixed_high),
            'meaning': 'INFEASIBLE at fixed k forbids this high subset in every same-k support containing it. OPTIMAL/FEASIBLE is only a rank-1-completion relaxation unless fixed_high has exactly 20-k points.',
        }


def subset_forbidden_search(oracle: ExactKOracle, name: str, high: Sequence[int], exact_k: int, *, time_limit: float, workers: int, max_subset_size: int | None = None) -> dict:
    high = sorted(int(p) for p in high)
    minimal_infeasible: list[tuple[int, ...]] = []
    queried = []
    max_r = len(high) if max_subset_size is None else min(len(high), int(max_subset_size))
    for r in range(1, max_r + 1):
        for sub in itertools.combinations(high, r):
            sset = set(sub)
            if any(set(mi).issubset(sset) for mi in minimal_infeasible):
                continue
            res = oracle.query(sub, exact_k, time_limit=time_limit, workers=workers, capture_support=(r == len(high)))
            q = {
                'subset': list(sub),
                'size': r,
                'status': res.get('status'),
                'build_sec': res.get('build_sec'),
                'solve_sec': res.get('solve_sec'),
                'constraints_added': res.get('constraints_added'),
                'empty_constraints': res.get('empty_constraints'),
                'canonical': res.get('fixed_high_canonical'),
                'orbit_image_count': res.get('fixed_high_orbit_image_count'),
                'single_orbit_labels': res.get('fixed_high_single_orbit_labels'),
                'witness_head': res.get('witness_head', [])[:5],
                'support_all_with_fixed_high': res.get('support_all_with_fixed_high'),
            }
            queried.append(q)
            if res.get('status') == 'INFEASIBLE':
                minimal_infeasible.append(tuple(sub))
    return {
        'name': name,
        'exact_rank1_count': int(exact_k),
        'full_high': high,
        'full_high_single_orbit_labels': [oracle.branch['orbit_label'].get(p) for p in high],
        'full_high_canonical': list(canonical_set(high, oracle.branch['stab_pair'])),
        'full_high_orbit_image_count': orbit_image_count(high, oracle.branch['stab_pair']),
        'queried_count': len(queried),
        'minimal_infeasible_subsets': [list(x) for x in minimal_infeasible],
        'minimal_infeasible_orbit_image_counts': [orbit_image_count(x, oracle.branch['stab_pair']) for x in minimal_infeasible],
        'queries': queried,
    }


def same_single_orbit_triple_pilot(oracle: ExactKOracle, point: int, exact_k: int, *, time_limit: float, workers: int, max_reps: int = 1000) -> dict:
    """Enumerate actual joint-orbit reps for triples within the single orbit of point."""
    label = oracle.branch['orbit_label'][int(point)]
    members = None
    for orb in oracle.branch['hr_orbits']:
        if int(orb['rep']) == int(label):
            members = [int(p) for p in orb['members']]
            break
    if members is None:
        raise ValueError(f'point {point} not in a higher-rank orbit')
    reps: dict[tuple[int, ...], tuple[int, ...]] = {}
    for tri in itertools.combinations(sorted(members), 3):
        can = canonical_set(tri, oracle.branch['stab_pair'])
        reps.setdefault(can, tri)
    results = []
    infeas = feas = unk = 0
    for j, can in enumerate(sorted(reps), 1):
        if j > max_reps:
            break
        res = oracle.query(can, exact_k, time_limit=time_limit, workers=workers, capture_support=True)
        item = {
            'joint_orbit_rep': list(can),
            'example': list(reps[can]),
            'status': res.get('status'),
            'build_sec': res.get('build_sec'),
            'solve_sec': res.get('solve_sec'),
            'constraints_added': res.get('constraints_added'),
            'empty_constraints': res.get('empty_constraints'),
            'orbit_image_count': res.get('fixed_high_orbit_image_count'),
            'support_all_with_fixed_high': res.get('support_all_with_fixed_high'),
            'witness_head': res.get('witness_head', [])[:5],
        }
        results.append(item)
        if item['status'] == 'INFEASIBLE':
            infeas += 1
        elif item['status'] in ('OPTIMAL', 'FEASIBLE'):
            feas += 1
        else:
            unk += 1
    return {
        'type': 'actual joint-orbit pilot for triples inside one single-point orbit',
        'single_orbit_rep': int(label),
        'single_orbit_size': len(members),
        'raw_triples': len(list(itertools.combinations(members, 3))),
        'joint_orbit_rep_count': len(reps),
        'tested': len(results),
        'infeasible': infeas,
        'feasible_or_optimal': feas,
        'unknown_or_other': unk,
        'results': results,
        'meaning': 'These are genuine common-stabilizer orbits of actual triples in one stratum, not triples of single-point orbit labels.',
    }


def process_branch(rep: int, bases: np.ndarray, lbs: np.ndarray, keys: Sequence[int], rank_s: int, *, time_limit: float, workers: int, do_joint_pilot: bool) -> dict:
    _, stab_e11 = compute_stab_e11()
    branch = build_branch(rep, stab_e11)
    known_extra = []
    if rep == 2:
        configs = [
            ('rep2_old_k17_high_25_194_217', [25, 194, 217], 17),
            ('rep2_old_k16_high_34_52_278_304', [34, 52, 278, 304], 16),
        ]
        known_extra = [25, 194, 217, 34, 52, 278, 304]
    elif rep == 16:
        configs = [
            ('rep16_old_k14_high_19_21_23_25_33_41', [19, 21, 23, 25, 33, 41], 14),
        ]
        known_extra = [19, 21, 23, 25, 33, 41]
    else:
        configs = []
    validation = validate_vectorized_membership(keys, bases, branch, known_extra)
    oracle = ExactKOracle(branch=branch, bases=bases, lbs=lbs, keys=keys, rank_s=rank_s)
    cfg_results = []
    for name, high, k in configs:
        cfg_results.append(subset_forbidden_search(oracle, name, high, k, time_limit=time_limit, workers=workers))
    joint_pilots = []
    if do_joint_pilot and rep == 2:
        # The analysis k=17 witness used three points from the single orbit labelled 25;
        # this pilot covers that omitted relative-position stratum exactly.
        joint_pilots.append(same_single_orbit_triple_pilot(oracle, 25, 17, time_limit=time_limit, workers=workers))
    return {
        'rep': rep,
        'branch': {
            'fixed_rank1': branch['fixed_rank1'],
            'free_r1_count': len(branch['free_r1']),
            'avail_hr_count': len(branch['avail_hr']),
            'excluded_count': len(branch['excluded']),
            'stab_pair_order': len(branch['stab_pair']),
            'hr_orbits': [{'rep': int(o['rep']), 'size': int(o['size']), 'rank_hist': o['rank_hist']} for o in branch['hr_orbits']],
        },
        'vectorized_membership_validation': validation,
        'oracle_precompute_sec': oracle.precompute_sec,
        'base_mask_count': len(oracle.base_tight),
        'known_config_subset_searches': cfg_results,
        'joint_orbit_pilots': joint_pilots,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--rank-s', type=int, default=20)
    ap.add_argument('--time-limit', type=float, default=12.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--reps', default='2,16')
    ap.add_argument('--no-joint-pilot', action='store_true')
    args = ap.parse_args()

    t_all = time.time()
    print('Loading LUT...', flush=True)
    lut, meta = load_lut(args.lut)
    keys = list(lut.keys())
    print(f'  {len(lut):,} rows coverage={meta.get("coverage_ok")} conflicts={meta.get("conflict_count")}', flush=True)
    print('Packing bases...', flush=True)
    bases, dims, lbs = pack_bases_numpy(lut)
    print(f'  packed bases shape={bases.shape}', flush=True)
    reps = [int(x) for x in args.reps.replace(';', ',').split(',') if x.strip()]
    branches = []
    for rep in reps:
        print(f'\n=== Processing fixed-E11 rep {rep} ===', flush=True)
        branches.append(process_branch(rep, bases, lbs, keys, args.rank_s, time_limit=args.time_limit, workers=args.workers, do_joint_pilot=not args.no_joint_pilot))
    result = {
        'problem': 'analysis repaired fixed-k skeleton oracle validation and actual joint-orbit pilot',
        'field': 'F2',
        'rank_s_for_wang_capacities': args.rank_s,
        'lut_meta_brief': {'coverage_ok': meta.get('coverage_ok'), 'conflict_count': meta.get('conflict_count'), 'subspace_count': meta.get('subspace_count'), 'lut_len': len(lut)},
        'time_limit_per_cp_sat_query_sec': args.time_limit,
        'branches': branches,
        'elapsed_sec': time.time() - t_all,
        'interpretation': 'Use INFEASIBLE subset results only as fixed-rank1-count high-subset exclusions under the same branch; use orbit_image_count under the common stabilizer for symmetry transfer. Feasible subset relaxations are not full A-supports unless the fixed high size equals 20-k and all returned points pass a complete LUT scan.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(args.out),
        'elapsed_sec': result['elapsed_sec'],
        'branch_summaries': [
            {
                'rep': b['rep'],
                'membership_mismatches': b['vectorized_membership_validation']['mismatch_count'],
                'known_searches': [
                    {
                        'name': s['name'],
                        'minimal_infeasible_subsets': s['minimal_infeasible_subsets'],
                        'queried_count': s['queried_count'],
                    } for s in b['known_config_subset_searches']
                ],
                'joint_pilots': [
                    {
                        'single_orbit_rep': p['single_orbit_rep'],
                        'joint_orbit_rep_count': p['joint_orbit_rep_count'],
                        'tested': p['tested'],
                        'infeasible': p['infeasible'],
                        'feasible_or_optimal': p['feasible_or_optimal'],
                        'unknown_or_other': p['unknown_or_other'],
                    } for p in b['joint_orbit_pilots']
                ],
            } for b in branches
        ],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
