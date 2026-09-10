#!/usr/bin/env python3
"""Certify the finite branch partitions used in the F2 Wang support route.

This is a small reproducible companion for the fixed-E11 proof assembly.  It
checks the projective A-point orbits under Stab(E11), the high-point pair orbits
used in the exact-18 rank-1 case, and the rank-1 count split.  It does not solve
any Wang occupation instance; it records the finite group partitions on which
the branch proofs rest.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from math import comb
from pathlib import Path
from typing import Iterable

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_highpair_batch import high_pair_orbits, single_orbit_map  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11, stab_e11_orbits  # noqa: E402
from wang_capacity_lazy import make_actions, matrix_rank_of_mask, transform_mask  # noqa: E402


def sorted_pair(a: int, b: int) -> tuple[int, int]:
    return (a, b) if a < b else (b, a)


def orbit_images_of_pair(pair: tuple[int, int], actions: Iterable) -> set[tuple[int, int]]:
    imgs = set()
    for act in actions:
        a = transform_mask(pair[0], act)
        b = transform_mask(pair[1], act)
        if a != b:
            imgs.add(sorted_pair(a, b))
    return imgs


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()

    all_points = set(range(1, 512))
    rank_hist_all = Counter(matrix_rank_of_mask(p) for p in all_points)
    actions = make_actions()
    stab = [g for g in actions if transform_mask(E11, g) == E11]

    single_orbits = stab_e11_orbits()
    seen: set[int] = set()
    single_records = []
    disjoint_single = True
    for i, orb in enumerate(single_orbits):
        members = set(map(int, orb['members']))
        if seen & members:
            disjoint_single = False
        seen |= members
        single_records.append({
            'index': i,
            'rep': int(orb['rep']),
            'size': len(members),
            'rank_hist': {str(k): int(v) for k, v in sorted(Counter(matrix_rank_of_mask(p) for p in members).items())},
            'excluded_before_count': sum(len(single_orbits[j]['members']) for j in range(i)),
        })
    single_cover_ok = seen == (all_points - {E11})
    single_sum = sum(r['size'] for r in single_records)

    rank1_points = {p for p in all_points if matrix_rank_of_mask(p) == 1}
    high_points = all_points - rank1_points
    high_reps = {10, 17, 20, 84, 160, 161}
    allowed_high_single_reps_exact18 = {17, 20, 160}
    somap = single_orbit_map()
    allowed_high_points = {p for p in high_points if somap[p] in allowed_high_single_reps_exact18}

    pair_orbits_all = high_pair_orbits(None)
    pair_orbits_allowed = high_pair_orbits(allowed_high_single_reps_exact18)

    def verify_pair_family(pair_orbits, universe: set[int]):
        unseen = {sorted_pair(a, b) for a in universe for b in universe if a < b}
        used: set[tuple[int, int]] = set()
        recs = []
        disjoint = True
        for i, po in enumerate(pair_orbits):
            pair = tuple(map(int, po['pair']))
            imgs = orbit_images_of_pair(pair, stab)
            imgs = {ab for ab in imgs if ab[0] in universe and ab[1] in universe}
            if used & imgs:
                disjoint = False
            used |= imgs
            recs.append({
                'index': i,
                'pair': list(pair),
                'size_from_script': int(po['orbit_size']),
                'size_recomputed': len(imgs),
                'single_orbit_pair_hist': po.get('single_orbit_pair_hist', {}),
                'rank_pair_hist': po.get('rank_pair_hist', {}),
            })
        return {
            'count': len(pair_orbits),
            'size_sum_from_script': sum(int(po['orbit_size']) for po in pair_orbits),
            'size_sum_recomputed': sum(r['size_recomputed'] for r in recs),
            'expected_pairs': comb(len(universe), 2),
            'cover_ok': used == unseen,
            'disjoint_ok': disjoint and len(used) == sum(r['size_recomputed'] for r in recs),
            'records': recs,
        }

    pair_all = verify_pair_family(pair_orbits_all, high_points)
    pair_allowed = verify_pair_family(pair_orbits_allowed, allowed_high_points)

    payload = {
        'problem': 'finite branch partitions for fixed-E11 F2 Wang support search',
        'field': 'F2',
        'E11_mask': E11,
        'group_action_count': len(actions),
        'stab_E11_action_count': len(stab),
        'all_projective_A_points': len(all_points),
        'rank_hist_all_projective_A_points': {str(k): int(v) for k, v in sorted(rank_hist_all.items())},
        'rank1_point_count': len(rank1_points),
        'higher_rank_point_count': len(high_points),
        'single_orbits_after_fixing_E11': {
            'records': single_records,
            'count': len(single_records),
            'size_sum': single_sum,
            'expected_non_E11_points': 510,
            'cover_ok': single_cover_ok,
            'disjoint_ok': disjoint_single and single_sum == len(seen),
            'reps': [r['rep'] for r in single_records],
        },
        'rank1_count_split_fixed_E11': {
            'meaning': 'After the no-rank-1 branch and fixing a rank-1 point to E11, the remaining rank-1-containing branch is split by the total number k of selected rank-1 projective directions.',
            'rank_s': 20,
            'possible_k_after_rank1_ge19_proof': list(range(1, 19)),
            'exact18_high_point_count': 2,
            'k_1_to_17_high_point_count_range': [3, 19],
        },
        'exact18_high_single_orbits': {
            'all_higher_rank_single_reps': sorted(high_reps),
            'excluded_by_single_high_prefix_proofs': [10, 84, 161],
            'remaining_single_reps': sorted(allowed_high_single_reps_exact18),
            'remaining_high_point_count': len(allowed_high_points),
            'remaining_rank_hist': {str(k): int(v) for k, v in sorted(Counter(matrix_rank_of_mask(p) for p in allowed_high_points).items())},
        },
        'high_pair_orbits_all_higher_rank_points': pair_all,
        'high_pair_orbits_exact18_remaining_points': pair_allowed,
        'overall_boolean': {
            'single_orbits_partition_non_E11_points': bool(single_cover_ok and disjoint_single and single_sum == 510),
            'all_high_pair_orbits_partition_pairs': bool(pair_all['cover_ok'] and pair_all['disjoint_ok'] and pair_all['size_sum_recomputed'] == pair_all['expected_pairs']),
            'remaining_exact18_pair_orbits_partition_pairs': bool(pair_allowed['cover_ok'] and pair_allowed['disjoint_ok'] and pair_allowed['size_sum_recomputed'] == pair_allowed['expected_pairs']),
        },
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(args.out),
        'stab_E11_action_count': len(stab),
        'single_reps': payload['single_orbits_after_fixing_E11']['reps'],
        'single_partition_ok': payload['overall_boolean']['single_orbits_partition_non_E11_points'],
        'all_high_pair_orbits': pair_all['count'],
        'all_high_pair_partition_ok': payload['overall_boolean']['all_high_pair_orbits_partition_pairs'],
        'remaining_exact18_pair_orbits': pair_allowed['count'],
        'remaining_exact18_pair_partition_ok': payload['overall_boolean']['remaining_exact18_pair_orbits_partition_pairs'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
