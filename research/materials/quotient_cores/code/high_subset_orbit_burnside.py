#!/usr/bin/env python3
"""Burnside counts for actual higher-rank subset orbits in fixed-E11 branches.

This counts unordered m-subsets under the common branch stabilizer, preserving
relative positions.  It is used to replace the invalid analysis count of triples
of single-point orbit labels.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from skeleton_oracle_joint_pilot import build_branch  # noqa: E402
from precompute_skeleton_system import compute_stab_e11  # noqa: E402
from wang_capacity_lazy import transform_mask  # noqa: E402


def fixed_subset_count_from_cycles(cycle_lengths, m: int) -> int:
    """Number of m-subsets fixed setwise by a permutation with given cycle lengths."""
    # Generating function prod_l (1+x^l)^{c_l}; m is at most small here.
    coeff = [0] * (m + 1)
    coeff[0] = 1
    hist = Counter(cycle_lengths)
    for l, c in hist.items():
        if l > m:
            continue
        for _ in range(c):
            for j in range(m, l - 1, -1):
                coeff[j] += coeff[j - l]
    return coeff[m]


def cycle_lengths_of_action(points, img):
    point_set = set(points)
    unseen = set(points)
    lengths = []
    while unseen:
        start = next(iter(unseen))
        cur = start
        length = 0
        while cur in unseen:
            unseen.remove(cur)
            length += 1
            cur = transform_mask(cur, img)
            if cur not in point_set:
                raise RuntimeError('action left branch universe')
        lengths.append(length)
    return lengths


def process_rep(rep: int, ms: list[int]) -> dict:
    _, stab_e11 = compute_stab_e11()
    branch = build_branch(rep, stab_e11)
    points = branch['avail_hr']
    rows = []
    sums = {m: 0 for m in ms}
    cycle_hist_summary = Counter()
    t0 = time.time()
    for idx, img in enumerate(branch['stab_pair']):
        lens = cycle_lengths_of_action(points, img)
        ch = Counter(lens)
        cycle_hist_summary[tuple(sorted(ch.items()))] += 1
        fixed_counts = {m: fixed_subset_count_from_cycles(lens, m) for m in ms}
        for m, val in fixed_counts.items():
            sums[m] += val
        rows.append({'group_index': idx, 'cycle_hist': dict(sorted(ch.items())), 'fixed_m_subsets': fixed_counts})
    orbit_counts = {m: sums[m] // len(branch['stab_pair']) for m in ms}
    raw_counts = {m: math.comb(len(points), m) for m in ms}
    return {
        'rep': rep,
        'fixed_rank1': branch['fixed_rank1'],
        'avail_hr_count': len(points),
        'stab_pair_order': len(branch['stab_pair']),
        'single_point_hr_orbits': [{'rep': int(o['rep']), 'size': int(o['size']), 'rank_hist': o['rank_hist']} for o in branch['hr_orbits']],
        'raw_subset_counts': raw_counts,
        'burnside_orbit_counts': orbit_counts,
        'cycle_hist_summary': [{'cycle_hist': dict(k), 'multiplicity': v} for k, v in cycle_hist_summary.items()],
        'group_rows': rows,
        'elapsed_sec': time.time() - t0,
        'meaning': 'Counts are for actual unordered higher-rank subsets under one common Stab(E11,rep) action; they preserve relative incidence.',
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--reps', default='2,16')
    ap.add_argument('--m', default='2,3,4,5,6')
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    reps = [int(x) for x in args.reps.replace(';', ',').split(',') if x.strip()]
    ms = [int(x) for x in args.m.replace(';', ',').split(',') if x.strip()]
    payload = {'problem': 'Burnside counts for actual high-subset joint orbits', 'branches': [process_rep(r, ms) for r in reps]}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(args.out),
        'branches': [
            {
                'rep': b['rep'],
                'avail_hr_count': b['avail_hr_count'],
                'stab_pair_order': b['stab_pair_order'],
                'raw_subset_counts': b['raw_subset_counts'],
                'burnside_orbit_counts': b['burnside_orbit_counts'],
            } for b in payload['branches']
        ],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
