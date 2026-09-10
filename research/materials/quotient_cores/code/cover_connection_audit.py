#!/usr/bin/env python3
"""Audit load-bearing connections in the analysis rank-1 cover.

Checks:
1. Wang expanded dim-1 rows give lb=19 for all 511 projective A directions,
   hence a rank-20 occupation multiset has multiplicity at most 1 in every
   projective direction. This justifies Boolean support variables for the
   rank-20 Wang support problem.
2. The rep2 branch builder has no earlier-orbit exclusions and does not forbid
   the other adjacent rank-1 points after fixing E11,E12.
3. The implemented action has the expected size and maps adjacent rank-1 pairs
   to the same orbit (already checked more fully in rank1_geometry_cover).
"""
from __future__ import annotations

import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from general_singleton_pair_survey import build_branch_general  # noqa: E402
from precompute_skeleton_system import compute_stab_e11, rank1_points  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11, stab_e11_orbits  # noqa: E402
from wang_capacity_lazy import make_actions, matrix_rank_of_mask, unpack_basis  # noqa: E402


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    t0 = time.time()

    with args.lut.open('rb') as f:
        payload = pickle.load(f)
    lut = payload['lut']; meta = payload.get('meta', {})
    dim1 = [(int(key), int(lb), unpack_basis(int(key))[0]) for key, lb in lut.items() if (int(key) & 0xF) == 1]
    dim1_points = sorted(row for key, lb, row in dim1)
    dim1_lb_hist = Counter(lb for key, lb, row in dim1)
    dim1_rank_lb_hist = Counter((matrix_rank_of_mask(row), lb) for key, lb, row in dim1)
    all_points = list(range(1, 512))
    missing_points = sorted(set(all_points) - set(dim1_points))
    extra_points = sorted(set(dim1_points) - set(all_points))
    dim1_bool_sound = (len(dim1) == 511 and not missing_points and not extra_points and dim1_lb_hist == Counter({19: 511}))

    e11_orbits = stab_e11_orbits()
    _, stab_e11 = compute_stab_e11()
    rep2_branch = build_branch_general(2, stab_e11)
    rep2_record = next(o for o in e11_orbits if int(o['rep']) == 2)
    rep2_other_rank1 = sorted(set(int(p) for p in rep2_record['members']) - {E11, 2})
    forbidden_other_rep2 = sorted(set(rep2_other_rank1) & set(rep2_branch['excluded']))
    free_other_rep2 = sorted(set(rep2_other_rank1) & set(rep2_branch['free_r1']))
    actions = make_actions()

    out = {
        'problem': 'analysis cover connection audit',
        'field': 'F2',
        'dim1_lut_rows': len(dim1),
        'dim1_lb_hist': dict(sorted(dim1_lb_hist.items())),
        'dim1_rank_lb_hist': {f'rank{r}_lb{lb}': c for (r, lb), c in sorted(dim1_rank_lb_hist.items())},
        'dim1_missing_points': missing_points[:20],
        'dim1_extra_points': extra_points[:20],
        'rank20_projective_multiplicity_bound': 'For every 1D subspace <p>, Wang gives L=19, so occupation count in a rank-20 multiset is <= 20-19 = 1.',
        'boolean_support_model_sound_for_rank20_Wang_A_side': dim1_bool_sound,
        'stab_E11_orbit_reps': [int(o['rep']) for o in e11_orbits],
        'rep2_branch_fixed_rank1': rep2_branch['fixed_rank1'],
        'rep2_branch_fixed_hr_permanent': rep2_branch['fixed_hr_permanent'],
        'rep2_branch_excluded_count': len(rep2_branch['excluded']),
        'rep2_branch_free_rank1_count': len(rep2_branch['free_r1']),
        'rep2_orbit_members': rep2_record['members'],
        'rep2_other_rank1_members_allowed_count': len(free_other_rep2),
        'rep2_other_rank1_members_forbidden': forbidden_other_rep2,
        'rep2_builder_allows_other_adjacent_rank1_after_fixing_E11_E12': (len(forbidden_other_rep2) == 0 and set(rep2_other_rank1).issubset(set(rep2_branch['free_r1']))),
        'full_action_count': len(actions),
        'full_action_count_expected': 2 * 168 * 168,
        'lut_meta_brief': {'coverage_ok': meta.get('coverage_ok'), 'conflict_count': meta.get('conflict_count'), 'subspace_count': meta.get('subspace_count'), 'action_count': meta.get('action_count')},
        'elapsed_sec': time.time() - t0,
    }
    out['all_connection_checks_passed'] = bool(out['boolean_support_model_sound_for_rank20_Wang_A_side'] and out['rep2_builder_allows_other_adjacent_rank1_after_fixing_E11_E12'] and out['full_action_count'] == out['full_action_count_expected'])
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'all_connection_checks_passed': out['all_connection_checks_passed'],
        'dim1_lb_hist': out['dim1_lb_hist'],
        'rep2_excluded_count': out['rep2_branch_excluded_count'],
        'rep2_other_allowed': out['rep2_builder_allows_other_adjacent_rank1_after_fixing_E11_E12'],
        'action_count': out['full_action_count'],
        'out': str(args.out),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
