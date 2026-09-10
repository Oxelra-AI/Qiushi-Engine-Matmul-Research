#!/usr/bin/env python3
"""Extract reusable forbidden high-subset constraints from guided clique runs.

The guided oracle output stores, for each rejected full higher-rank set, a shrink
record with minimal infeasible singleton/pair/higher-order subsets.  This script
turns those CP-SAT oracle rejections into the same constraint-list format used by
`guided_clique_oracle.py`, so subsequent guided runs start from the learned
family obstructions instead of rediscovering them.

The resulting file is still computational evidence; it is not a mathematical
certificate until the underlying oracle rejections are independently checked.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from general_singleton_pair_survey import build_branch_general  # noqa: E402
from precompute_skeleton_system import compute_stab_e11  # noqa: E402
from skeleton_oracle_joint_pilot import canonical_set, orbit_image_count  # noqa: E402
from wang_capacity_lazy import matrix_rank_of_mask, transform_mask  # noqa: E402


def orbit_images(points, group):
    return sorted({tuple(sorted(transform_mask(int(p), g) for p in points)) for g in group})


def normalize_constraint(c, branch, source):
    rep = int(c['branch_second_rep'])
    k = int(c['exact_rank1_count'])
    pts = [int(x) for x in c['canonical_subset']]
    can = tuple(canonical_set(pts, branch['stab_pair'])) if pts else tuple()
    imgs = [list(x) for x in orbit_images(can, branch['stab_pair'])]
    return {
        'branch_second_rep': rep,
        'exact_rank1_count': k,
        'canonical_subset': list(can),
        'forbidden_subset_size': len(can),
        'orbit_image_count': len(imgs),
        'orbit_images': imgs,
        'rank_hist': dict(sorted(__import__('collections').Counter(matrix_rank_of_mask(p) for p in can).items())),
        'source': source,
        'meaning': 'No same-branch support at this or larger rank-1 count may contain all points of any listed branch-stabilizer image, conditional on the CP-SAT skeleton-oracle infeasibility result.',
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', type=Path, default=None)
    ap.add_argument('--guided', type=Path, action='append', default=[])
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()

    _, stab_e11 = compute_stab_e11()
    branch_cache = {}
    merged = {}
    inputs = []

    def get_branch(rep):
        rep = int(rep)
        if rep not in branch_cache:
            branch_cache[rep] = build_branch_general(rep, stab_e11)
        return branch_cache[rep]

    if args.base and args.base.exists():
        b = json.loads(args.base.read_text())
        inputs.append(str(args.base))
        for c in b.get('constraints', []):
            rep = int(c['branch_second_rep'])
            branch = get_branch(rep)
            nc = normalize_constraint(c, branch, source=c.get('source', str(args.base)))
            key = (nc['branch_second_rep'], nc['exact_rank1_count'], tuple(nc['canonical_subset']))
            merged[key] = nc

    for path in args.guided:
        g = json.loads(path.read_text())
        inputs.append(str(path))
        rep = int(g['branch_rep'])
        k = int(g['k'])
        branch = get_branch(rep)
        for it in g.get('iterations', []):
            shrink = it.get('shrink') or {}
            # New guided runs store reusable_infeasible_subsets; old runs stored
            # minimal_infeasible_subsets.  If shrink found no smaller subset,
            # reusable_infeasible_subsets may contain the full high set that was
            # directly queried INFEASIBLE.
            sub_list = shrink.get('reusable_infeasible_subsets')
            if sub_list is None:
                sub_list = shrink.get('infeasible_subsets_at_first_detected_size')
            if sub_list is None:
                sub_list = shrink.get('minimal_infeasible_subsets', [])
            for sub in sub_list:
                raw = {
                    'branch_second_rep': rep,
                    'exact_rank1_count': k,
                    'canonical_subset': list(sub),
                }
                nc = normalize_constraint(raw, branch, source=str(path))
                nc['source_iteration'] = it.get('iteration')
                nc['source_full_high'] = it.get('high')
                nc['source_full_high_status'] = it.get('query_status')
                key = (nc['branch_second_rep'], nc['exact_rank1_count'], tuple(nc['canonical_subset']))
                merged[key] = nc

    constraints = [merged[k] for k in sorted(merged)]
    by_rep_k = {}
    for c in constraints:
        by_rep_k.setdefault(f"rep{c['branch_second_rep']}_k{c['exact_rank1_count']}", 0)
        by_rep_k[f"rep{c['branch_second_rep']}_k{c['exact_rank1_count']}"] += 1
    payload = {
        'problem': 'merged guided high-subset constraints for Wang skeleton support search',
        'constraint_count': len(constraints),
        'inputs': inputs,
        'constraints_by_rep_k': dict(sorted(by_rep_k.items())),
        'constraints': constraints,
        'proof_status': 'CP-SAT skeleton evidence only; constraints guide search and define proof targets but do not by themselves establish a lower bound.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(args.out),
        'constraint_count': len(constraints),
        'constraints_by_rep_k': payload['constraints_by_rep_k'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
