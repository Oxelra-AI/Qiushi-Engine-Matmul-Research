#!/usr/bin/env python3
"""Extract symmetry-transferable forbidden high-subset constraints from a skeleton pilot.

Input is the analysis skeleton_oracle_joint_pilot summary.  For each INFEASIBLE
minimal high subset found at a fixed rank-1 count k and branch, this writes the
actual orbit of the subset under the common branch stabilizer.  Each image H0
encodes a master-search constraint sum_{h in H0} y_h <= |H0|-1 for the same
branch and the same k.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from skeleton_oracle_joint_pilot import build_branch, canonical_set  # noqa: E402
from precompute_skeleton_system import compute_stab_e11  # noqa: E402
from wang_capacity_lazy import transform_mask  # noqa: E402


def orbit_images(points, group):
    return sorted({tuple(sorted(transform_mask(int(p), g) for p in points)) for g in group})


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--summary', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    summary = json.loads(args.summary.read_text())
    _, stab_e11 = compute_stab_e11()
    constraints = []
    for b in summary['branches']:
        rep = int(b['rep'])
        branch = build_branch(rep, stab_e11)
        group = branch['stab_pair']
        seen = set()
        for search in b.get('known_config_subset_searches', []):
            exact_k = int(search['exact_rank1_count'])
            for q in search.get('queries', []):
                if q.get('status') != 'INFEASIBLE':
                    continue
                subset = tuple(int(x) for x in q['subset'])
                can = tuple(canonical_set(subset, group))
                key = (rep, exact_k, can)
                if key in seen:
                    continue
                seen.add(key)
                imgs = orbit_images(can, group)
                constraints.append({
                    'branch_second_rep': rep,
                    'exact_rank1_count': exact_k,
                    'forbidden_subset_size': len(can),
                    'canonical_subset': list(can),
                    'orbit_image_count': len(imgs),
                    'orbit_images': [list(x) for x in imgs],
                    'master_constraint': f"sum_y[{','.join(map(str, can))}] <= {len(can)-1} and all branch-stabilizer images",
                    'source_search': search['name'],
                    'source_subset': list(subset),
                    'source_query': {
                        'status': q.get('status'),
                        'build_sec': q.get('build_sec'),
                        'solve_sec': q.get('solve_sec'),
                        'constraints_added': q.get('constraints_added'),
                        'empty_constraints': q.get('empty_constraints'),
                        'witness_head': q.get('witness_head', [])[:10],
                    },
                    'meaning': 'At this fixed rank-1 count and branch, no support may contain all points of any listed orbit image. This is a CP-SAT skeleton-oracle result, not yet a DRAT certificate.',
                })
    payload = {
        'problem': 'symmetry-transferable high-subset exclusions from analysis fixed-k skeleton oracle',
        'source_summary': str(args.summary),
        'constraint_count': len(constraints),
        'constraints': constraints,
        'interpretation': 'Each constraint is valid only for the listed branch and exact rank-1 count. Symmetry transfer uses a single common branch-stabilizer element on the whole subset.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(args.out),
        'constraint_count': len(constraints),
        'summary': [
            {'rep': c['branch_second_rep'], 'k': c['exact_rank1_count'], 'subset': c['canonical_subset'], 'images': c['orbit_image_count']}
            for c in constraints
        ],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
