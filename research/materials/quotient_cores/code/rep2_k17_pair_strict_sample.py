#!/usr/bin/env python3
"""Sample surviving rep2/k17 higher-rank pair orbits for strict ruling effects.

For a fixed higher-rank pair P in the adjacent-pair branch and exact rank-1
count k=17, the skeleton query fixes {1,2} plus P and asks whether the remaining
15 rank-1 points can satisfy all Wang occupation rows.  If this is already
INFEASIBLE, every full support containing P is impossible, independently of the
third high-rank point.  This is the old monotone actual-set pair method.

The new question after analysis is stricter: are there pair orbits for which
Wang-only is feasible/optimal but the transported ruling-line clauses make the
rank-1 completion infeasible?  Such pairs would be genuinely new reusable
constraints from the ruling-line theorem.
"""
from __future__ import annotations

import itertools
import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from general_singleton_pair_survey import GeneralExactKOracle, build_branch_general  # noqa:E402
from precompute_skeleton_system import compute_stab_e11, pack_bases_numpy  # noqa:E402
from skeleton_oracle_joint_pilot import canonical_set, orbit_image_count  # noqa:E402
from rep2_k17_ruling_guided import RulingExactKOracle, load_lut_pickle, setwise_stabilizer_pair  # noqa:E402
from wang_capacity_lazy import matrix_rank_of_mask, transform_mask  # noqa:E402

FEAS = {'OPTIMAL', 'FEASIBLE'}


def load_json(path: Path):
    return json.loads(path.read_text())


def all_images(points, group):
    return sorted({tuple(sorted(transform_mask(int(p), g) for p in points)) for g in group})


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--k', type=int, default=17)
    ap.add_argument('--max-per-ranktype', type=int, default=6)
    ap.add_argument('--time-limit', type=float, default=15.0)
    ap.add_argument('--workers', type=int, default=8)
    args = ap.parse_args()
    t_all = time.time()

    _, stab_e11 = compute_stab_e11()
    branch = build_branch_general(2, stab_e11)
    stab = setwise_stabilizer_pair(1, 2)

    # Remove only k=17 singleton-INFEASIBLE high orbits, conservatively transported
    # under the setwise branch stabilizer.
    sdata = load_json(Path('data/coverage/rep2_k17_survivors_corrected.json'))
    forbidden = set()
    for row in sdata.get('phase1_results', []):
        if row.get('status') == 'INFEASIBLE' and int(row.get('k', args.k)) == args.k:
            rep = int(row['orbit_rep'])
            forbidden.update(p for (p,) in all_images([rep], stab) if matrix_rank_of_mask(p) > 1)
    vertices = [p for p in range(1, 512) if matrix_rank_of_mask(p) > 1 and p not in forbidden]

    # Old imported pair constraints, canonicalized under setwise stabilizer.
    old = load_json(Path('data/guided_clique/merged_guided_constraints_v3.json'))
    old_pairs = set()
    for c in old.get('constraints', []):
        if int(c.get('branch_second_rep', 2)) != 2:
            continue
        if int(c.get('exact_rank1_count', args.k)) > args.k:
            continue
        pts = c.get('canonical_subset', [])
        if len(pts) == 2:
            old_pairs.add(tuple(canonical_set([int(x) for x in pts], stab)))

    # All current pair orbits after singleton removals.
    by_rank = defaultdict(list)
    seen = set()
    for a, b in itertools.combinations(vertices, 2):
        can = tuple(canonical_set([a, b], stab))
        if can in seen:
            continue
        seen.add(can)
        if can in old_pairs:
            continue
        rt = tuple(sorted(matrix_rank_of_mask(p) for p in can))
        by_rank[rt].append(can)
    for rt in by_rank:
        by_rank[rt].sort()

    selected = []
    for rt in sorted(by_rank):
        arr = by_rank[rt]
        if not arr:
            continue
        # deterministic spread through the list rather than just lexicographic head
        m = min(args.max_per_ranktype, len(arr))
        if m == 1:
            inds = [0]
        else:
            inds = sorted({round(i * (len(arr) - 1) / (m - 1)) for i in range(m)})
        for i in inds:
            selected.append(arr[int(i)])

    print(f'Loading LUT {args.lut}...', flush=True)
    lut, meta = load_lut_pickle(args.lut)
    keys = list(lut.keys())
    bases, dims, lbs = pack_bases_numpy(lut)
    print(f'  rows={len(lut):,}; selected pair orbits={len(selected)}', flush=True)
    wang = GeneralExactKOracle(branch=branch, bases=bases, lbs=lbs, keys=keys, rank_s=20)
    ruling = RulingExactKOracle(branch=branch, bases=bases, lbs=lbs, keys=keys, rank_s=20, prefix=[1, 2])

    rows = []
    status_pairs = Counter()
    strict = []
    for i, can in enumerate(selected, 1):
        can = tuple(int(x) for x in can)
        print(f'[{i}/{len(selected)}] pair={list(can)} rank={tuple(matrix_rank_of_mask(p) for p in can)}', flush=True)
        wq = wang.query(can, args.k, time_limit=args.time_limit, workers=args.workers, capture_support=True)
        rq = ruling.query(can, args.k, time_limit=args.time_limit, workers=args.workers, capture_support=True)
        row = {
            'canonical_pair': list(can),
            'rank_pair': [matrix_rank_of_mask(p) for p in can],
            'orbit_image_count_setwise': orbit_image_count(can, stab),
            'wang_only_status': wq.get('status'),
            'wang_only_solve_sec': wq.get('solve_sec'),
            'ruling_status': rq.get('status'),
            'ruling_solve_sec': rq.get('solve_sec'),
            'ruling_strict_vs_wang_only': rq.get('status') == 'INFEASIBLE' and wq.get('status') in FEAS,
            'both_feasible': (wq.get('status') in FEAS and rq.get('status') in FEAS),
        }
        if row['both_feasible']:
            row['wang_support_rank1'] = wq.get('support_rank1')
            row['ruling_support_rank1'] = rq.get('support_rank1')
        if row['ruling_strict_vs_wang_only']:
            strict.append(row)
        status_pairs[(wq.get('status'), rq.get('status'))] += 1
        rows.append(row)

    payload = {
        'schema': 'rep2_k17_pair_strict_sample_v1',
        'problem': 'sample whether transported ruling-line exclusions create new fixed-pair impossibilities in rep2/k17',
        'field': 'F2',
        'fixed_prefix': [1, 2],
        'exact_rank1_count': args.k,
        'vertex_count_after_old_singletons': len(vertices),
        'setwise_stabilizer_order': len(stab),
        'old_pair_canonical_count': len(old_pairs),
        'unimported_pair_orbit_count_by_rank': {str(k): len(v) for k, v in sorted(by_rank.items())},
        'selected_pair_count': len(selected),
        'selected_by_rank': {str(k): sum(1 for p in selected if tuple(sorted(matrix_rank_of_mask(x) for x in p)) == k) for k in sorted(by_rank)},
        'status_pair_hist': {str(k): v for k, v in sorted(status_pairs.items(), key=lambda kv: str(kv[0]))},
        'strict_ruling_pair_count': len(strict),
        'strict_ruling_pairs': strict,
        'rows': rows,
        'ruling_meta': ruling.ruling_meta,
        'lut_meta_brief': {'coverage_ok': meta.get('coverage_ok'), 'conflict_count': meta.get('conflict_count'), 'subspace_count': meta.get('subspace_count')},
        'meaning': 'If strict_ruling_pair_count is zero, this sample found no fixed-pair incompatibility caused by ruling-line transport; Wang-only occupation already explains all sampled pair exclusions. Feasible rows are still only rank-1 skeleton completions, not full 20-point A-supports.',
        'elapsed_sec': time.time() - t_all,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True, default=str) + '\n')
    print(json.dumps({
        'selected': len(selected),
        'strict': len(strict),
        'status_pair_hist': payload['status_pair_hist'],
        'elapsed_sec': payload['elapsed_sec'],
    }, sort_keys=True))


if __name__ == '__main__':
    main()
