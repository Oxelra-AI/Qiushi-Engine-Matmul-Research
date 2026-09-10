#!/usr/bin/env python3
"""Cheap orbit profile for rep2 exact-k17 higher-rank pairs.

Counts actual high-rank pair orbits under the setwise stabilizer of {E11,E12}
and compares them with the old guided-pair constraints.  This avoids launching
another large enumeration until we know the scale and what part of the previous
actual-set pair/clique work is being reused.
"""
from __future__ import annotations

import itertools
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from general_singleton_pair_survey import build_branch_general  # noqa:E402
from precompute_skeleton_system import compute_stab_e11  # noqa:E402
from skeleton_oracle_joint_pilot import canonical_set  # noqa:E402
from wang_capacity_lazy import make_actions, matrix_rank_of_mask, transform_mask  # noqa:E402


def setwise_stabilizer_pair(p: int = 1, q: int = 2):
    pair = {int(p), int(q)}
    return [g for g in make_actions() if {transform_mask(p, g), transform_mask(q, g)} == pair]


def load_json(path: Path):
    return json.loads(path.read_text())


def main():
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('data/rep2_k17_ruling_guided/pair_orbit_profile.json')
    _, stab_e11 = compute_stab_e11()
    branch = build_branch_general(2, stab_e11)
    stab_setwise = setwise_stabilizer_pair(1, 2)

    # Conservative k=17 singleton eliminations from the corrected analysis file.
    sdata = load_json(Path('data/coverage/rep2_k17_survivors_corrected.json'))
    forbidden = set()
    singleton_removed = []
    for row in sdata.get('phase1_results', []):
        if row.get('status') == 'INFEASIBLE':
            rep = int(row['orbit_rep'])
            imgs = sorted({transform_mask(rep, g) for g in stab_setwise})
            imgs = [p for p in imgs if matrix_rank_of_mask(p) > 1]
            before = len(forbidden)
            forbidden.update(imgs)
            singleton_removed.append({'rep': rep, 'images': len(imgs), 'new_removed': len(forbidden)-before})
    all_hr = [p for p in range(1, 512) if matrix_rank_of_mask(p) > 1]
    vertices = [p for p in all_hr if p not in forbidden]

    canon_to_example = {}
    orbit_size_hist = Counter()
    rank_pair_hist = Counter()
    for a, b in itertools.combinations(vertices, 2):
        can = tuple(canonical_set([a, b], stab_setwise))
        if can not in canon_to_example:
            canon_to_example[can] = (a, b)
            imgs = {tuple(sorted(transform_mask(p, g) for p in can)) for g in stab_setwise}
            orbit_size_hist[len(imgs)] += 1
            rank_pair_hist[tuple(sorted(matrix_rank_of_mask(p) for p in can))] += 1

    old_constraints = load_json(Path('data/guided_clique/merged_guided_constraints_v3.json'))
    old_pair_can = set()
    old_singletons = set()
    for c in old_constraints.get('constraints', []):
        if int(c.get('branch_second_rep', 2)) != 2:
            continue
        if int(c.get('exact_rank1_count', 17)) > 17:
            continue
        pts = tuple(int(x) for x in c.get('canonical_subset', []))
        if len(pts) == 1:
            old_singletons.add(tuple(canonical_set(pts, stab_setwise)))
        elif len(pts) == 2:
            old_pair_can.add(tuple(canonical_set(pts, stab_setwise)))

    all_pair_can = set(canon_to_example)
    covered_old = old_pair_can & all_pair_can
    not_old = sorted(all_pair_can - old_pair_can)
    old_not_current = sorted(old_pair_can - all_pair_can)

    # Greedy clique in graph after old pair exclusions to show scale of actual-set work.
    idx = {p: i for i, p in enumerate(vertices)}
    adj = [(1 << len(vertices)) - 1 for _ in vertices]
    for i in range(len(vertices)):
        adj[i] &= ~(1 << i)
    removed_edges = 0
    for can in covered_old:
        imgs = {tuple(sorted(transform_mask(p, g) for p in can)) for g in stab_setwise}
        for x, y in imgs:
            if x in idx and y in idx:
                i, j = idx[x], idx[y]
                if (adj[i] >> j) & 1:
                    adj[i] &= ~(1 << j)
                    adj[j] &= ~(1 << i)
                    removed_edges += 1
    degrees = [a.bit_count() for a in adj]

    # Deterministic target-clique finder using the existing tested helper.
    from guided_clique_oracle import find_clique_with_hyperedges
    clique, stats = find_clique_with_hyperedges(adj, 3, [], set(), vertices, stab_setwise, max_nodes=2_000_000)
    clique_pts = [vertices[i] for i in clique] if clique is not None else None
    clique_can = tuple(canonical_set(clique_pts, stab_setwise)) if clique_pts else None

    payload = {
        'schema': 'rep2_k17_pair_orbit_profile_v1',
        'fixed_prefix': [1, 2],
        'exact_rank1_count': 17,
        'target_high_rank_points': 3,
        'pointwise_stabilizer_order': len(branch['stab_pair']),
        'setwise_stabilizer_order': len(stab_setwise),
        'all_high_rank_points': len(all_hr),
        'singleton_removed': singleton_removed,
        'vertices_after_singletons': len(vertices),
        'vertex_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in vertices).items())),
        'canonical_pair_orbits_total': len(all_pair_can),
        'canonical_pair_orbit_size_hist': dict(sorted(orbit_size_hist.items())),
        'canonical_pair_rank_hist': {str(k): v for k, v in sorted(rank_pair_hist.items())},
        'old_pair_constraint_canonicals': len(old_pair_can),
        'old_pair_constraints_cover_current_pair_orbits': len(covered_old),
        'old_pair_constraints_not_current_after_singletons': len(old_not_current),
        'current_pair_orbits_not_in_old_constraints': len(not_old),
        'not_old_examples': [list(x) for x in not_old[:30]],
        'old_not_current_examples': [list(x) for x in old_not_current[:20]],
        'edge_count_after_old_pairs': sum(degrees)//2,
        'removed_edges_by_old_pair_orbits': removed_edges,
        'degree_hist_after_old_pairs': dict(sorted(Counter(degrees).items())),
        'target_clique_after_old_pairs': clique_pts,
        'target_clique_canonical': list(clique_can) if clique_can else None,
        'target_clique_search_stats': stats,
        'meaning': 'Scale profile only: old CP-SAT pair constraints cover a small fraction of actual pair orbits, and a target high-rank triple still exists in the conservative graph unless target_clique_after_old_pairs is null.',
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'vertices': payload['vertices_after_singletons'],
        'pair_orbits_total': payload['canonical_pair_orbits_total'],
        'old_pair_orbits': payload['old_pair_constraints_cover_current_pair_orbits'],
        'not_old': payload['current_pair_orbits_not_in_old_constraints'],
        'edge_count_after_old_pairs': payload['edge_count_after_old_pairs'],
        'target_clique_after_old_pairs': payload['target_clique_after_old_pairs'],
    }, sort_keys=True))


if __name__ == '__main__':
    main()
