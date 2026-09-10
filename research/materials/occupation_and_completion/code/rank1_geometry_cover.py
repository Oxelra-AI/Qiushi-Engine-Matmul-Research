#!/usr/bin/env python3
"""Verify the rank-1 Segre-grid covering used in analysis.

Over F2 every nonzero rank-1 3x3 matrix is uniquely u v^T with
u,v in F2^3\{0}.  For a rank-20 Wang A-support, if the selected rank-1
points contain two points sharing u or sharing v, the full matrix-multiplication
A-side symmetry (left/right GL plus transpose) sends that unordered pair to
{E11,E12}.  Thus the whole support lies in the fixed-E11 rep2 branch after
choosing this adjacent pair as anchor.  If no such pair exists, the selected
rank-1 points form a matching in the 7x7 Segre grid and have size at most 7.

This script checks the finite combinatorics and the implemented action/orbit
facts used by the proof structure.  It is not a rank lower-bound proof by
itself; it certifies the branch-covering reduction used by later computations.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_cnf_e11_fixed import E11, stab_e11_orbits  # noqa: E402
from wang_capacity_lazy import make_actions, matrix_rank_of_mask, transform_mask  # noqa: E402

E12 = 2


def outer_mask(u: int, v: int) -> int:
    """Rows of u v^T, with vectors encoded by bits 0,1,2."""
    mask = 0
    for i in range(3):
        if (u >> i) & 1:
            mask |= int(v) << (3 * i)
    return mask


def rank1_uv_map() -> dict[int, tuple[int, int]]:
    out: dict[int, tuple[int, int]] = {}
    collisions = []
    for u in range(1, 8):
        for v in range(1, 8):
            m = outer_mask(u, v)
            if m in out:
                collisions.append((m, out[m], (u, v)))
            out[m] = (u, v)
    rank1 = [p for p in range(1, 512) if matrix_rank_of_mask(p) == 1]
    missing = sorted(set(rank1) - set(out))
    extra = sorted(set(out) - set(rank1))
    if collisions or missing or extra or len(out) != 49:
        raise RuntimeError({'collisions': collisions[:5], 'missing': missing[:10], 'extra': extra[:10], 'count': len(out)})
    return out


def adjacent_pair(pair: Sequence[int], uv: dict[int, tuple[int, int]]) -> bool:
    a, b = pair
    ua, va = uv[int(a)]
    ub, vb = uv[int(b)]
    return ua == ub or va == vb


def matching_ok(points: Iterable[int], uv: dict[int, tuple[int, int]]) -> bool:
    us = set(); vs = set()
    for p in points:
        u, v = uv[int(p)]
        if u in us or v in vs:
            return False
        us.add(u); vs.add(v)
    return True


def pair_orbit(seed: Sequence[int], actions) -> set[tuple[int, int]]:
    a, b = map(int, seed)
    return {tuple(sorted((transform_mask(a, g), transform_mask(b, g)))) for g in actions}


def greedy_max_matching_size(rank1: list[int], uv: dict[int, tuple[int, int]]) -> tuple[int, list[int]]:
    """Exact backtracking maximum for selected rank1 universe; tiny (49 pts)."""
    pts = sorted(rank1)
    best: list[int] = []

    def rec(i: int, chosen: list[int], used_u: set[int], used_v: set[int]) -> None:
        nonlocal best
        if len(chosen) + (len(pts) - i) <= len(best):
            return
        if i == len(pts):
            if len(chosen) > len(best):
                best = chosen.copy()
            return
        p = pts[i]
        u, v = uv[p]
        if u not in used_u and v not in used_v:
            used_u.add(u); used_v.add(v); chosen.append(p)
            rec(i + 1, chosen, used_u, used_v)
            chosen.pop(); used_v.remove(v); used_u.remove(u)
        rec(i + 1, chosen, used_u, used_v)

    rec(0, [], set(), set())
    return len(best), best


def main() -> None:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    t0 = time.time()

    uv = rank1_uv_map()
    rank1 = sorted(uv)
    actions = make_actions()

    all_pairs = [tuple(sorted((a, b))) for i, a in enumerate(rank1) for b in rank1[i+1:]]
    adjacent = {p for p in all_pairs if adjacent_pair(p, uv)}
    nonadjacent = set(all_pairs) - adjacent
    orbit_adj = pair_orbit([E11, E12], actions)
    orbit_nonadj_seed = pair_orbit([E11, outer_mask(2, 2)], actions)  # E11, E22 in this encoding

    e11_orbits = stab_e11_orbits()
    rank1_orbits = [o for o in e11_orbits if o['rank_hist'] == {1: o['size']} or o['rank_hist'] == {'1': o['size']}]
    # JSON-created files may stringify hist keys; imported runtime has int keys.
    e11_orbit_reps = [int(o['rep']) for o in e11_orbits]
    rep2_record = next((o for o in e11_orbits if int(o['rep']) == E12), None)

    by_u = Counter(u for u, v in uv.values())
    by_v = Counter(v for u, v in uv.values())
    max_match_size, max_match_example = greedy_max_matching_size(rank1, uv)

    # Direct random-free exhaustive check of the dichotomy for all small subsets up to size 8:
    # if size >= 8 it cannot be a matching, hence has an adjacent pair.  For all 8-subsets,
    # checking C(49,8) is too large; the exact max matching computation above is the certificate.
    matching_example_uv = [(p, uv[p]) for p in max_match_example]

    payload = {
        'problem': 'rank-1 Segre-grid adjacent-pair vs matching cover over F2',
        'field': 'F2',
        'rank1_point_count': len(rank1),
        'rank1_points_head': rank1[:20],
        'uv_unique': True,
        'E11': E11,
        'E12': E12,
        'E11_uv': uv[E11],
        'E12_uv': uv[E12],
        'rank1_points_per_left_vector': dict(sorted(by_u.items())),
        'rank1_points_per_right_vector': dict(sorted(by_v.items())),
        'all_rank1_pair_count': len(all_pairs),
        'adjacent_pair_count_by_uv': len(adjacent),
        'nonadjacent_pair_count_by_uv': len(nonadjacent),
        'orbit_of_E11_E12_pair_size': len(orbit_adj),
        'orbit_of_E11_E12_equals_all_adjacent_pairs': orbit_adj == adjacent,
        'adjacent_missing_from_orbit_head': sorted(adjacent - orbit_adj)[:20],
        'adjacent_orbit_extra_head': sorted(orbit_adj - adjacent)[:20],
        'orbit_of_E11_E22_pair_size': len(orbit_nonadj_seed),
        'orbit_of_E11_E22_equals_all_nonadjacent_pairs': orbit_nonadj_seed == nonadjacent,
        'nonadjacent_missing_from_orbit_head': sorted(nonadjacent - orbit_nonadj_seed)[:20],
        'nonadjacent_orbit_extra_head': sorted(orbit_nonadj_seed - nonadjacent)[:20],
        'stab_E11_orbit_reps_in_order': e11_orbit_reps,
        'rep2_is_first_stab_E11_orbit': bool(e11_orbit_reps and e11_orbit_reps[0] == E12),
        'rep2_record': rep2_record,
        'rank1_stab_E11_orbits': [o for o in e11_orbits if 1 in o['rank_hist']],
        'max_nonadjacent_rank1_subset_size': max_match_size,
        'max_matching_example_points': max_match_example,
        'max_matching_example_uv': matching_example_uv,
        'matching_example_ok': matching_ok(max_match_example, uv),
        'cover_statement_checked': (
            len(rank1) == 49 and len(adjacent) == 294 and len(nonadjacent) == 882 and
            orbit_adj == adjacent and orbit_nonadj_seed == nonadjacent and
            e11_orbit_reps and e11_orbit_reps[0] == E12 and max_match_size == 7
        ),
        'mathematical_use': (
            'Any rank-20 A-support with at least two adjacent rank-1 points can be normalized to the fixed E11+E12 (rep2) branch. '
            'If it has no adjacent rank-1 pair, its rank-1 points form a matching in the 7x7 rank-1 grid, so k<=7 after fixing one rank-1 point to E11 and imposing row/column matching constraints.'
        ),
        'proof_status': 'finite combinatorial and implemented-group orbit check; lower-bound use still requires Wang-support infeasibility certificates in the resulting cases',
        'elapsed_sec': time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True, default=str) + '\n')
    print(json.dumps({
        'cover_statement_checked': payload['cover_statement_checked'],
        'rank1_point_count': len(rank1),
        'adjacent_pair_count': len(adjacent),
        'adjacent_orbit_size': len(orbit_adj),
        'nonadjacent_pair_count': len(nonadjacent),
        'nonadjacent_orbit_size': len(orbit_nonadj_seed),
        'rep2_first': payload['rep2_is_first_stab_E11_orbit'],
        'max_matching_size': max_match_size,
        'out': str(args.out),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
