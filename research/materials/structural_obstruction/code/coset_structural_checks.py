#!/usr/bin/env python3
"""analysis structural checks for the high-rank A-factor coset reduction.

This is proof support, not a replacement for the written argument.  It checks
finite facts used by the short proof:

* Under the recorded dim-2 raise picture (allowed orbits 481--483), a pair of
  distinct high-rank 3x3 matrices is compatible iff their sum has rank one.
* For nonzero rank-one 3x3 matrices over F2, a pair has rank-one sum iff the
  two matrices share their left vector or share their right vector.  Every
  pairwise-compatible triple shares one side globally; hence every larger
  compatible family shares one side.
* In AG(3,2), every 5-subset contains an affine plane; for a lower-block rank-2
  column coset, the four rank-3 points form one affine plane.

The mathematical proof should cite these as independently checked finite facts
and then give the short linear-algebra argument in text.
"""
from __future__ import annotations

import json
import pickle
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

CACHE_PATH = Path('data/wang_f2_lb20/wang_orbit_closed_cache.pkl')
CASCADE_PATH = Path('data/wang_analysis/cascade/dim3_raises_to_dim2.json')
OUT = Path('data/structural/coset_structural_checks.json')

NBITS = 9


def gf2_rank_rows(rows: Sequence[int]) -> int:
    basis: List[int] = []
    for x0 in rows:
        x = int(x0)
        for b in basis:
            p = b.bit_length() - 1
            if (x >> p) & 1:
                x ^= b
        if x == 0:
            continue
        p = x.bit_length() - 1
        for i, b in enumerate(basis):
            if (b >> p) & 1:
                basis[i] = b ^ x
        basis.append(x)
        basis.sort(key=lambda z: z.bit_length(), reverse=True)
    return len(basis)


def mat_rows(x: int) -> List[int]:
    return [sum(((int(x) >> (3*i+j)) & 1) << j for j in range(3)) for i in range(3)]


def rank3(x: int) -> int:
    return gf2_rank_rows(mat_rows(x))


def outer_mask(u: int, v: int) -> int:
    z = 0
    for i in range(3):
        if (u >> i) & 1:
            for j in range(3):
                if (v >> j) & 1:
                    z |= 1 << (3*i+j)
    return z


def rank_one_uv() -> dict[int, Tuple[int,int]]:
    d: dict[int, Tuple[int,int]] = {}
    for u in range(1,8):
        for v in range(1,8):
            d[outer_mask(u,v)] = (u,v)
    assert len(d) == 49
    return d


def rref_basis(rows: Iterable[int]) -> Tuple[int,...]:
    basis: List[int] = []
    for x0 in rows:
        x = int(x0)
        if x == 0:
            continue
        for b in basis:
            p = b.bit_length() - 1
            if (x >> p) & 1:
                x ^= b
        if x == 0:
            continue
        p = x.bit_length() - 1
        for i,b in enumerate(basis):
            if (b >> p) & 1:
                basis[i] = b ^ x
        basis.append(x)
        basis.sort(key=lambda z: z.bit_length(), reverse=True)
    return tuple(basis)


def pack_basis(basis: Sequence[int]) -> int:
    x = 0
    for i,b in enumerate(basis):
        x |= int(b) << (NBITS*i)
    return (x << 4) | len(basis)


def pair_orbit(a: int, b: int, cache) -> int:
    key = pack_basis(rref_basis([a,b]))
    return int(cache['key_to_orbit'][key])


def affine_planes_ag3() -> List[Tuple[int,...]]:
    planes = set()
    for base in range(8):
        for u,v in combinations(range(1,8),2):
            plane = tuple(sorted({base, base^u, base^v, base^u^v}))
            if len(plane) == 4:
                planes.add(plane)
    return sorted(planes)


def affine_plane_count(subset: Sequence[int]) -> int:
    S = set(subset)
    return sum(1 for P in affine_planes_ag3() if set(P).issubset(S))


def main():
    with CACHE_PATH.open('rb') as f:
        cache = pickle.load(f)
    cascade = json.loads(CASCADE_PATH.read_text())
    current_lbs = {int(o['position']): int(o.get('raw_lb',0)) for o in cache['orbits']}
    for k,v in cascade.get('all_raises_after_tests',{}).items():
        current_lbs[int(k)] = max(current_lbs.get(int(k),0), int(v))

    high = [a for a in range(1,512) if rank3(a) >= 2]
    allowed_orbits = {481,482,483}
    pair_records = Counter()
    bad_allowed = []
    bad_allowed_sum_not_rankone = []
    rankone_sum_but_excluded = []
    orbit_rankpattern = defaultdict(Counter)
    for a,b in combinations(high,2):
        pos = pair_orbit(a,b,cache)
        allowed_by_lb = current_lbs.get(pos,0) < 19
        rankone_sum = (rank3(a ^ b) == 1)
        pair_records[(pos, rank3(a), rank3(b), rank3(a^b), allowed_by_lb)] += 1
        orbit_rankpattern[pos][tuple(sorted([rank3(a), rank3(b), rank3(a^b)]))] += 1
        if allowed_by_lb and pos not in allowed_orbits:
            bad_allowed.append([a,b,pos,rank3(a^b)])
        if allowed_by_lb and not rankone_sum:
            bad_allowed_sum_not_rankone.append([a,b,pos,current_lbs.get(pos,0),rank3(a^b)])
        if rankone_sum and not allowed_by_lb:
            rankone_sum_but_excluded.append([a,b,pos,current_lbs.get(pos,0),rank3(a^b)])

    uv = rank_one_uv(); r1 = sorted(uv)
    pair_lemma_bad = []
    rankone_pair_hist = Counter()
    for x,y in combinations(r1,2):
        ux,vx = uv[x]; uy,vy = uv[y]
        same_left = ux == uy
        same_right = vx == vy
        srank = rank3(x ^ y)
        rankone_pair_hist[(same_left, same_right, srank)] += 1
        if (srank == 1) != (same_left or same_right):
            pair_lemma_bad.append([x,y,uv[x],uv[y],srank])
    triple_bad = []
    compatible_triples = 0
    for tri in combinations(r1,3):
        if all(rank3(x^y)==1 for x,y in combinations(tri,2)):
            compatible_triples += 1
            lefts = {uv[x][0] for x in tri}
            rights = {uv[x][1] for x in tri}
            if not (len(lefts)==1 or len(rights)==1):
                triple_bad.append([[x,uv[x]] for x in tri])

    plane_count_by_size = {str(k): Counter() for k in range(9)}
    for k in range(9):
        for S in combinations(range(8),k):
            plane_count_by_size[str(k)][affine_plane_count(S)] += 1

    # Canonical column coset p + e0 tensor F2^3 with lower-block rank 2.
    p = (1 << 4) | (1 << 8)  # rows 2 and 3 have independent standard rows; first row variable.
    coset = [p | r for r in range(8)]
    ranks = {r: rank3(p | r) for r in range(8)}
    rank3_firstrows = sorted(r for r,v in ranks.items() if v == 3)
    rank2_firstrows = sorted(r for r,v in ranks.items() if v == 2)
    coset_plane = affine_plane_count(rank3_firstrows)

    out = {
        'schema': 's0908_coset_structural_checks_v1',
        'meaning': 'Finite proof-support checks for the high-rank rank-one-difference/coset reduction. CP-SAT/orbit raise certification is a separate premise.',
        'sources': {'cache': str(CACHE_PATH), 'cascade': str(CASCADE_PATH)},
        'high_rank_vertex_count': len(high),
        'current_allowed_dim2_orbits': sorted([pos for pos in range(478,492) if current_lbs.get(pos,0) < 19]),
        'allowed_orbits_used': sorted(allowed_orbits),
        'high_rank_pair_summary': {
            'total_pairs': sum(pair_records.values()),
            'bad_allowed_not_481_483_count': len(bad_allowed),
            'bad_allowed_not_481_483_head': bad_allowed[:20],
            'bad_allowed_sum_not_rankone_count': len(bad_allowed_sum_not_rankone),
            'bad_allowed_sum_not_rankone_head': bad_allowed_sum_not_rankone[:20],
            'rankone_sum_but_excluded_count': len(rankone_sum_but_excluded),
            'rankone_sum_but_excluded_head': rankone_sum_but_excluded[:20],
            'orbit_rankpattern': {str(pos): {str(list(k)): int(v) for k,v in sorted(cnt.items())} for pos,cnt in sorted(orbit_rankpattern.items())},
        },
        'rankone_sum_lemma_check': {
            'rankone_point_count': len(r1),
            'pair_hist_by_same_left_same_right_sumrank': {str(k): int(v) for k,v in sorted(rankone_pair_hist.items(), key=lambda kv: str(kv[0]))},
            'bad_pair_count': len(pair_lemma_bad),
            'bad_pair_head': pair_lemma_bad[:20],
            'compatible_triple_count': compatible_triples,
            'compatible_triples_without_global_side_count': len(triple_bad),
            'bad_triple_head': triple_bad[:20],
        },
        'ag32_plane_check': {
            'plane_count': len(affine_planes_ag3()),
            'plane_count_by_subset_size': {k: {str(a): int(b) for a,b in sorted(v.items())} for k,v in plane_count_by_size.items()},
            'every_5_subset_contains_plane': list(plane_count_by_size['5'].keys()) == [1],
        },
        'canonical_rank2_lowerblock_coset_check': {
            'p': p,
            'coset_by_firstrow': {str(r): p|r for r in range(8)},
            'rank_by_firstrow': {str(r): int(v) for r,v in ranks.items()},
            'rank2_firstrows': rank2_firstrows,
            'rank3_firstrows': rank3_firstrows,
            'rank3_firstrows_affine_plane_count': coset_plane,
            'rank3_points_form_affine_plane': coset_plane == 1,
        },
        'conditional_interpretation': {
            'if_dim2_raises_479_484_491_are_certified': 'then every pair of distinct high-rank A-factors in a length-20 candidate has an allowed dim-2 orbit, hence differs by rank one; the converse is false because orbit 479 also has rank-one sums but is excluded. The one-way implication is enough for coset containment.',
            'with_dim3_coset_LB17_and_AG32_fact': 'at most four high-rank factors; split-flattening excess then forces exactly four with profile one rank2 and three rank3 in a lower-block rank2 coset',
        }
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'status': 'ok',
        'out': str(OUT),
        'bad_allowed_sum_not_rankone_count': len(bad_allowed_sum_not_rankone),
        'rankone_sum_but_excluded_count': len(rankone_sum_but_excluded),
        'bad_rankone_pair_count': len(pair_lemma_bad),
        'bad_compatible_triple_count': len(triple_bad),
        'every_5_subset_contains_plane': out['ag32_plane_check']['every_5_subset_contains_plane'],
        'rank3_points_form_affine_plane': out['canonical_rank2_lowerblock_coset_check']['rank3_points_form_affine_plane'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
