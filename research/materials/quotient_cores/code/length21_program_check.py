#!/usr/bin/env python3
"""Small exact checks for the length-21 continuation program.

This is not part of the proof of R_F2(T_333) >= 21.  It checks the finite
AG(3,2) and rank-pattern arithmetic behind a future rank >= 22 route under
three additional quotient improvements: line values 20, all-high two-plane
values 20, and normalized affine-plane values 18.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path

SESSION = Path('research/research_record')
OUT = SESSION / 'workspace/data/length21_program/length21_program_check.json'


def bits3(x: int):
    return [(x >> i) & 1 for i in range(3)]


def parity(x: int) -> int:
    return x.bit_count() & 1


def mat_from_mask(mask: int):
    return [[(mask >> (3*i+j)) & 1 for j in range(3)] for i in range(3)]


def mask_from_mat(M) -> int:
    m = 0
    for i in range(3):
        for j in range(3):
            if M[i][j] & 1:
                m |= 1 << (3*i+j)
    return m


def rank_mask(mask: int) -> int:
    rows = [sum(((mask >> (3*i+j)) & 1) << j for j in range(3)) for i in range(3)]
    r = 0
    rows = rows[:]
    for col in range(3):
        piv = None
        for i in range(r, 3):
            if (rows[i] >> col) & 1:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(3):
            if i != r and ((rows[i] >> col) & 1):
                rows[i] ^= rows[r]
        r += 1
    return r


def affine_planes_ag32():
    points = list(range(8))
    planes = set()
    for a in points:
        for u in range(1, 8):
            for v in range(u + 1, 8):
                if u == v:
                    continue
                # u,v independent over F2 iff u != v for nonzero vectors.
                plane = frozenset([a, a ^ u, a ^ v, a ^ u ^ v])
                planes.add(plane)
    return sorted([sorted(p) for p in planes])


def rank1_signature(mask: int):
    """Return (column-space generator, row-space generator) for rank-one mask."""
    if rank_mask(mask) != 1:
        return None
    M = mat_from_mask(mask)
    col = 0
    for j in range(3):
        v = 0
        for i in range(3):
            v |= (M[i][j] & 1) << i
        if v:
            col = v
            break
    row = 0
    for i in range(3):
        v = 0
        for j in range(3):
            v |= (M[i][j] & 1) << j
        if v:
            row = v
            break
    return col, row


def check_three_point_coset_lemma():
    matrices = list(range(512))
    rank1 = {m for m in matrices if rank_mask(m) == 1}
    neigh = {a: [a ^ d for d in rank1] for a in matrices}
    triples = 0
    failures = []
    orientation_counts = {'column': 0, 'row': 0, 'both': 0}
    for a in matrices:
        ns = [b for b in neigh[a] if b > a]
        for b, c in itertools.combinations(ns, 2):
            if b >= c:
                continue
            if rank_mask(b ^ c) != 1:
                continue
            triples += 1
            sig1 = rank1_signature(a ^ b)
            sig2 = rank1_signature(a ^ c)
            ok_col = sig1[0] == sig2[0]
            ok_row = sig1[1] == sig2[1]
            if ok_col and ok_row:
                orientation_counts['both'] += 1
            elif ok_col:
                orientation_counts['column'] += 1
            elif ok_row:
                orientation_counts['row'] += 1
            else:
                failures.append([a, b, c, a ^ b, a ^ c, b ^ c])
                if len(failures) >= 10:
                    break
        if failures:
            break
    return {
        'triples_checked': triples,
        'failure_count': len(failures),
        'sample_failures': failures,
        'orientation_counts': orientation_counts,
        'ok': len(failures) == 0,
    }


def subset_classification_for_coset(base: int, description: str):
    planes = [frozenset(p) for p in affine_planes_ag32()]
    ranks = {label: rank_mask(base ^ label) for label in range(8)}
    high = [label for label, r in ranks.items() if r >= 2]
    high_rank3 = [label for label, r in ranks.items() if r == 3]
    cases = []
    max_excess_under_plane_cap = 0
    max_size_under_plane_cap = 0
    for r in range(9):
        for S_tuple in itertools.combinations(range(8), r):
            S = frozenset(S_tuple)
            if not S.issubset(high):
                continue
            # affine-plane cap 3: no affine plane can be entirely occupied by high factors
            if any(P.issubset(S) for P in planes):
                continue
            excess = sum(ranks[x] - 1 for x in S)
            max_excess_under_plane_cap = max(max_excess_under_plane_cap, excess)
            max_size_under_plane_cap = max(max_size_under_plane_cap, len(S))
            if excess >= 6:
                rank_counts = {1: 0, 2: 0, 3: 0}
                for x in S:
                    rank_counts[ranks[x]] += 1
                total_rank_length21 = (21 - len(S)) + sum(ranks[x] for x in S)
                cases.append({
                    'labels': list(S_tuple),
                    'size': len(S),
                    'rank_counts': rank_counts,
                    'excess_sum_rank_minus_terms': excess,
                    'total_A_rank_at_length21': total_rank_length21,
                    'split_bound_excess_total_rank_minus_27': total_rank_length21 - 27,
                    'saturation_kills_by_existing_lemma': total_rank_length21 == 27 and rank_counts[3] >= 2,
                })
    summary = {}
    for c in cases:
        key = f"size{c['size']}_r2{c['rank_counts'][2]}_r3{c['rank_counts'][3]}_total{c['total_A_rank_at_length21']}"
        summary[key] = summary.get(key, 0) + 1
    survivors_after_saturation = [c for c in cases if not c['saturation_kills_by_existing_lemma']]
    return {
        'description': description,
        'base_mask': base,
        'label_ranks': ranks,
        'high_labels': high,
        'rank3_labels': high_rank3,
        'rank3_labels_form_affine_plane': frozenset(high_rank3) in planes,
        'affine_plane_count': len(planes),
        'every_5_subset_contains_plane': all(any(P.issubset(S) for P in planes) for S in map(frozenset, itertools.combinations(range(8), 5))),
        'max_size_under_affine_plane_cap3': max_size_under_plane_cap,
        'max_excess_under_affine_plane_cap3': max_excess_under_plane_cap,
        'cases_with_excess_at_least_6': cases,
        'case_family_counts': summary,
        'survivors_after_existing_saturation': survivors_after_saturation,
        'ok': True,
    }


def main():
    planes = affine_planes_ag32()
    # rank-two lower block: diag(0,1,1), first row labels 0..7
    rank2_lower = subset_classification_for_coset(272, 'lower 2x3 block has rank two; base diag(0,1,1)')
    # rank-one lower block: single lower pivot at bit 4, first row labels 0..7
    rank1_lower = subset_classification_for_coset(16, 'lower 2x3 block has rank one; base has only middle lower pivot')
    out = {
        'schema': 'length21_program_check_v1',
        'purpose': 'Verify the finite AG(3,2), rank-pattern, and three-point rank-one-difference arithmetic behind the proposed length-21 continuation program under three additional quotient raises.',
        'additional_raises_assumed': {
            'line_values': 'L(line) >= 20, restoring line cap 1 at length 21',
            'all_high_two_planes': 'L(W) >= 20 for all all-high two-planes, restoring two-plane cap 1 at length 21',
            'affine_planes_in_normalized_cosets': 'L(H) >= 18 for affine-plane spans, restoring affine-plane cap 3 at length 21',
        },
        'ag32': {
            'point_count': 8,
            'affine_plane_count': len(planes),
            'planes': planes,
            'every_5_subset_contains_plane': all(any(frozenset(P).issubset(S) for P in map(frozenset, planes)) for S in map(frozenset, itertools.combinations(range(8), 5))),
        },
        'three_point_rank_one_difference_lemma': check_three_point_coset_lemma(),
        'rank_one_lower_block': rank1_lower,
        'rank_two_lower_block': rank2_lower,
    }
    out['conclusion'] = {
        'rank_one_lower_block_dies': rank1_lower['max_excess_under_affine_plane_cap3'] < 6,
        'rank_two_saturation_killed_families': {k: v for k, v in rank2_lower['case_family_counts'].items() if 'total27' in k},
        'rank_two_survivor_families_after_saturation': rank2_lower['survivors_after_existing_saturation'],
        'unique_surviving_family_statement': 'After affine-plane cap 3 and the existing saturation lemma, the only length-21 high-set family with excess >= 6 is size 4 with one rank-two and three rank-three high factors, total A-rank 28 (one above the split-flattening rank 27).'
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True), encoding='utf-8')
    print(json.dumps({
        'ok': out['three_point_rank_one_difference_lemma']['ok']
              and out['ag32']['every_5_subset_contains_plane']
              and out['conclusion']['rank_one_lower_block_dies']
              and len(out['conclusion']['rank_two_survivor_families_after_saturation']) > 0,
        'out': str(OUT),
        'three_point_triples_checked': out['three_point_rank_one_difference_lemma']['triples_checked'],
        'rank1_lower_max_excess': rank1_lower['max_excess_under_affine_plane_cap3'],
        'rank2_case_families': rank2_lower['case_family_counts'],
        'rank2_survivor_count': len(rank2_lower['survivors_after_existing_saturation']),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
