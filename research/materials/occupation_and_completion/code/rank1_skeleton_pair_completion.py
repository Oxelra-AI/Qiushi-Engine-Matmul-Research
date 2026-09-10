#!/usr/bin/env python3
"""Test exact-18 rank-1 skeletons for two higher-rank Wang completions.

Given an exact rank-1 skeleton S (usually |S|=18 and E11 in S), this script
scans the complete T-level Wang occupation LUT for rank_s=20 and derives the
exact constraints on adding two non-rank-1 A-points h1,h2:

  occ_S(Phi) + 1_{h1 in Phi} + 1_{h2 in Phi} <= 20 - L(Phi).

Rows with slack 0 forbid every higher-rank point in Phi; rows with slack 1
forbid pairs lying together in Phi.  After one complete scan, remaining allowed
pairs are exactly the higher-rank completions of S allowed by the full Wang
occupation table.  Such a completion is still only an A-support necessary
condition, not a tensor decomposition.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Set, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_cnf_e11_fixed import E11, stab_e11_orbits  # noqa: E402
from wang_capacity_lazy import matrix_rank_of_mask, unpack_basis, subspace_points_from_basis  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def load_skeletons(path: Path, use_canonical: bool = True) -> List[List[int]]:
    data = json.loads(path.read_text())
    out: List[List[int]] = []
    if isinstance(data, list):
        if all(isinstance(x, int) for x in data):
            return [sorted(int(x) for x in data)]
        for item in data:
            if isinstance(item, list):
                out.append(sorted(int(x) for x in item))
            elif isinstance(item, dict):
                key = 'canonical' if use_canonical and 'canonical' in item else 'support'
                if key in item:
                    out.append(sorted(int(x) for x in item[key]))
    elif isinstance(data, dict):
        if 'support' in data and data['support'] is not None:
            supp = data['support']
            if isinstance(supp, list):
                out.append(sorted(int(x) for x in supp))
            elif isinstance(supp, dict):
                out.append(sorted(int(k) for k, v in supp.items() if int(v)))
        if 'enumeration' in data:
            for w in data.get('enumeration', {}).get('witnesses', []):
                key = 'canonical' if use_canonical and 'canonical' in w else 'support'
                if key in w:
                    out.append(sorted(int(x) for x in w[key]))
        if 'witnesses' in data:
            for w in data['witnesses']:
                key = 'canonical' if use_canonical and 'canonical' in w else 'support'
                if key in w:
                    out.append(sorted(int(x) for x in w[key]))
    # unique, preserve order
    seen = set(); uniq=[]
    for s in out:
        t = tuple(s)
        if t not in seen:
            seen.add(t); uniq.append(s)
    return uniq


def bit_positions(mask: int):
    y = mask
    while y:
        lb = y & -y
        yield lb.bit_length() - 1
        y ^= lb


def high_mask_for_points(points: Iterable[int], high_index: Dict[int, int]) -> int:
    m = 0
    for p in points:
        i = high_index.get(int(p))
        if i is not None:
            m |= 1 << i
    return m


def count_pairs_from_conflicts(allowed_mask: int, conflicts: Sequence[int]) -> Tuple[int, List[Tuple[int, int]]]:
    count = 0; examples: List[Tuple[int,int]] = []
    y = allowed_mask
    while y:
        lb = y & -y; i = lb.bit_length() - 1; y ^= lb
        later = y & ~conflicts[i]
        c = later.bit_count(); count += c
        if len(examples) < 20:
            z = later
            while z and len(examples) < 20:
                lb2 = z & -z; j = lb2.bit_length() - 1; z ^= lb2
                examples.append((i, j))
    return count, examples


def branch_rep_for_support(support: Sequence[int]) -> int | None:
    support_set = set(int(p) for p in support)
    support_set.discard(E11)
    for orb in stab_e11_orbits():
        if any(int(p) in support_set for p in orb['members']):
            return int(orb['rep'])
    return None


def check_skeleton(lut: Dict[int, int], skeleton: Sequence[int], rank_s: int, max_pair_examples: int = 20):
    t0 = time.time()
    skel = set(int(p) for p in skeleton)
    high_pts = [p for p in range(1, 512) if matrix_rank_of_mask(p) > 1 and p not in skel]
    high_index = {p: i for i, p in enumerate(high_pts)}
    all_mask = (1 << len(high_pts)) - 1
    forbidden = 0
    conflicts = [0] * len(high_pts)
    rows_by_dim = Counter(); rows_by_lb = Counter(); slack_hist = Counter(); slack_dim_hist = Counter()
    slack0_rows = 0; slack1_rows = 0; invalid_rows = 0; highmask_size_hist = Counter(); max_occ_excess = 0
    invalid_head = []; slack0_head = []; slack1_head = []
    for idx, (key, lb0) in enumerate(lut.items(), 1):
        basis = unpack_basis(key)
        pts_in = subspace_points_from_basis(basis)
        occ = sum(1 for p in skel if p in pts_in)
        cap = rank_s - int(lb0)
        slack = cap - occ
        d = key & 0xF
        rows_by_dim[d] += 1; rows_by_lb[int(lb0)] += 1; slack_hist[slack] += 1; slack_dim_hist[(d, slack)] += 1
        if slack < 0:
            invalid_rows += 1; max_occ_excess = max(max_occ_excess, -slack)
            if len(invalid_head) < 20:
                invalid_head.append({'key': int(key), 'dim': d, 'lb': int(lb0), 'cap': cap, 'occupancy': occ, 'excess': -slack, 'basis': list(basis)})
            # If the skeleton itself violates, completion is impossible, but keep
            # scanning to report how badly.
            continue
        if slack <= 1:
            hmask = high_mask_for_points(pts_in, high_index)
            highmask_size_hist[hmask.bit_count()] += 1
            if slack == 0:
                slack0_rows += 1; forbidden |= hmask
                if hmask and len(slack0_head) < 20:
                    slack0_head.append({'key': int(key), 'dim': d, 'lb': int(lb0), 'cap': cap, 'occupancy': occ, 'high_count': hmask.bit_count(), 'basis': list(basis)})
            else:
                slack1_rows += 1
                # Add a clique conflict on hmask.
                y = hmask
                while y:
                    bit = y & -y; i = bit.bit_length() - 1; y ^= bit
                    conflicts[i] |= hmask ^ bit
                if hmask.bit_count() >= 2 and len(slack1_head) < 20:
                    slack1_head.append({'key': int(key), 'dim': d, 'lb': int(lb0), 'cap': cap, 'occupancy': occ, 'high_count': hmask.bit_count(), 'basis': list(basis)})
        if idx % 1_000_000 == 0:
            print(f'scanned {idx:,}/{len(lut):,}; invalid={invalid_rows:,}; forbidden={forbidden.bit_count():,}; elapsed={time.time()-t0:.1f}s', flush=True)
    allowed = all_mask & ~forbidden
    pair_count, pair_examples_idx = (0, []) if invalid_rows else count_pairs_from_conflicts(allowed, conflicts)
    pair_examples = []
    for i, j in pair_examples_idx[:max_pair_examples]:
        pair = [high_pts[i], high_pts[j]]
        supp = sorted(list(skel) + pair)
        pair_examples.append({'pair': pair, 'pair_ranks': [matrix_rank_of_mask(pair[0]), matrix_rank_of_mask(pair[1])], 'support': supp, 'branch_rep': branch_rep_for_support(supp), 'support_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in supp).items()))})
    # Count conflict edges among allowed points for interpretability.
    conflict_edges_allowed = 0
    y = allowed
    while y:
        lb = y & -y; i = lb.bit_length() - 1; y ^= lb
        conflict_edges_allowed += (y & conflicts[i]).bit_count()
    return {
        'skeleton': sorted(skel),
        'skeleton_size': len(skel),
        'skeleton_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in skel).items())),
        'rank_s': rank_s,
        'high_point_count': len(high_pts),
        'rows_by_dim': dict(sorted(rows_by_dim.items())),
        'rows_by_lb': dict(sorted(rows_by_lb.items())),
        'slack_hist': {str(k): v for k, v in sorted(slack_hist.items())},
        'slack_by_dim': {f'{d},{s}': v for (d, s), v in sorted(slack_dim_hist.items()) if s <= 2},
        'slack0_rows': slack0_rows,
        'slack1_rows': slack1_rows,
        'slack01_highmask_size_hist': dict(sorted(highmask_size_hist.items())),
        'invalid_rows': invalid_rows,
        'max_occ_excess': max_occ_excess,
        'invalid_head': invalid_head,
        'slack0_head': slack0_head,
        'slack1_head': slack1_head,
        'forbidden_high_count': forbidden.bit_count(),
        'allowed_high_count': allowed.bit_count(),
        'conflict_edges_among_allowed': conflict_edges_allowed,
        'allowed_pair_completion_count': pair_count,
        'allowed_pair_examples': pair_examples,
        'elapsed_sec': time.time() - t0,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('skeleton_json', type=Path)
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--use-support-not-canonical', action='store_true')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--max-pair-examples', type=int, default=20)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    lut, meta = load_lut(args.lut)
    skeletons = load_skeletons(args.skeleton_json, use_canonical=not args.use_support_not_canonical)
    if args.limit:
        skeletons = skeletons[:args.limit]
    print(f'loaded LUT {len(lut):,}; skeletons={len(skeletons)} from {args.skeleton_json}')
    results = []
    t0 = time.time()
    for i, sk in enumerate(skeletons, 1):
        print(f'checking skeleton {i}/{len(skeletons)} size={len(sk)} head={sk[:5]}...', flush=True)
        results.append(check_skeleton(lut, sk, args.rank, args.max_pair_examples))
    summary = {
        'problem': 'two higher-rank completions for rank-1 Wang skeletons',
        'source_skeleton_json': str(args.skeleton_json),
        'field': 'F2',
        'rank_s': args.rank,
        'skeleton_count': len(skeletons),
        'completed_skeleton_count': sum(1 for r in results if r['allowed_pair_completion_count'] > 0),
        'total_allowed_pair_completions': sum(int(r['allowed_pair_completion_count']) for r in results),
        'max_allowed_pair_completions_for_one_skeleton': max((int(r['allowed_pair_completion_count']) for r in results), default=0),
        'invalid_skeleton_count': sum(1 for r in results if r['invalid_rows'] > 0),
        'branch_rep_hist_for_examples': dict(sorted(Counter(ex['branch_rep'] for r in results for ex in r['allowed_pair_examples']).items())),
        'lut_meta_brief': {'coverage_ok': meta.get('coverage_ok'), 'conflict_count': meta.get('conflict_count'), 'subspace_count': meta.get('subspace_count')},
        'elapsed_sec': time.time() - t0,
        'meaning': 'A positive allowed_pair_completion is a full-Wang-admissible A-support candidate of size 20 with exact two higher-rank points; it still requires fixed-A B/C solving to test tensor decomposition.',
    }
    payload = {'summary': summary, 'results': results}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps(summary, indent=2, sort_keys=True))
    print('saved', args.out)


if __name__ == '__main__':
    main()
