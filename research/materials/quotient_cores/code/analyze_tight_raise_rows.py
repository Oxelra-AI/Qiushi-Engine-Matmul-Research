#!/usr/bin/env python3
"""Find Wang rows that are tight on current near-supports and would cut them if raised.

For a rank-20 occupation candidate P, a Wang row Phi with lower bound L is
currently tight when |P∩Phi| = 20-L.  Proving R(T|Phi=0) >= L+1 would change the
cap to 20-(L+1) and exclude P.  This script scans supports and ranks such rows
by recurrence, rank-1 richness, and small restricted-tensor size.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_support_capacity import extract_solution  # noqa: E402
from restricted_tensor_rank_probe import apply_a_constraints, build_matmul_tensor_f2, flattening_ranks  # noqa: E402
from wang_capacity_lazy import in_rowspace, matrix_rank_of_mask, subspace_points_from_basis, unpack_basis  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def support_from_path(path: Path) -> Dict[int, int]:
    data = json.loads(path.read_text())
    if 'support' in data and isinstance(data['support'], dict):
        return {int(k): int(v) for k, v in data['support'].items() if int(v)}
    return extract_solution(path)


def point_label(mask: int) -> str:
    return '/'.join(''.join('1' if (mask >> (3 * i + j)) & 1 else '0' for j in range(3)) for i in range(3))


def row_occupancy(basis: Sequence[int], support: Dict[int, int]) -> tuple[int, List[int]]:
    pts = []
    occ = 0
    for p, m in support.items():
        if in_rowspace(p, basis, n=9):
            occ += m
            pts.append(p)
    return occ, sorted(pts)


def parse_int_set(s: str | None) -> set[int] | None:
    if not s:
        return None
    out = set()
    for part in s.split(','):
        part = part.strip()
        if not part:
            continue
        if '-' in part:
            a, b = [int(x) for x in part.split('-', 1)]
            out.update(range(a, b + 1))
        else:
            out.add(int(part))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--sources', nargs='+', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--top', type=int, default=50)
    ap.add_argument('--dims', default='1-8')
    ap.add_argument('--lbs', default=None)
    ap.add_argument('--min-occupancy', type=int, default=2)
    ap.add_argument('--max-cap', type=int, default=8)
    args = ap.parse_args()

    dims = parse_int_set(args.dims)
    lbs = parse_int_set(args.lbs)
    lut, meta = load_lut(args.lut)
    supports = [(str(p), support_from_path(p)) for p in args.sources]
    summaries = []
    rows: Dict[int, dict] = {}
    t0 = time.time()
    for source, support in supports:
        rh = Counter(matrix_rank_of_mask(p) for p, m in support.items() for _ in range(m))
        tight_count = 0
        tight_by_dim_lb = Counter()
        violated = 0
        for key, lb0 in lut.items():
            dim = key & 0xF
            lb = int(lb0)
            if dims is not None and dim not in dims:
                continue
            if lbs is not None and lb not in lbs:
                continue
            cap = 20 - lb
            if cap < args.min_occupancy or cap > args.max_cap:
                continue
            basis = unpack_basis(key)
            occ, pts = row_occupancy(basis, support)
            if occ > cap:
                violated += 1
                continue
            if occ != cap:
                continue
            tight_count += 1
            tight_by_dim_lb[(dim, lb)] += 1
            e = rows.setdefault(key, {'key': key, 'basis': list(basis), 'dim': dim, 'lb': lb, 'cap': cap, 'hits': [], 'hit_count': 0, 'total_occupancy': 0})
            e['hits'].append({'source': source, 'occupancy': occ, 'points_in_support': pts})
            e['hit_count'] += 1
            e['total_occupancy'] += occ
        summaries.append({'source': source, 'support_rank_hist': dict(sorted(rh.items())), 'tight_count': tight_count, 'violated_ignored_count': violated, 'tight_by_dim_lb': {f'{d},{lb}': c for (d, lb), c in sorted(tight_by_dim_lb.items())}})

    T = build_matmul_tensor_f2()
    ranked = sorted(rows.values(), key=lambda e: (e['hit_count'], e['cap'], e['lb'], -e['dim'], e['total_occupancy'], -e['key']), reverse=True)
    top = []
    for e in ranked[:args.top]:
        basis = e['basis']
        core, keep, pivots = apply_a_constraints(T, basis)
        r1_phi = [p for p in subspace_points_from_basis(basis) if matrix_rank_of_mask(p) == 1]
        top.append({
            **e,
            'raise_to_lb': e['lb'] + 1,
            'new_rank20_cap_if_raised': 20 - (e['lb'] + 1),
            'restricted_tensor_shape': list(core.shape),
            'restricted_tensor_nnz': int(core.sum()),
            'flattening_ranks': flattening_ranks(core),
            'rank1_points_in_phi_count': len(r1_phi),
            'rank1_points_in_phi': r1_phi,
            'basis_matrix_labels': [point_label(x) for x in basis],
            'A_keep_indices': keep,
            'A_pivot_indices': pivots,
        })

    payload = {
        'problem': 'tight Wang rows that would cut current supports if raised by one',
        'field': 'F2',
        'rank_s': 20,
        'lut_meta_brief': {'coverage_ok': meta.get('coverage_ok'), 'conflict_count': meta.get('conflict_count'), 'subspace_count': meta.get('subspace_count')},
        'filters': {'dims': sorted(dims) if dims is not None else None, 'lbs': sorted(lbs) if lbs is not None else None, 'min_occupancy': args.min_occupancy, 'max_cap': args.max_cap},
        'sources': [str(p) for p in args.sources],
        'source_summaries': summaries,
        'distinct_tight_rows': len(rows),
        'top_rows': top,
        'elapsed_sec': time.time() - t0,
        'meaning': 'For each row, a verified rank lower bound lb+1 for the displayed restricted tensor would cut every listed support hit. These are candidate rows for table strengthening, not strengthened results.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'distinct_tight_rows': len(rows),
        'source_summaries': summaries,
        'top': [{'key': r['key'], 'dim': r['dim'], 'lb': r['lb'], 'cap': r['cap'], 'hits': r['hit_count'], 'basis': r['basis'], 'shape': r['restricted_tensor_shape'], 'flat': r['flattening_ranks'], 'r1_phi': r['rank1_points_in_phi_count']} for r in top[:20]],
        'out': str(args.out),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
