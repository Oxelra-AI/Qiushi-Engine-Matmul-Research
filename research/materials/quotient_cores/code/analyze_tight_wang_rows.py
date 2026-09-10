#!/usr/bin/env python3
"""Inspect tight/violated Wang rows from current fixed-E11 supports.

The output ranks violated subspaces by how promising they are for raising Wang's
A-restriction table: high occupancy excess, small current lower bound gap,
small restricted tensor dimensions, and recurrence across rep2/rep16/k-slices.
For each selected row it materializes the restricted tensor's cheap invariants
and, optionally, checks the known rank-23 scheme A-supports against a table in
which that single row is raised by one.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Sequence

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_support_capacity import extract_solution  # noqa: E402
from restricted_tensor_rank_probe import apply_a_constraints, build_matmul_tensor_f2, flattening_ranks  # noqa: E402
from scan_rank23_restrictions import discover_qmm_records, scan_record, convert_terms_to_session  # noqa: E402
from wang_capacity_lazy import (  # noqa: E402
    in_rowspace,
    matrix_rank_of_mask,
    subspace_points_from_basis,
    unpack_basis,
)


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def support_from_check_or_solution(path: Path) -> Dict[int, int]:
    data = json.loads(path.read_text())
    if 'support' in data and isinstance(data['support'], dict):
        return {int(k): int(v) for k, v in data['support'].items() if int(v)}
    return extract_solution(path)


def point_label(mask: int) -> str:
    rows = []
    for i in range(3):
        rows.append(''.join('1' if (mask >> (3 * i + j)) & 1 else '0' for j in range(3)))
    return '/'.join(rows)


def row_occupancy(basis: Sequence[int], support: Dict[int, int]) -> tuple[int, List[int]]:
    pts = []
    occ = 0
    for p, m in support.items():
        if in_rowspace(p, basis, n=9):
            occ += m
            pts.append(p)
    return occ, sorted(pts)


def analyze_sources(lut, sources: List[Path], max_report_per_source: int):
    rows: Dict[int, dict] = {}
    source_summaries = []
    for source in sources:
        support = support_from_check_or_solution(source)
        name = source.stem
        rank_hist = Counter(matrix_rank_of_mask(p) for p, m in support.items() for _ in range(m))
        vcount = 0
        worst = 0
        by_dim_lb = Counter()
        for key, lb in lut.items():
            basis = unpack_basis(key)
            occ, pts = row_occupancy(basis, support)
            cap = 20 - int(lb)
            excess = occ - cap
            if excess <= 0:
                continue
            vcount += 1
            worst = max(worst, excess)
            by_dim_lb[(key & 0xF, int(lb))] += 1
            entry = rows.setdefault(key, {
                'key': key,
                'basis': list(basis),
                'dim': key & 0xF,
                'lb': int(lb),
                'cap': cap,
                'source_hits': [],
                'max_excess': 0,
                'max_occupancy': 0,
                'total_excess': 0,
            })
            entry['source_hits'].append({'source': str(source), 'name': name, 'occupancy': occ, 'excess': excess, 'points_in_support': pts})
            entry['max_excess'] = max(entry['max_excess'], excess)
            entry['max_occupancy'] = max(entry['max_occupancy'], occ)
            entry['total_excess'] += excess
        source_summaries.append({
            'source': str(source),
            'support_size': len(support),
            'total_multiplicity': sum(support.values()),
            'rank_hist': dict(sorted(rank_hist.items())),
            'violation_count': vcount,
            'max_excess': worst,
            'violations_by_dim_lb': {f'{d},{lb}': c for (d, lb), c in sorted(by_dim_lb.items())},
        })
    return rows, source_summaries


def known_rank23_slack_for_raise(key: int) -> dict:
    """Check local qmm rank-23 schemes only; this is a regression screen."""
    basis = unpack_basis(key)
    records = []
    for rec in discover_qmm_records():
        sc = scan_record(rec)
        if not sc.get('valid'):
            continue
        terms = convert_terms_to_session(rec.terms, sc['input_convention'])
        counts = Counter(a for a, b, c in terms)
        occ = sum(m for p, m in counts.items() if in_rowspace(p, basis, n=9))
        records.append({'scheme': rec.name, 'source': rec.source, 'A_occupancy': occ, 'rank23_cap_if_lb_plus1': 23 - (sc.get('lb_plus1', 0))})
    return {'qmm_scheme_count': len(records), 'records': records}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--sources', nargs='+', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--top', type=int, default=20)
    args = ap.parse_args()
    t0 = time.time()
    lut, meta = load_lut(args.lut)
    rows, source_summaries = analyze_sources(lut, args.sources, args.top)
    T = build_matmul_tensor_f2()
    ranked = sorted(rows.values(), key=lambda e: (e['max_excess'], len(e['source_hits']), e['total_excess'], e['lb'], -e['dim'], e['key']), reverse=True)
    top_rows = []
    for e in ranked[:args.top]:
        core, keep, pivots = apply_a_constraints(T, e['basis'])
        nonzero_a_slices = int(sum(1 for i in range(core.shape[0]) if core[i].any()))
        slice_rank_hist = Counter()
        for i in range(core.shape[0]):
            slice_rank_hist[int(np.linalg.matrix_rank(core[i].astype(np.float64) % 2))] += 1  # only descriptive; exact flattening below is F2
        r1_points_in_phi = [p for p in subspace_points_from_basis(e['basis']) if matrix_rank_of_mask(p) == 1]
        # Check local rank-23 A-support safety of raising by one: for a true rank-23 scheme, occ <= 23-(lb+1)
        rank23_checks = []
        cap23_raised = 23 - (e['lb'] + 1)
        for rec in discover_qmm_records():
            sc = scan_record(rec)
            if not sc.get('valid'):
                continue
            terms = convert_terms_to_session(rec.terms, sc['input_convention'])
            counts = Counter(a for a, b, c in terms)
            occ = sum(m for p, m in counts.items() if in_rowspace(p, e['basis'], n=9))
            rank23_checks.append({'scheme': rec.name, 'A_occupancy': occ, 'passes_raised_bound': occ <= cap23_raised, 'cap23_if_raised': cap23_raised})
        top_rows.append({
            **e,
            'raise_by_one_would_cap_rank20': 20 - (e['lb'] + 1),
            'restricted_tensor_shape': list(core.shape),
            'restricted_tensor_nnz': int(core.sum()),
            'flattening_ranks': flattening_ranks(core),
            'nonzero_A_slices_after_restriction': nonzero_a_slices,
            'rank1_points_in_phi_count': len(r1_points_in_phi),
            'rank1_points_in_phi_head': r1_points_in_phi[:20],
            'rank23_A_support_raise_screen': rank23_checks,
            'basis_matrix_labels': [point_label(x) for x in e['basis']],
        })
    payload = {
        'problem': 'tight Wang rows from fixed-E11 rep2/rep16 midrange supports',
        'field': 'F2',
        'lut_meta_brief': {'coverage_ok': meta.get('coverage_ok'), 'conflict_count': meta.get('conflict_count'), 'subspace_count': meta.get('subspace_count')},
        'sources': [str(p) for p in args.sources],
        'source_summaries': source_summaries,
        'distinct_violated_rows': len(rows),
        'top_rows': top_rows,
        'elapsed_sec': time.time() - t0,
        'meaning': 'Rows with max_excess>=1 in these supports are exactly places where raising the row lower bound by one would cut the displayed support. A rank proof for the restricted tensor at current lb+1 is still required before changing the table.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'distinct_violated_rows': len(rows),
        'source_summaries': source_summaries,
        'top_keys': [{'key': r['key'], 'dim': r['dim'], 'lb': r['lb'], 'max_excess': r['max_excess'], 'hits': len(r['source_hits']), 'basis': r['basis'], 'flattening': r['flattening_ranks'], 'nnz': r['restricted_tensor_nnz'], 'rank1_in_phi': r['rank1_points_in_phi_count']} for r in top_rows[:10]],
        'out': str(args.out),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
