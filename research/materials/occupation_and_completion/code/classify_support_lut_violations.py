#!/usr/bin/env python3
"""Classify Wang-LUT occupation violations of saved A-support candidates.

Default mode scans the entire expanded Wang LUT.  This is necessary because a
support can violate a super-subspace whose occupied points span a smaller
subspace with a weaker lower bound.  The optional subset-span mode is only a
fast heuristic and must not be used as a complete LUT check.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_cnf_e11_fixed import E11  # noqa: E402
from wang_capacity_lazy import all_subset_span_keys, in_rowspace, matrix_rank_of_mask, occupancy_of_key, unpack_basis  # noqa: E402


def parse_ints(spec: str) -> list[int]:
    return [int(x) for x in spec.replace(';', ',').split(',') if x.strip()]


def load_support(path: Path) -> dict[int, int]:
    data = json.loads(path.read_text())
    if data.get('support') is not None:
        if isinstance(data['support'], list):
            return {int(p): 1 for p in data['support']}
        if isinstance(data['support'], dict):
            return {int(p): int(c) for p, c in data['support'].items() if int(c)}
    if data.get('support_dict') is not None:
        return {int(p): int(c) for p, c in data['support_dict'].items() if int(c)}
    if data.get('solution') is not None:
        return {int(p): int(c) for p, c in data['solution'].items() if int(c)}
    raise ValueError(f'no support/support_dict/solution in {path}')


def iter_keys_for_mode(lut: dict[int, int], sol: dict[int, int], mode: str) -> tuple[Iterable[int], int | None]:
    if mode == 'full':
        return lut.keys(), len(lut)
    if mode == 'subset-spans':
        keys = all_subset_span_keys(sorted(sol))
        return keys, len(keys)
    raise ValueError(f'unknown mode {mode}')


def classify(sol: dict[int, int], lut: dict[int, int], rank_s: int, contain_points: Sequence[int],
             max_report: int, mode: str) -> dict:
    keys, key_count_hint = iter_keys_for_mode(lut, sol, mode)
    support_items = sorted(sol.items())
    t0 = time.time()
    violations = []
    tight = []
    by_dim = Counter()
    by_dim_lb = Counter()
    by_dim_lb_excess = Counter()
    contain_mask_hist = Counter()
    contain_mask_dim_lb = Counter()
    tight_by_containment = Counter()
    tight_by_dim_lb = Counter()
    worst_by_containment: dict[str, dict] = {}
    worst_by_dim: dict[int, dict] = {}
    occupancy_hist = Counter()
    checked = 0
    missing = 0
    for key in keys:
        lb = lut.get(key)
        if lb is None:
            missing += 1
            continue
        basis = unpack_basis(key)
        occ = 0
        for p, mult in support_items:
            if in_rowspace(int(p), basis, n=9):
                occ += int(mult)
        cap = rank_s - int(lb)
        d = int(key) & 0xF
        contained = tuple(int(p) for p in contain_points if in_rowspace(int(p), basis, n=9))
        contain_label = ','.join(map(str, contained)) if contained else 'none'
        margin = cap - occ
        occupancy_hist[occ] += 1
        if margin == 0:
            tight_by_containment[contain_label] += 1
            tight_by_dim_lb[(d, int(lb))] += 1
            if len(tight) < max_report:
                tight.append({'key': int(key), 'dim': d, 'lb': int(lb), 'cap': int(cap), 'occupancy': int(occ), 'contained': list(contained), 'basis': list(basis)})
        rec_base = {
            'key': int(key),
            'dim': d,
            'lb': int(lb),
            'cap': int(cap),
            'occupancy': int(occ),
            'excess': int(occ - cap),
            'contained': list(contained),
            'basis': list(basis),
        }
        oldd = worst_by_dim.get(d)
        if oldd is None or (rec_base['excess'], rec_base['lb'], rec_base['occupancy']) > (oldd['excess'], oldd['lb'], oldd['occupancy']):
            worst_by_dim[d] = rec_base
        if occ > cap:
            violations.append(rec_base)
            by_dim[d] += 1
            by_dim_lb[(d, int(lb))] += 1
            by_dim_lb_excess[(d, int(lb), int(occ - cap))] += 1
            contain_mask_hist[contain_label] += 1
            contain_mask_dim_lb[(contain_label, d, int(lb))] += 1
            old = worst_by_containment.get(contain_label)
            if old is None or (rec_base['excess'], rec_base['lb'], rec_base['occupancy'], -rec_base['dim']) > (old['excess'], old['lb'], old['occupancy'], -old['dim']):
                worst_by_containment[contain_label] = rec_base
        checked += 1
    violations.sort(key=lambda v: (v['excess'], v['lb'], v['occupancy'], -v['dim']), reverse=True)
    return {
        'mode': mode,
        'mode_meaning': 'full expanded LUT scan' if mode == 'full' else 'subset-span heuristic; not a complete LUT check',
        'support_size': len(sol),
        'total_multiplicity': sum(sol.values()),
        'support_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p, m in sol.items() for _ in range(m)).items())),
        'support': {str(k): v for k, v in sorted(sol.items())},
        'rank_s': rank_s,
        'contain_points': list(contain_points),
        'key_count_hint': key_count_hint,
        'checked_keys': checked,
        'missing_keys': missing,
        'violation_count': len(violations),
        'max_excess': max((v['excess'] for v in violations), default=0),
        'violations_by_dim': dict(sorted(by_dim.items())),
        'violations_by_dim_lb': {f'{d},{lb}': c for (d, lb), c in sorted(by_dim_lb.items())},
        'violations_by_dim_lb_excess': {f'{d},{lb},{e}': c for (d, lb, e), c in sorted(by_dim_lb_excess.items())},
        'violations_by_containment': dict(sorted(contain_mask_hist.items())),
        'violations_by_containment_dim_lb': {f'{lab}|{d},{lb}': c for (lab, d, lb), c in sorted(contain_mask_dim_lb.items())},
        'tight_by_containment': dict(sorted(tight_by_containment.items())),
        'tight_by_dim_lb': {f'{d},{lb}': c for (d, lb), c in sorted(tight_by_dim_lb.items())},
        'occupancy_hist': dict(sorted(occupancy_hist.items())),
        'worst_by_containment': dict(sorted(worst_by_containment.items())),
        'worst_by_dim': {str(k): v for k, v in sorted(worst_by_dim.items())},
        'violations_head': violations[:max_report],
        'tight_head': tight[:max_report],
        'elapsed_sec': time.time() - t0,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--support-json', type=Path, required=True)
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--contain-points', default=str(E11))
    ap.add_argument('--max-report', type=int, default=100)
    ap.add_argument('--mode', choices=['full', 'subset-spans'], default='full')
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    with args.lut.open('rb') as f:
        payload = pickle.load(f)
    lut = payload['lut']
    meta = payload.get('meta', {})
    sol = load_support(args.support_json)
    out = classify(sol, lut, args.rank, parse_ints(args.contain_points), args.max_report, args.mode)
    out['source_support_json'] = str(args.support_json)
    out['lut_meta_brief'] = {'coverage_ok': meta.get('coverage_ok'), 'conflict_count': meta.get('conflict_count'), 'subspace_count': meta.get('subspace_count')}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    brief = {k: out[k] for k in ['mode', 'source_support_json', 'checked_keys', 'violation_count', 'max_excess', 'violations_by_containment', 'violations_by_dim_lb', 'elapsed_sec']}
    print(json.dumps(brief, indent=2, sort_keys=True))
    print('saved', args.out)


if __name__ == '__main__':
    main()
