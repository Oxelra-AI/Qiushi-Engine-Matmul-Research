#!/usr/bin/env python3
"""Extract short certificates for zero saturated-domain intersections.

For a fixed A-support already analyzed by fixed_A_saturation.py, a term
with B_s={0} or C_s={0} is impossible in a nonzero rank-one decomposition.  This
script recomputes the saturated contractions containing that term and finds a
small subset of saturated contractions whose column-space or row-space
intersection is zero.
"""
from __future__ import annotations

import argparse
import json
import sys
from itertools import combinations
from pathlib import Path
from typing import Sequence

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (  # noqa: E402
    build_matmul_tensor_f2,
    col_space_basis,
    contraction_matrix,
    intersection_basis,
    mat_rank_f2,
    row_space_basis,
)


def tensor_for_kind(kind: str) -> np.ndarray:
    if kind == 'full_T333':
        return build_matmul_tensor_f2()
    paths = {
        'E11_core': 'data/restricted_cores/mask_001_E11_core.npy',
        'E12_E21_core': 'data/restricted_cores/mask_010_E12_E21_core.npy',
        'E13_E22_E31_core': 'data/restricted_cores/mask_084_E13_E22_E31_core.npy',
    }
    return np.load(paths[kind]).astype(np.uint8) % 2


def saturated_records_by_term(T, A_cols):
    na = T.shape[0]
    out = [[] for _ in A_cols]
    for q in range(1, 1 << na):
        I = [s for s, a in enumerate(A_cols) if ((q & int(a)).bit_count() & 1)]
        M = contraction_matrix(T, q)
        rk = mat_rank_f2(M)
        if rk == len(I) and rk > 0:
            rec = {
                'q': q,
                'q_hex': hex(q),
                'rank': rk,
                'count': len(I),
                'terms': I,
                'B_basis': list(col_space_basis(M)),
                'C_basis': list(row_space_basis(M)),
            }
            for s in I:
                out[s].append(rec)
    return out


def find_zero_subset(records: Sequence[dict], side: str, n: int):
    key = f'{side}_basis'
    spaces = [tuple(int(x) for x in r[key]) for r in records]
    for size in range(1, min(5, len(records)) + 1):
        for idxs in combinations(range(len(records)), size):
            inter = intersection_basis([spaces[i] for i in idxs], n)
            if len(inter) == 0:
                return {
                    'side': side,
                    'subset_size': size,
                    'records': [records[i] for i in idxs],
                }
    # Fallback greedy certificate if no subset of size <=5 found.
    return {
        'side': side,
        'subset_size': None,
        'records': records[:20],
        'note': 'No zero-intersection subset of size <=5 found; full record head returned.',
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--summary', default='data/fixed_A_saturation/summary.json')
    ap.add_argument('--label', action='append', required=True)
    ap.add_argument('--out', default='data/fixed_A_saturation/zero_domain_certificates.json')
    args = ap.parse_args()
    summary = json.load(open(args.summary))
    by_label = {r['target']['label']: r for r in summary['targets']}
    results = []
    for label in args.label:
        rec = by_label[label]
        target = rec['target']
        analysis = rec['analysis']
        T = tensor_for_kind(target['tensor_kind'])
        A_cols = [int(x) for x in target['A_cols']]
        sat_by_term = saturated_records_by_term(T, A_cols)
        term_certs = []
        for t in analysis['term_summaries']:
            s = int(t['term'])
            if t['B_dim'] == 0 or t['C_dim'] == 0:
                side = 'B' if t['B_dim'] == 0 else 'C'
                cert = find_zero_subset(sat_by_term[s], side, T.shape[1] if side == 'B' else T.shape[2])
                term_certs.append({
                    'term': s,
                    'a': int(t['a']),
                    'a_hex': t['a_hex'],
                    'B_dim': int(t['B_dim']),
                    'C_dim': int(t['C_dim']),
                    'saturated_contractions': int(t['saturated_contractions']),
                    'certificate': cert,
                })
        results.append({
            'label': label,
            'tensor_kind': target['tensor_kind'],
            'term_count': len(A_cols),
            'zero_domain_term_count': len(term_certs),
            'term_certificates': term_certs,
        })
        print(json.dumps({'label': label, 'zero_domain_term_count': len(term_certs), 'terms': [c['term'] for c in term_certs]}, sort_keys=True))
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({'schema': 'zero_domain_certificates_v1', 'results': results}, indent=2, sort_keys=True) + '\n')
    print(f'Saved {out}')


if __name__ == '__main__':
    main()
