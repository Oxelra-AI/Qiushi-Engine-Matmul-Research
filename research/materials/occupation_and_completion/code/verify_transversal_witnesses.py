#!/usr/bin/env python3
"""Independent-ish verification of selected analysis transversality witnesses.

This script deliberately avoids using the analysis subspace routines for the
critical rank, span, intersection, and domain-sum computations.  It enumerates
small F2 spans directly (dimension <= 9) and recomputes saturated contractions
from the tensor arrays.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np

ROOT = Path('research/research_record')
OUT = ROOT / 'workspace/data/core_complete_transversal/transversal_witness_verification.json'
WIT = ROOT / 'workspace/data/core_complete_transversal/transversal_witnesses.json'


def rank_vecs(vecs: Iterable[int], n: int) -> int:
    rows = [int(v) & ((1 << n) - 1) for v in vecs if int(v) & ((1 << n) - 1)]
    rank = 0
    col = 0
    while col < n and rank < len(rows):
        piv = None
        for r in range(rank, len(rows)):
            if (rows[r] >> col) & 1:
                piv = r
                break
        if piv is None:
            col += 1
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for r in range(len(rows)):
            if r != rank and ((rows[r] >> col) & 1):
                rows[r] ^= rows[rank]
        rank += 1
        col += 1
    return rank


def rref_vecs(vecs: Iterable[int], n: int) -> list[int]:
    rows = [int(v) & ((1 << n) - 1) for v in vecs if int(v) & ((1 << n) - 1)]
    out = []
    rank = 0
    for col in range(n):
        piv = None
        for r in range(rank, len(rows)):
            if (rows[r] >> col) & 1:
                piv = r
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for r in range(len(rows)):
            if r != rank and ((rows[r] >> col) & 1):
                rows[r] ^= rows[rank]
        out.append(rows[rank])
        rank += 1
    return out


def span_set(basis: Sequence[int]) -> set[int]:
    vals = {0}
    for b in basis:
        vals |= {x ^ int(b) for x in list(vals)}
    return vals


def intersection_basis(spaces: Sequence[Sequence[int]], n: int) -> list[int]:
    if not spaces:
        return rref_vecs([1 << i for i in range(n)], n)
    cur = None
    for sp in spaces:
        vals = span_set(sp)
        cur = vals if cur is None else (cur & vals)
    return rref_vecs(cur or [], n)


def contraction(T: np.ndarray, q: int) -> np.ndarray:
    M = np.zeros((T.shape[1], T.shape[2]), dtype=np.uint8)
    for a in range(T.shape[0]):
        if (int(q) >> a) & 1:
            M ^= T[a]
    return M


def rank_mat(M: np.ndarray) -> int:
    return rank_vecs([sum(int(M[i, j]) << j for j in range(M.shape[1])) for i in range(M.shape[0])], M.shape[1])


def col_basis(M: np.ndarray) -> list[int]:
    return rref_vecs([sum(int(M[i, j]) << i for i in range(M.shape[0])) for j in range(M.shape[1])], M.shape[0])


def row_basis(M: np.ndarray) -> list[int]:
    return rref_vecs([sum(int(M[i, j]) << j for j in range(M.shape[1])) for i in range(M.shape[0])], M.shape[1])


def compute_domains(T: np.ndarray, A_cols: Sequence[int]):
    nterms = len(A_cols)
    sat_B = [[] for _ in range(nterms)]
    sat_C = [[] for _ in range(nterms)]
    sat_records = []
    for q in range(1, 1 << T.shape[0]):
        I = [s for s, a in enumerate(A_cols) if ((int(q) & int(a)).bit_count() & 1)]
        M = contraction(T, q)
        rk = rank_mat(M)
        if rk > 0 and rk == len(I):
            Bb = col_basis(M)
            Cb = row_basis(M)
            sat_records.append({'q': int(q), 'rank': int(rk), 'terms': I, 'B_basis': Bb, 'C_basis': Cb})
            for s in I:
                sat_B[s].append(Bb)
                sat_C[s].append(Cb)
    B = [intersection_basis(sat_B[s], T.shape[1]) for s in range(nterms)]
    C = [intersection_basis(sat_C[s], T.shape[2]) for s in range(nterms)]
    return sat_records, B, C


def get_target(label: str):
    core_v2 = json.loads((ROOT / 'workspace/data/dual_ruling/core_e11_saturation_v2_long.json').read_text())
    T_core = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    if label.startswith('core_round'):
        rnum = int(label.split('round')[1].split('_')[0])
        rec = next(r for r in core_v2['rounds'] if r.get('round') == rnum)
        return T_core, [int(x) for x in rec['support']]
    if label == 'combined_rep2_all5_round0':
        combined = json.loads((ROOT / 'workspace/data/dual_ruling/combined_sep_all5.json').read_text())
        # Independent prefix-semantics check: the generating script fixes prefix
        # [1,2], selects 18 candidates, and stores support=prefix+selected.
        T = np.zeros((9, 9, 9), dtype=np.uint8)
        for i in range(3):
            for j in range(3):
                for k in range(3):
                    T[3*i+j, 3*j+k, 3*i+k] = 1
        support = [int(x) for x in combined['rounds'][0]['support']]
        return T, support
    raise KeyError(label)


def verify_target(label: str, witnesses: Sequence[dict]) -> dict:
    T, A = get_target(label)
    sat_records, B, C = compute_domains(T, A)
    sat_by_q = {r['q']: r for r in sat_records}
    checks = []
    for w in witnesses:
        q = int(w['q'])
        side = w['side']
        rec = sat_by_q.get(q)
        domains = B if side == 'B' else C
        J = [int(x) for x in w['subset_terms']]
        n = T.shape[1] if side == 'B' else T.shape[2]
        sum_dim = rank_vecs([v for s in J for v in domains[s]], n)
        M = contraction(T, q)
        I = [s for s, a in enumerate(A) if ((q & int(a)).bit_count() & 1)]
        checks.append({
            'q': q,
            'side': side,
            'recomputed_rank': rank_mat(M),
            'recomputed_participating_terms': I,
            'matches_recorded_participating_terms': I == [int(x) for x in w['participating_terms']],
            'is_saturated': rec is not None and rec['rank'] == len(I),
            'subset_terms': J,
            'subset_size': len(J),
            'recomputed_sum_domain_dim': sum_dim,
            'recorded_sum_domain_dim': int(w['sum_domain_dim']),
            'dimension_defect_confirmed': sum_dim < len(J),
            'domain_bases': [[int(v) for v in domains[s]] for s in J],
        })
    return {
        'label': label,
        'term_count': len(A),
        'distinct_A': len(set(A)),
        'saturated_count_recomputed': len(sat_records),
        'checks': checks,
        'all_checked': all(c['matches_recorded_participating_terms'] and c['is_saturated'] and c['dimension_defect_confirmed'] and c['recomputed_sum_domain_dim'] == c['recorded_sum_domain_dim'] for c in checks),
    }


def main():
    data = json.loads(WIT.read_text())
    results = []
    for target in data['targets']:
        checks = verify_target(target['label'], target['focused_witnesses'][:6])
        results.append(checks)
        print(json.dumps({'label': checks['label'], 'checked': len(checks['checks']), 'all_checked': checks['all_checked'], 'saturated': checks['saturated_count_recomputed']}, sort_keys=True))
    combined = json.loads((ROOT / 'workspace/data/dual_ruling/combined_sep_all5.json').read_text())
    prefix = combined.get('prefix')
    support = combined['rounds'][0]['support']
    prefix_semantics = {
        'prefix': prefix,
        'support_len': len(support),
        'prefix_entries_in_support': {str(p): support.count(p) for p in prefix},
        'support_has_no_duplicate_points': len(set(support)) == len(support),
        'support_interpretation': 'analysis script constructs support=sorted(prefix+selected) with target=18 selected candidates, so the stored support is the 20-term A-list tested by analysis, not support plus extra prefix multiplicity.',
    }
    out = {'schema': 'transversal_witness_verification_v1', 'field': 'F2', 'prefix_semantics': prefix_semantics, 'targets': results}
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f'Saved {OUT}')


if __name__ == '__main__':
    main()
