#!/usr/bin/env python3
"""Slice-rank necessary invariants for E11 quotient-lift cosets.

For fixed V, fixed quotient CPD, and residual budget s, compute for every
nonzero phi in V^* the minimum matrix rank in the coset
  R_phi + span{M_j}
where M_j=b_j c_j are the fixed quotient B-C matrices.  If a residual CPD with
A-factors in V has at most s terms, then there exist nonnegative counts n_v for
v in V minus {0} such that sum n_v <= s and sum_{phi(v)=1} n_v >= m_phi.
This script checks that integer necessary condition exactly for small s.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

SCRIPTS = Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import e11_quotient_lift_general_sat as glift  # noqa: E402


def gf2_rank_rows(rows: list[int]) -> int:
    basis: dict[int, int] = {}
    for r in rows:
        x = int(r)
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                break
    return len(basis)


def rows_from_matrix(M: np.ndarray) -> list[int]:
    rows = []
    for b in range(9):
        val = 0
        for c in range(9):
            if int(M[b, c]) & 1:
                val |= 1 << c
        rows.append(val)
    return rows


def min_rank_coset(target_rows: list[int], term_rows: list[list[int]]) -> dict:
    n = len(term_rows)
    current = list(target_rows)
    best = gf2_rank_rows(current)
    best_code = 0
    hist = Counter({best: 1})
    for step in range(1, 1 << n):
        j = (step & -step).bit_length() - 1
        tr = term_rows[j]
        for b in range(9):
            current[b] ^= tr[b]
        r = gf2_rank_rows(current)
        hist[r] += 1
        if r < best:
            best = r
            best_code = step ^ (step >> 1)
            if best == 0:
                # cannot improve further, but continue only if histogram requested; skip for speed
                pass
    return {'min_rank': int(best), 'arg_subset_gray_code': int(best_code), 'rank_histogram': dict(sorted((int(k), int(v)) for k, v in hist.items()))}


def cover_feasible(m_by_phi: dict[int, int], s: int) -> dict:
    phis = list(range(1, 16))
    vectors = list(range(1, 16))
    # enumerate counts n_v by multisets of up to s vectors (small: C(15+s,s)).
    best_def = 10**9
    best_counts = None
    total_checked = 0
    for k in range(s + 1):
        for tup in itertools.combinations_with_replacement(vectors, k):
            total_checked += 1
            cnt = Counter(tup)
            max_def = 0
            sum_def = 0
            ok = True
            for phi in phis:
                cov = sum(n for v, n in cnt.items() if ((phi & v).bit_count() & 1))
                d = max(0, int(m_by_phi[phi]) - cov)
                if d:
                    ok = False
                    sum_def += d
                    max_def = max(max_def, d)
            score = (sum_def, max_def, k)
            if sum_def < best_def:
                best_def = sum_def
                best_counts = dict(sorted((int(v), int(n)) for v, n in cnt.items()))
            if ok:
                return {'cover_feasible': True, 'terms_used': k, 'counts': dict(sorted((int(v), int(n)) for v, n in cnt.items())), 'checked': total_checked}
    return {'cover_feasible': False, 'checked': total_checked, 'best_total_deficiency': int(best_def), 'best_counts': best_counts}


def analyze_scheme(core: np.ndarray, prefix: list[int], scheme: np.ndarray, s: int, hist: bool = False) -> dict:
    meta, Rcoords, lifts, b_masks, c_masks, M_rows = glift.scheme_to_residual(core, prefix, scheme)
    rec = {**meta}
    if meta['quotient_diff'] or meta['residual_reconstruction_diff'] or any(meta['annihilator_residual_nnz']):
        rec['bad_input'] = True
        return rec
    term_rows = M_rows
    min_records = {}
    m_by_phi = {}
    for phi in range(1, 16):
        target = [0] * 9
        for k in range(4):
            if (phi >> k) & 1:
                rows = rows_from_matrix(Rcoords[k])
                for b in range(9):
                    target[b] ^= rows[b]
        mr = min_rank_coset(target, term_rows)
        if not hist:
            mr.pop('rank_histogram', None)
        min_records[phi] = mr
        m_by_phi[phi] = mr['min_rank']
    sum_m = sum(m_by_phi.values())
    cover = cover_feasible(m_by_phi, s)
    rec.update({
        'residual_rank_budget': int(s),
        'm_by_phi': {int(k): int(v) for k, v in m_by_phi.items()},
        'sum_m_phi': int(sum_m),
        'eight_s_bound': int(8 * s),
        'sum_bound_violated': bool(sum_m > 8 * s),
        'cover_condition': cover,
        'min_rank_records': min_records,
    })
    return rec


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--pool', type=Path, required=True)
    ap.add_argument('--prefix', required=True)
    ap.add_argument('--rank-res', type=int, required=True)
    ap.add_argument('--scheme-idx', type=int, default=-1)
    ap.add_argument('--max-schemes', type=int, default=0)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--hist', action='store_true')
    args = ap.parse_args()
    t0 = time.time()
    prefix = [int(x) for x in args.prefix.split(',') if x.strip()]
    core = glift.build_e11_core()
    pool = np.load(args.pool)
    indices = [args.scheme_idx] if args.scheme_idx >= 0 else list(range(pool.shape[0]))
    if args.max_schemes:
        indices = indices[:args.max_schemes]
    records = []
    for idx in indices:
        rec = analyze_scheme(core, prefix, pool[idx], args.rank_res, hist=args.hist)
        rec['scheme_idx'] = int(idx)
        records.append(rec)
        print(f"scheme {idx}: sum_m={rec.get('sum_m_phi')} eight_s={rec.get('eight_s_bound')} cover={rec.get('cover_condition',{}).get('cover_feasible')}")
    dist_sum = Counter(r.get('sum_m_phi') for r in records)
    dist_cover = Counter(str(r.get('cover_condition', {}).get('cover_feasible')) for r in records)
    result = {
        'purpose': 'exact contraction-coset matrix-rank necessary conditions for quotient lift',
        'field': 'F2',
        'prefix': prefix,
        'pool': str(args.pool),
        'residual_rank_budget': int(args.rank_res),
        'schemes_analyzed': len(records),
        'sum_m_distribution': dict(sorted((str(k), int(v)) for k, v in dist_sum.items())),
        'cover_feasible_distribution': dict(sorted((str(k), int(v)) for k, v in dist_cover.items())),
        'meaning': 'If sum_m_phi > 8s or the cover condition is infeasible, no rank<=s residual lift can exist for this fixed quotient scheme. Feasible cover is only necessary, not sufficient.',
        'elapsed_sec': time.time() - t0,
        'records': records,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True, default=int) + '\n')
    print(json.dumps({k: result[k] for k in ['schemes_analyzed','sum_m_distribution','cover_feasible_distribution','elapsed_sec']}, indent=2, sort_keys=True))
    print('wrote', args.out)


if __name__ == '__main__':
    main()
