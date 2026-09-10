#!/usr/bin/env python3
"""Choose exact affine charts for uv-pairing incidence computations.

For a rank-23 QMM scheme with uv pairing matrix P (81 x 23), a chart with
lambda_k=1 and rank(P_without_k)=22 can eliminate the other lambda variables
from P lambda = 0 using a 22 x 22 row minor.  This script records such row
sets and nonzero u/v/w pivot coordinates from verified seed schemes.  The data
are intended for exact CAS generation; they do not by themselves prove or find
rank 22.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import List, Sequence


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def parse_qmm(path: Path):
    terms = []
    cur = None
    dims = None
    rank = None
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith('#'):
            continue
        parts = line.split()
        if parts[0] == 'dimensions':
            dims = tuple(map(int, parts[1:4]))
        elif parts[0] == 'rank':
            rank = int(parts[1])
        elif parts[0] == 'term':
            if cur is not None:
                terms.append(cur)
            cur = {'index': int(parts[1])}
        elif parts[0] in ('u','v','w'):
            if cur is None:
                raise ValueError('factor before term')
            cur[parts[0]] = [int(x) for x in parts[1:]]
    if cur is not None:
        terms.append(cur)
    if dims != (3,3,3) or rank != 23 or len(terms) != 23:
        raise ValueError(f'unexpected QMM header/term count in {path}: dims={dims}, rank={rank}, terms={len(terms)}')
    return terms


def pairing_matrix(terms, pair='uv'):
    out = []
    for a in range(81):
        row = []
        ia, ib = divmod(a, 9)
        for t in terms:
            row.append(int(t[pair[0]][ia]) * int(t[pair[1]][ib]))
        out.append(row)
    return out


def rank_rational(rows: Sequence[Sequence[int]]) -> int:
    A = [[Fraction(x) for x in row] for row in rows]
    if not A:
        return 0
    m, n = len(A), len(A[0])
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = A[r][c]
        A[r] = [x / inv for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(n)]
        r += 1
        if r == m:
            break
    return r


def independent_row_indices(mat: Sequence[Sequence[int]], cols: Sequence[int]) -> List[int]:
    basis = []
    chosen = []
    current_rank = 0
    for ri, row in enumerate(mat):
        cand = basis + [[row[c] for c in cols]]
        rk = rank_rational(cand)
        if rk > current_rank:
            basis = cand
            chosen.append(ri)
            current_rank = rk
            if current_rank == len(cols):
                return chosen
    return chosen


def det_bareiss_int(A: Sequence[Sequence[int]]) -> int:
    M = [list(map(int, row)) for row in A]
    n = len(M)
    if n == 0:
        return 1
    sign = 1
    prev = 1
    for k in range(n - 1):
        piv = None
        for i in range(k, n):
            if M[i][k] != 0:
                piv = i
                break
        if piv is None:
            return 0
        if piv != k:
            M[k], M[piv] = M[piv], M[k]
            sign *= -1
        pivot = M[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * pivot - M[i][k] * M[k][j]) // prev
        prev = pivot
        for i in range(k + 1, n):
            M[i][k] = 0
        for j in range(k + 1, n):
            M[k][j] = 0
    return sign * M[n - 1][n - 1]


def first_nonzero(vec):
    for i, x in enumerate(vec):
        if x != 0:
            return i, int(x)
    return None, 0


def summarize_scheme(path: Path, pair='uv'):
    terms = parse_qmm(path)
    P = pairing_matrix(terms, pair=pair)
    full_rank = rank_rational(P)
    pivots = []
    for ti, t in enumerate(terms):
        rec = {'term': ti}
        for f in ['u','v','w']:
            j, val = first_nonzero(t[f])
            rec[f'{f}_pivot_index'] = j
            rec[f'{f}_pivot_seed_value'] = val
        pivots.append(rec)
    charts = []
    for k in range(23):
        cols = [j for j in range(23) if j != k]
        row_idx = independent_row_indices(P, cols)
        rk = len(row_idx)
        det = 0
        if rk == 22:
            minor = [[P[r][c] for c in cols] for r in row_idx]
            det = det_bareiss_int(minor)
        charts.append({
            'lambda_pivot_term': k,
            'columns_solved_terms': cols,
            'row_indices_for_22x22_minor': row_idx,
            'row_indices_as_uv_coordinates': [{'row_index': r, 'u_index': r // 9, 'v_index': r % 9} for r in row_idx],
            'minor_rank': rk,
            'minor_det': int(det),
            'minor_det_abs': abs(int(det)),
            'usable_rank22_open_chart': rk == 22 and det != 0,
        })
    return {
        'scheme_path': str(path),
        'scheme_sha256': sha256_file(path),
        'pair': pair,
        'full_pairing_rank_over_Q': full_rank,
        'factor_pivots_from_seed': pivots,
        'lambda_elimination_charts': charts,
        'usable_chart_count': sum(1 for c in charts if c['usable_rank22_open_chart']),
        'meaning': 'For a chart with lambda_k=1 and the recorded 22x22 minor nonzero, solve the selected uv relation equations for the other lambda variables and impose the remaining 59 relation equations together with Brent equations and chosen factor pivots. A solution shortens exactly to rank at most 22; emptiness excludes only this chart/layer.',
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--outdir', type=Path, default=Path('data/pairing_incidence_charts'))
    ap.add_argument('--pair', default='uv', choices=['uv','uw','vw'])
    ap.add_argument('schemes', nargs='*', type=Path, default=[
        Path('data/cn122_r23_reproduce/scheme.qmm'),
        Path('data/fmm_r23_schemes/serendipitous_8d34.qmm'),
    ])
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    summaries = []
    for scheme in args.schemes:
        s = summarize_scheme(scheme, pair=args.pair)
        summaries.append(s)
        out = args.outdir / (scheme.stem + f'_{args.pair}_incidence_charts.json')
        out.write_text(json.dumps(s, indent=2, sort_keys=True) + '\n')
        print(json.dumps({'scheme': str(scheme), 'pair': args.pair, 'full_rank': s['full_pairing_rank_over_Q'], 'usable_chart_count': s['usable_chart_count'], 'out': str(out)}, indent=2))
    index = {'pair': args.pair, 'scheme_count': len(summaries), 'outputs': [str(args.outdir / (Path(s['scheme_path']).stem + f'_{args.pair}_incidence_charts.json')) for s in summaries]}
    (args.outdir / f'index_{args.pair}.json').write_text(json.dumps(index, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
