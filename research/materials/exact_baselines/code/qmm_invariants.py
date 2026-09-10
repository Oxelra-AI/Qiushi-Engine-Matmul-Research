#!/usr/bin/env python3
"""Exact invariants for QMM_SCHEME_V1 matrix multiplication schemes.

Computes per-term 3x3 factor ranks, two-factor pairing ranks, full factor span
ranks, and the Jacobian rank/nullity of the map
  (u_i,v_i,w_i)_{i=1..r} -> sum_i u_i \otimes v_i \otimes w_i
at the scheme, over Q and over small prime fields.

The parameter Jacobian has columns
  e_a \otimes v_i \otimes w_i,
  u_i \otimes e_b \otimes w_i,
  u_i \otimes v_i \otimes e_c
for each term i and coordinate a,b,c.
"""
from __future__ import annotations
import argparse, json
from fractions import Fraction
from collections import Counter, defaultdict
from pathlib import Path


def parse_qmm(path: Path):
    dims = None; rank = None; domain = None
    terms = []
    cur = None
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith('#'):
            continue
        parts = line.split()
        if parts[0] == 'dimensions':
            dims = tuple(map(int, parts[1:4]))
        elif parts[0] == 'rank':
            rank = int(parts[1])
        elif parts[0] == 'domain':
            domain = parts[1]
        elif parts[0] == 'term':
            if cur is not None:
                terms.append(cur)
            cur = {'index': int(parts[1])}
        elif parts[0] in ('u','v','w'):
            assert cur is not None
            cur[parts[0]] = [int(x) for x in parts[1:]]
    if cur is not None:
        terms.append(cur)
    assert dims is not None and rank is not None
    assert len(terms) == rank
    for t in terms:
        assert all(k in t for k in ['u','v','w'])
        assert len(t['u']) == dims[0]*dims[1]
        assert len(t['v']) == dims[1]*dims[2]
        assert len(t['w']) == dims[0]*dims[2]
    return {'dimensions': dims, 'rank': rank, 'domain': domain, 'terms': terms}


def rank_mod(mat, p: int) -> int:
    A = [[x % p for x in row] for row in mat]
    if not A:
        return 0
    m, n = len(A), len(A[0])
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i][c] % p:
                piv = i; break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c] % p, -1, p)
        A[r] = [(v * inv) % p for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] % p:
                f = A[i][c] % p
                A[i] = [(A[i][j] - f * A[r][j]) % p for j in range(n)]
        r += 1
        if r == m:
            break
    return r


def rank_q(mat) -> int:
    A = [[Fraction(x) for x in row] for row in mat]
    if not A:
        return 0
    m, n = len(A), len(A[0])
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i][c] != 0:
                piv = i; break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = A[r][c]
        A[r] = [v / inv for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(n)]
        r += 1
        if r == m:
            break
    return r


def mat_rank_vec(vec, p=None):
    M = [vec[0:3], vec[3:6], vec[6:9]]
    return rank_mod(M, p) if p else rank_q(M)


def outer2(x,y):
    return [a*b for a in x for b in y]


def jacobian_columns(terms):
    # 729 rows, 27*r columns; return as list of rows to rank.
    cols = []
    n = 9
    basis = [[1 if i==j else 0 for i in range(n)] for j in range(n)]
    for t in terms:
        u,v,w = t['u'], t['v'], t['w']
        for e in basis:
            cols.append([e[a]*v[b]*w[c] for a in range(n) for b in range(n) for c in range(n)])
        for e in basis:
            cols.append([u[a]*e[b]*w[c] for a in range(n) for b in range(n) for c in range(n)])
        for e in basis:
            cols.append([u[a]*v[b]*e[c] for a in range(n) for b in range(n) for c in range(n)])
    # rank function expects rows; transpose columns to rows.
    return [list(row) for row in zip(*cols)]


def analyze(path: Path, primes=(2,3,5)):
    S = parse_qmm(path)
    terms = S['terms']
    out = {'scheme': str(path), 'dimensions': S['dimensions'], 'rank': S['rank'], 'domain': S['domain']}
    for label,p in [('Q',None)] + [(f'F{q}',q) for q in primes]:
        term_ranks = []
        ordered = []
        sorted_types = []
        for t in terms:
            ru,rv,rw = (mat_rank_vec(t[k], p) for k in ['u','v','w'])
            ordered.append((ru,rv,rw))
            sorted_types.append(tuple(sorted((ru,rv,rw))))
            term_ranks.append({'term': t['index'], 'u': ru, 'v': rv, 'w': rw, 'sorted': tuple(sorted((ru,rv,rw)))})
        pair_mats = {}
        for name, pair in [('uv',('u','v')), ('uw',('u','w')), ('vw',('v','w'))]:
            cols = [outer2(t[pair[0]], t[pair[1]]) for t in terms]
            rows = [list(row) for row in zip(*cols)]
            pair_mats[name] = rank_mod(rows,p) if p else rank_q(rows)
        factor_span = {}
        for k in ['u','v','w']:
            rows = [t[k] for t in terms]
            factor_span[k] = rank_mod(rows,p) if p else rank_q(rows)
        J = jacobian_columns(terms)
        jrank = rank_mod(J,p) if p else rank_q(J)
        out[label] = {
            'term_ranks': term_ranks,
            'ordered_rank_triple_counts': {str(k): v for k,v in sorted(Counter(ordered).items())},
            'sorted_rank_type_counts': {str(k): v for k,v in sorted(Counter(sorted_types).items())},
            'pairing_column_ranks': pair_mats,
            'factor_span_ranks': factor_span,
            'jacobian_rank': jrank,
            'jacobian_nullity_in_27r_parameters': 27*S['rank'] - jrank,
            'expected_scaling_nullity_2r': 2*S['rank'],
            'excess_nullity_over_scaling': 27*S['rank'] - jrank - 2*S['rank'],
        }
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('scheme')
    ap.add_argument('--json-out')
    args = ap.parse_args()
    out = analyze(Path(args.scheme))
    txt = json.dumps(out, indent=2, sort_keys=True)
    print(txt)
    if args.json_out:
        Path(args.json_out).write_text(txt + '\n')

if __name__ == '__main__':
    main()
