#!/usr/bin/env python3
"""Profile complete Wang residual layers for arbitrary fixed A-support prefixes.

For a prefix such as the rep2 marked branch [1,2,10], compute the survivor
universe after residual-0 exclusions and residual-1 base edges, then scan the
complete Wang LUT and count how expensive it would be to encode all rows of each
residual as direct forbidden (r+1)-subsets.  This is a planning/evidence tool:
it does not prove exclusion by itself.
"""
from __future__ import annotations
import argparse
import json
import pathlib
import sys
import time
from collections import defaultdict
from math import comb
from typing import Sequence

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from graph_coloring_certificate import load_lut, make_pivot_dict, in_span_piv  # noqa:E402
from witness_subset_separation import process_rep2, build_base_cnf  # noqa:E402
from wang_capacity_lazy import unpack_basis  # noqa:E402


def parse_prefix(s: str) -> list[int]:
    out = [int(x) for x in s.replace(';', ',').split(',') if x.strip()]
    if len(out) != len(set(out)):
        raise SystemExit(f'duplicate prefix points: {out}')
    return out


def profile(lut: dict[int, int], prefix: Sequence[int], max_residual: int) -> dict:
    candidates = sorted(m for m in range(1, 512) if m not in set(prefix))
    info = process_rep2(lut, list(prefix), candidates)
    survivors = [int(x) for x in info['survivors']]
    if info.get('impossible_rows'):
        return {
            'prefix': list(prefix), 'status': 'FIXED_PREFIX_VIOLATES',
            'impossible_rows': info['impossible_rows'][:20],
            'candidate_count': len(candidates),
        }
    _base_clauses, _var_map, _top_id, base_meta = build_base_cnf(info)
    out = {
        'prefix': list(prefix),
        'status': 'PROFILED',
        'candidate_count': len(candidates),
        'survivor_count': len(survivors),
        'target': int(info['target']),
        'base_vertex_exclusions': len(info.get('vertex_exclusions', [])),
        'base_edges': len(info.get('base_edges', [])),
        'base_formula_meta': base_meta,
        'residual': {},
        'row_size_hist_by_residual': {},
        'largest_rows_by_residual': {},
    }
    counts = defaultdict(int)
    clause_counts = defaultdict(int)
    max_row_size = defaultdict(int)
    row_size_hist = defaultdict(lambda: defaultdict(int))
    largest = defaultdict(list)
    t0 = time.time()
    for key, lb0 in lut.items():
        lb = int(lb0)
        cap = 20 - lb
        # residual = cap - fixed_count; fixed_count<=|prefix|.
        # if even max fixed_count cannot bring residual below max_residual, skip.
        if cap - len(prefix) > max_residual:
            continue
        basis = unpack_basis(int(key))
        piv = make_pivot_dict(basis)
        fixed_count = sum(1 for p in prefix if in_span_piv(piv, int(p)))
        residual = cap - fixed_count
        if residual < 0 or residual > max_residual:
            continue
        row_points = [s for s in survivors if in_span_piv(piv, int(s))]
        n = len(row_points)
        if n <= residual:
            continue
        c = comb(n, residual + 1)
        counts[residual] += 1
        clause_counts[residual] += c
        max_row_size[residual] = max(max_row_size[residual], n)
        row_size_hist[residual][n] += 1
        largest[residual].append((c, n, int(key), lb, fixed_count))
    for r in sorted(counts):
        largest[r].sort(reverse=True)
        out['residual'][str(r)] = {
            'rows': counts[r],
            'direct_clause_count': clause_counts[r],
            'max_row_size': max_row_size[r],
            'largest_rows': [
                {'clauses': c, 'row_size': n, 'key': key, 'lb': lb, 'fixed_count': fc}
                for c, n, key, lb, fc in largest[r][:20]
            ],
        }
        out['row_size_hist_by_residual'][str(r)] = {str(k): v for k, v in sorted(row_size_hist[r].items())}
    out['scan_sec'] = round(time.time() - t0, 2)
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--prefixes', required=True, help='semicolon-separated prefixes, each comma-separated, e.g. 1,2,3;1,2,10')
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--max-residual', type=int, default=3)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()
    lut = load_lut(pathlib.Path(args.lut))
    records = []
    for s in args.prefixes.split(';'):
        s = s.strip()
        if not s:
            continue
        prefix = parse_prefix(s)
        print(f'profiling prefix {prefix}...')
        rec = profile(lut, prefix, args.max_residual)
        records.append(rec)
        brief = {r: {'rows': d['rows'], 'clauses': d['direct_clause_count'], 'max_row_size': d['max_row_size']} for r, d in rec.get('residual', {}).items()}
        print(json.dumps({'prefix': prefix, 'survivors': rec.get('survivor_count'), 'target': rec.get('target'), 'residual': brief, 'scan_sec': rec.get('scan_sec')}, sort_keys=True))
    out = {'schema': 'fixed_prefix_residual_profile_v1', 'records': records}
    path = pathlib.Path(args.out)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f'saved {path}')


if __name__ == '__main__':
    main()
