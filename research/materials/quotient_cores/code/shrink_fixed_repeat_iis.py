#!/usr/bin/env python3
"""analysis: shrink the fixed-repeat compact E11-core contradiction with HiGHS.

The fixed p=1 repeat instance is infeasible very quickly in HiGHS, while a direct
CP-SAT assumption-core extraction timed out.  This script uses HiGHS as an
infeasibility oracle to greedily delete compact high-level constraints while
preserving infeasibility, then emits a clean CNF for the surviving subset.

This is an engineering path toward a short DRAT certificate: the shrink result is
not itself a proof, but if the emitted CNF is UNSAT and drat-trim verifies the
DRAT trace, the fixed-repeat branch is independently certified.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from complete_core_and_transversal import ROOT
from extract_fixed_repeat_core_cnf import build_high_level_constraints, emit_clean_cnf
from core_repeat_symmetry_and_cnf import label8, sha256

OUTDIR = ROOT / 'workspace/data/repeat_branch_certificate'


def build_matrix_for_subset(data: dict, indices: List[int], fixed_repeat: int):
    points = data['points']
    point_cap = data['point_cap']
    n = 255
    rows = []
    lbs = []
    ubs = []

    # Hard total equality.
    rows.append({p - 1: 1 for p in points})
    lbs.append(float(data['s']))
    ubs.append(float(data['s']))

    # Selected compact constraints.
    for idx in indices:
        c = data['constraints'][idx]
        row = {int(p) - 1: int(coef) for p, coef in c['coeffs'].items() if coef}
        if c['sense'] == '<=':
            lb, ub = -np.inf, float(c['rhs'])
        else:
            lb, ub = float(c['rhs']), np.inf
        rows.append(row)
        lbs.append(lb)
        ubs.append(ub)

    A = lil_matrix((len(rows), n), dtype=float)
    for i, row in enumerate(rows):
        for j, v in row.items():
            A[i, j] = float(v)
    lower = np.zeros(n)
    upper = np.array([point_cap[p] for p in points], dtype=float)
    lower[fixed_repeat - 1] = 2
    upper[fixed_repeat - 1] = 2
    return A.tocsr(), np.array(lbs, dtype=float), np.array(ubs, dtype=float), Bounds(lower, upper)


def solve_subset(data: dict, indices: List[int], fixed_repeat: int, time_limit: float) -> dict:
    A, lbs, ubs, bounds = build_matrix_for_subset(data, indices, fixed_repeat)
    t0 = time.time()
    res = milp(
        c=np.zeros(255),
        integrality=np.ones(255, dtype=int),
        bounds=bounds,
        constraints=LinearConstraint(A, lbs, ubs),
        options={'time_limit': float(time_limit), 'mip_rel_gap': 0.0, 'presolve': True},
    )
    out = {
        'status': int(res.status),
        'success': bool(res.success),
        'message': str(res.message),
        'solve_sec': round(time.time() - t0, 4),
        'rows': int(A.shape[0]),
    }
    if res.x is not None:
        vals = np.rint(res.x).astype(int)
        out['counts'] = {str(p): int(vals[p - 1]) for p in range(1, 256) if vals[p - 1]}
    return out


def chunked(seq: List[int], size: int):
    for i in range(0, len(seq), size):
        yield seq[i:i+size]


def greedy_shrink(data: dict, fixed_repeat: int, time_limit: float, passes: int, min_chunk: int) -> dict:
    selected = list(range(len(data['constraints'])))
    log = []
    base = solve_subset(data, selected, fixed_repeat, time_limit)
    if base['status'] != 2:
        return {'initial': base, 'selected_indices': selected, 'log': log, 'failed': 'initial model not proven infeasible'}

    # Work by kind first, then by progressively smaller chunks.  Preserve order
    # so emitted metadata is deterministic.
    kind_order = ['wang', 'contraction_lower', 'unconditional_qcut']
    for pass_id in range(passes):
        changed = False
        for kind in kind_order:
            kind_sel = [i for i in selected if data['constraints'][i]['kind'] == kind]
            if not kind_sel:
                continue
            size = max(min_chunk, 2 ** max(0, (len(kind_sel).bit_length() - 2 - pass_id)))
            while size >= min_chunk:
                removed_in_size = 0
                chunks = list(chunked([i for i in selected if data['constraints'][i]['kind'] == kind], size))
                for ch in chunks:
                    if not ch:
                        continue
                    cand_set = set(selected)
                    for i in ch:
                        cand_set.discard(i)
                    cand = [i for i in selected if i in cand_set]
                    r = solve_subset(data, cand, fixed_repeat, time_limit)
                    log.append({'pass': pass_id, 'kind': kind, 'chunk_size': size, 'removed_candidate': len(ch), 'candidate_remaining': len(cand), 'status': r['status'], 'solve_sec': r['solve_sec']})
                    if r['status'] == 2:  # infeasible remains, deletion accepted
                        selected = cand
                        removed_in_size += len(ch)
                        changed = True
                if removed_in_size == 0:
                    size //= 2
                else:
                    # After successful removals, retry same size on the shorter list.
                    pass
                if size < min_chunk:
                    break
        if not changed:
            break

    # One final single-constraint pass if the set is not too large.
    if len(selected) <= 2000:
        for i in list(selected):
            cand = [j for j in selected if j != i]
            r = solve_subset(data, cand, fixed_repeat, time_limit)
            log.append({'pass': 'single', 'kind': data['constraints'][i]['kind'], 'chunk_size': 1, 'removed_candidate': 1, 'candidate_remaining': len(cand), 'status': r['status'], 'solve_sec': r['solve_sec']})
            if r['status'] == 2:
                selected = cand

    final = solve_subset(data, selected, fixed_repeat, max(time_limit, 30.0))
    return {'initial': base, 'final': final, 'selected_indices': selected, 'log': log}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', type=Path, default=ROOT / 'workspace/data/quotient_rank_cuts/core_e11_multiset_quotient_sep_24r_fullstored.json')
    ap.add_argument('--fixed-repeat', type=int, default=1)
    ap.add_argument('--time-limit', type=float, default=2.0, help='HiGHS time limit per deletion test')
    ap.add_argument('--passes', type=int, default=3)
    ap.add_argument('--min-chunk', type=int, default=8)
    ap.add_argument('--outdir', type=Path, default=OUTDIR / 'iis_shrink_p1')
    ap.add_argument('--stem', default='fixed_repeat_p1_iis')
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    data = build_high_level_constraints(args.source, args.fixed_repeat)
    print(f"built high-level constraints={len(data['constraints'])} input_counts={data['constraint_input_counts']}")
    shrink = greedy_shrink(data, args.fixed_repeat, args.time_limit, args.passes, args.min_chunk)
    sel = shrink['selected_indices']
    by_kind = Counter(data['constraints'][i]['kind'] for i in sel)
    print(f"selected={len(sel)} by_kind={dict(by_kind)} final={shrink.get('final', shrink.get('initial'))}")

    cnf_meta = None
    if shrink.get('final', shrink.get('initial')).get('status') == 2:
        cnf_meta = emit_clean_cnf(data, args.fixed_repeat, sel, args.outdir, args.stem)
        print(f"emitted CNF vars={cnf_meta['cnf_variables']} clauses={cnf_meta['cnf_clauses']}")

    # Store a light representation of selected constraints with full provenance.
    selected_records = []
    for i in sel:
        c = data['constraints'][i]
        rec = {k: v for k, v in c.items() if k != 'coeffs'}
        rec['index'] = i
        rec['support_coeff_count'] = len(c['coeffs'])
        selected_records.append(rec)

    result = {
        'schema': 'fixed_repeat_iis_shrink_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': data['s'],
        'fixed_repeat_point': args.fixed_repeat,
        'fixed_repeat_label': label8(data['core'], args.fixed_repeat),
        'source': str(args.source),
        'source_sha256': sha256(args.source),
        'input_constraint_counts': data['constraint_input_counts'],
        'point_cap_distribution': {str(k): int(v) for k, v in sorted(Counter(data['point_cap'].values()).items())},
        'shrink_parameters': {'time_limit_per_test': args.time_limit, 'passes': args.passes, 'min_chunk': args.min_chunk},
        'initial_status': shrink['initial'],
        'final_status': shrink.get('final'),
        'selected_constraint_count': len(sel),
        'selected_constraints_by_kind': dict(by_kind),
        'selected_indices': sel,
        'selected_constraint_records': selected_records,
        'deletion_tests': len(shrink['log']),
        'deletion_log_tail': shrink['log'][-200:],
        'clean_cnf': cnf_meta,
        'total_elapsed_sec': round(time.time() - t0, 3),
    }
    summary = args.outdir / 'shrink_summary.json'
    summary.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'Saved {summary}')
    print(json.dumps({'summary': str(summary), 'selected': len(sel), 'by_kind': dict(by_kind), 'cnf_clauses': None if cnf_meta is None else cnf_meta['cnf_clauses'], 'elapsed': result['total_elapsed_sec']}, sort_keys=True))


if __name__ == '__main__':
    main()
