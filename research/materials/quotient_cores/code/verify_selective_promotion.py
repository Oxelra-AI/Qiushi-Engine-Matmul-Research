#!/usr/bin/env python3
"""Verify analysis selective-promotion CNF provenance and regeneration.

Checks a run directory produced by selective_promotion.py:
  * imports and revalidates the seed run's base and learned clauses;
  * verifies every promoted row against the Wang LUT and fixed prefix;
  * checks promoted-row auxiliary intervals are fresh, increasing, and disjoint;
  * regenerates the entire promoted CNF from base + learned + promoted counters;
  * optionally replays DRAT-trim if the promoted formula was UNSAT.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
import time
from math import comb
from typing import Dict, List, Sequence, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from graph_coloring_certificate import load_lut, make_pivot_dict, in_span_piv  # noqa:E402
from wang_capacity_lazy import unpack_basis  # noqa:E402
from witness_subset_separation import atleast_pysat, atmost_pysat  # noqa:E402
from selective_promotion import read_base_and_summary, validate_learned_records, build_base_formula  # noqa:E402


def read_cnf(path: pathlib.Path) -> Tuple[int, List[List[int]]]:
    top = None
    declared = None
    clauses: List[List[int]] = []
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c'):
                continue
            if line.startswith('p '):
                parts = line.split()
                top = int(parts[2])
                declared = int(parts[3])
                continue
            xs = [int(tok) for tok in line.split()]
            if xs and xs[-1] == 0:
                xs = xs[:-1]
            clauses.append(xs)
    if top is None or declared is None:
        raise ValueError(f'no DIMACS header in {path}')
    if declared != len(clauses):
        raise ValueError(f'DIMACS declared {declared} clauses but found {len(clauses)}')
    return top, clauses


def wang_row(lut: Dict[int, int], key: int, fixed_prefix: Sequence[int], survivors: Sequence[int]) -> dict:
    if key not in lut:
        raise AssertionError(f'row key {key} absent from LUT')
    lb = int(lut[key])
    cap = 20 - lb
    basis = unpack_basis(key)
    piv = make_pivot_dict(basis)
    fixed_count = sum(1 for p in fixed_prefix if in_span_piv(piv, int(p)))
    residual = cap - fixed_count
    row_points = tuple(sorted(int(s) for s in survivors if in_span_piv(piv, int(s))))
    return {'lb': lb, 'cap': cap, 'fixed_count': fixed_count, 'residual': residual, 'row_points': row_points}


def verify_promotions(promoted: dict, base: dict, lut: Dict[int, int], var_map: Dict[int, int], seed_top: int) -> dict:
    fixed_prefix = [int(x) for x in base['fixed_prefix']]
    survivors = [int(x) for x in base['base']['survivors']]
    problems = []
    intervals = []
    total_clauses = 0
    regenerated: List[List[int]] = []
    top = seed_top
    last_top = seed_top
    for i, rec in enumerate(promoted.get('promotions', [])):
        key = int(rec['key'])
        row = wang_row(lut, key, fixed_prefix, survivors)
        pts = [int(x) for x in rec['row_points']]
        lits = [int(x) for x in rec['row_lits']]
        residual = int(row['residual'])
        local = []
        if int(rec['lb']) != row['lb']:
            local.append('lb_mismatch')
        if int(rec['cap']) != row['cap']:
            local.append('cap_mismatch')
        if int(rec['fixed_count']) != row['fixed_count']:
            local.append('fixed_count_mismatch')
        if int(rec['residual']) != residual:
            local.append('residual_mismatch')
        if pts != list(row['row_points']):
            local.append('row_points_mismatch')
        expected_lits = [var_map[p] for p in row['row_points']]
        if lits != expected_lits:
            local.append('row_lits_mismatch')
        if int(rec['row_candidate_count']) != len(row['row_points']):
            local.append('row_candidate_count_mismatch')
        if int(rec['aux_top_before']) != last_top:
            local.append(f'aux_top_before_{rec["aux_top_before"]}_not_previous_{last_top}')
        before = int(rec['aux_top_before'])
        if before != top:
            local.append(f'counter_regen_top_before_{before}_not_{top}')
        if residual < 0:
            enc = [[]]
            after = top
        else:
            enc, after = atmost_pysat(expected_lits, residual, top)
        regenerated.extend(enc)
        top = after
        last_top = int(rec['aux_top_after'])
        if after != int(rec['aux_top_after']):
            local.append(f'aux_top_after_{rec["aux_top_after"]}_not_regenerated_{after}')
        if len(enc) != int(rec['promotion_clause_count']):
            local.append(f'promotion_clause_count_{rec["promotion_clause_count"]}_not_{len(enc)}')
        if after > before:
            start = int(rec['aux_start']) if rec.get('aux_start') is not None else None
            end = int(rec['aux_end']) if rec.get('aux_end') is not None else None
            if start != before + 1 or end != after:
                local.append('aux_start_end_mismatch')
            intervals.append((before + 1, after, key))
        else:
            if rec.get('aux_start') is not None or rec.get('aux_end') is not None:
                local.append('unexpected_aux_interval_for_no_aux_counter')
        total_clauses += len(enc)
        if local:
            problems.append({'promotion_index': i, 'key': key, 'problems': local})
    # Interval disjointness and freshness beyond seed top.
    for a, b, key in intervals:
        if a <= seed_top:
            problems.append({'key': key, 'problems': [f'aux interval starts at {a} <= seed top {seed_top}']})
        if a > b:
            problems.append({'key': key, 'problems': [f'bad interval {a}>{b}']})
    sorted_intervals = sorted(intervals)
    for (a1, b1, k1), (a2, b2, k2) in zip(sorted_intervals, sorted_intervals[1:]):
        if a2 <= b1:
            problems.append({'key': k2, 'problems': [f'aux interval overlaps previous row {k1}: {a2}<={b1}']})
    return {
        'promotion_count': len(promoted.get('promotions', [])),
        'promotion_clause_count_regenerated': total_clauses,
        'promotion_aux_interval_count': len(intervals),
        'promotion_aux_intervals_head': [{'start': a, 'end': b, 'key': k} for a, b, k in sorted_intervals[:20]],
        'promotion_problems': problems[:50],
        'promotion_problem_count': len(problems),
        'regenerated_promotion_clauses': regenerated,
        'regenerated_top': top,
    }


def run_drat_trim(cnf: pathlib.Path, drat: pathlib.Path, timeout: int) -> dict:
    t0 = time.time()
    try:
        proc = subprocess.run(['drat-trim', str(cnf), str(drat)], capture_output=True, text=True, timeout=timeout)
        text = (proc.stdout or '') + '\n' + (proc.stderr or '')
        return {'exit': proc.returncode, 'elapsed_sec': round(time.time() - t0, 2), 'verified': proc.returncode == 0 and 'VERIFIED' in text}
    except subprocess.TimeoutExpired:
        return {'exit': None, 'elapsed_sec': timeout, 'verified': False, 'timeout': True}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--run-dir', required=True)
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--drat-replay', action='store_true')
    ap.add_argument('--drat-time', type=int, default=900)
    ap.add_argument('--out', default='')
    args = ap.parse_args()

    run_dir = pathlib.Path(args.run_dir)
    summary = json.loads((run_dir / 'summary.json').read_text())
    promoted = json.loads((run_dir / 'promoted_rows.json').read_text())
    seed_dir = pathlib.Path(summary['seed_run_dir'])
    base, seed_summary, learned = read_base_and_summary(seed_dir)
    lut = load_lut(pathlib.Path(args.lut))

    base_clauses, var_map, seed_top, base_meta = build_base_formula(base)
    learned_clauses, learned_meta = validate_learned_records(
        learned, lut, [int(x) for x in base['fixed_prefix']], [int(x) for x in base['base']['survivors']], var_map)
    seed_clauses = list(base_clauses) + learned_clauses
    promo_check = verify_promotions(promoted, base, lut, var_map, seed_top)
    regen_clauses = seed_clauses + promo_check.pop('regenerated_promotion_clauses')
    regen_top = promo_check.pop('regenerated_top')

    cnf_path = pathlib.Path(summary['cnf'])
    cnf_top, cnf_clauses = read_cnf(cnf_path)
    exact = cnf_top == regen_top and cnf_clauses == regen_clauses
    first_mismatch = None
    if not exact:
        for i, (a, b) in enumerate(zip(cnf_clauses, regen_clauses)):
            if a != b:
                first_mismatch = {'index': i, 'cnf': a, 'regen': b}
                break
        if first_mismatch is None:
            first_mismatch = {'index': min(len(cnf_clauses), len(regen_clauses)), 'reason': 'length or top mismatch'}

    drat = None
    if args.drat_replay and summary.get('drat'):
        drat_path = pathlib.Path(summary['drat'])
        drat = run_drat_trim(cnf_path, drat_path, args.drat_time) if drat_path.exists() else {'verified': False, 'reason': 'drat not found'}

    ok = (promo_check['promotion_problem_count'] == 0 and exact)
    if args.drat_replay:
        ok = ok and bool(drat and drat.get('verified'))
    result = {
        'schema': 'verify_selective_promotion_v1',
        'run_dir': str(run_dir),
        'seed_run_dir': str(seed_dir),
        'status': 'verified' if ok else 'failed',
        'summary_status': summary.get('status'),
        'base_meta': base_meta,
        'learned_meta': learned_meta,
        'promotion_check': promo_check,
        'cnf_check': {
            'cnf': str(cnf_path),
            'cnf_variables': cnf_top,
            'cnf_clauses': len(cnf_clauses),
            'regenerated_variables': regen_top,
            'regenerated_clauses': len(regen_clauses),
            'exact_sequence_match': exact,
            'first_mismatch': first_mismatch,
        },
        'drat_replay': drat,
    }
    out_path = pathlib.Path(args.out) if args.out else (run_dir / 'strict_verification.json')
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'status': result['status'],
        'summary_status': result['summary_status'],
        'promotions': promo_check['promotion_count'],
        'promotion_aux_intervals': promo_check['promotion_aux_interval_count'],
        'exact_sequence_match': exact,
        'drat_verified': None if drat is None else drat.get('verified'),
    }, sort_keys=True))
    if not ok:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
