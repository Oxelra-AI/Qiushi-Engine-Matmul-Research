#!/usr/bin/env python3
"""Selective promotion of repeatedly implicated Wang rows to complete at-most constraints.

This script is a controlled analysis experiment.  It starts from an existing
witness-subset run directory (base residual-0/1 graph + exact cardinality +
learned witness/full-row clauses) and promotes a small number of Wang rows to
full residual capacity constraints using compact PySAT sequential counters.

The scientific purpose is to compare bounded decision/proof behavior after
adding a few complete Wang inequalities, not to treat the number of unencoded
full-LUT violations in one solver-returned SAT model as a monotone progress
metric.  A valid promoted row shrinks the encoded support set even if the next
arbitrary satisfying assignment violates more unencoded rows.  Every promoted
row is stored with row-level provenance and an explicit auxiliary-variable
interval, so analysis-style counter variable collisions can be independently
checked.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys
import time
from collections import defaultdict
from typing import Dict, Iterable, List, Sequence, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))

from graph_coloring_certificate import load_lut, make_pivot_dict, in_span_piv  # noqa:E402
from wang_capacity_lazy import unpack_basis  # noqa:E402
from witness_subset_separation import (  # noqa:E402
    atleast_pysat,
    atmost_pysat,
    write_cnf,
    run_cadical,
    run_drat_trim,
    parse_model_from_log,
    full_lut_violations,
    sha256_file,
)


def read_jsonl(path: pathlib.Path) -> List[dict]:
    out = []
    if not path.exists():
        return out
    with path.open() as f:
        for line_no, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            rec['_line'] = line_no
            out.append(rec)
    return out


def read_base_and_summary(run_dir: pathlib.Path) -> Tuple[dict, dict, List[dict]]:
    base = json.loads((run_dir / 'base_metadata.json').read_text())
    summary = json.loads((run_dir / 'summary.json').read_text()) if (run_dir / 'summary.json').exists() else {}
    learned = read_jsonl(run_dir / 'learned_clauses.jsonl')
    return base, summary, learned


def wang_values_for_key(lut: Dict[int, int], key: int, fixed_prefix: Sequence[int], survivors: Sequence[int]) -> dict:
    if int(key) not in lut:
        raise KeyError(f'row key {key} absent from LUT')
    lb = int(lut[int(key)])
    cap = 20 - lb
    basis = unpack_basis(int(key))
    piv = make_pivot_dict(basis)
    fixed_count = sum(1 for p in fixed_prefix if in_span_piv(piv, int(p)))
    residual = cap - fixed_count
    row_points = tuple(sorted(int(s) for s in survivors if in_span_piv(piv, int(s))))
    return {
        'key': int(key),
        'lb': lb,
        'cap': cap,
        'fixed_count': int(fixed_count),
        'residual': int(residual),
        'row_points': row_points,
        'row_candidate_count': len(row_points),
    }


def validate_learned_records(records: Sequence[dict], lut: Dict[int, int], fixed_prefix: Sequence[int], survivors: Sequence[int], var_map: Dict[int, int]) -> Tuple[List[List[int]], dict]:
    """Validate learned clauses and return re-literalized clauses in file order."""
    survivor_set = set(int(s) for s in survivors)
    row_cache: Dict[int, Tuple[int, int, int, int, object]] = {}
    clauses: List[List[int]] = []
    bad = []
    by_source = defaultdict(int)
    by_residual = defaultdict(int)
    keys_seen = set()
    for rec in records:
        key = int(rec['key'])
        keys_seen.add(key)
        if key not in row_cache:
            if key not in lut:
                bad.append({'line': rec.get('_line'), 'key': key, 'reason': 'key_absent'})
                continue
            lb = int(lut[key])
            cap = 20 - lb
            basis = unpack_basis(key)
            piv = make_pivot_dict(basis)
            fixed_count = sum(1 for p in fixed_prefix if in_span_piv(piv, int(p)))
            residual = cap - fixed_count
            row_cache[key] = (lb, cap, fixed_count, residual, piv)
        lb, cap, fixed_count, residual, piv = row_cache[key]
        pts = [int(p) for p in rec['points']]
        probs = []
        if int(rec.get('lb', lb)) != lb:
            probs.append('lb_mismatch')
        if int(rec.get('cap', cap)) != cap:
            probs.append('cap_mismatch')
        if int(rec.get('fixed_count', fixed_count)) != fixed_count:
            probs.append('fixed_count_mismatch')
        if int(rec.get('residual', residual)) != residual:
            probs.append('residual_mismatch')
        if residual < 0:
            probs.append('negative_residual')
        elif len(pts) != residual + 1:
            probs.append(f'len_points_{len(pts)}_not_residual_plus_one_{residual+1}')
        if len(set(pts)) != len(pts):
            probs.append('duplicate_points')
        for p in pts:
            if p not in survivor_set:
                probs.append(f'point_{p}_not_survivor')
            elif not in_span_piv(piv, p):
                probs.append(f'point_{p}_not_in_row')
            elif p not in var_map:
                probs.append(f'point_{p}_no_variable')
        if probs:
            bad.append({'line': rec.get('_line'), 'key': key, 'points': pts, 'problems': probs})
            if len(bad) >= 20:
                break
            continue
        lits = [-var_map[p] for p in pts]
        clauses.append(lits)
        by_source[str(rec.get('source', '?'))] += 1
        by_residual[str(residual)] += 1
    if bad:
        raise ValueError(f'bad learned records: {bad[:5]}')
    return clauses, {
        'learned_records_checked': len(records),
        'learned_distinct_row_keys': len(keys_seen),
        'learned_by_source': dict(sorted(by_source.items())),
        'learned_by_residual': dict(sorted(by_residual.items(), key=lambda kv: int(kv[0]))),
    }


def build_base_formula(base: dict) -> Tuple[List[List[int]], Dict[int, int], int, dict]:
    survivors = [int(x) for x in base['base']['survivors']]
    target = int(base['target'])
    var_map = {p: i + 1 for i, p in enumerate(survivors)}
    top_id = len(var_map)
    clauses: List[List[int]] = []
    clauses.extend([[int(x) for x in edge['lits']] for edge in base['base'].get('base_edges', [])])
    al, top_id = atleast_pysat(list(var_map.values()), target, top_id)
    clauses.extend(al)
    after_atleast = top_id
    am, top_id = atmost_pysat(list(var_map.values()), target, top_id)
    clauses.extend(am)
    meta = {
        'base_edges': len(base['base'].get('base_edges', [])),
        'atleast_clauses': len(al),
        'atmost_clauses': len(am),
        'candidate_variables': len(var_map),
        'after_atleast_top': after_atleast,
        'base_final_top': top_id,
        'base_clause_count': len(clauses),
    }
    return clauses, var_map, top_id, meta


def row_score_records(records: Sequence[dict], eligible_keys: Iterable[int]) -> List[dict]:
    stats: Dict[int, dict] = {}
    eligible = set(int(k) for k in eligible_keys)
    for rec in records:
        key = int(rec['key'])
        if key not in eligible:
            continue
        st = stats.setdefault(key, {
            'key': key,
            'record_count': 0,
            'witness_record_count': 0,
            'full_record_count': 0,
            'rounds': set(),
            'residual_values': set(),
            'source_values': set(),
            'max_selection_count': 0,
            'max_excess': 0,
            'max_full_direct_clause_count_for_row': 0,
            'row_candidate_count_values': set(),
        })
        st['record_count'] += 1
        source = str(rec.get('source', '?'))
        st['source_values'].add(source)
        if source == 'witness_subset':
            st['witness_record_count'] += 1
        if source == 'full_row_direct':
            st['full_record_count'] += 1
        if 'round' in rec:
            st['rounds'].add(int(rec['round']))
        if 'residual' in rec:
            st['residual_values'].add(int(rec['residual']))
        if 'selection_count' in rec:
            st['max_selection_count'] = max(st['max_selection_count'], int(rec['selection_count']))
        if 'excess' in rec:
            st['max_excess'] = max(st['max_excess'], int(rec['excess']))
        if 'full_direct_clause_count_for_row' in rec:
            st['max_full_direct_clause_count_for_row'] = max(st['max_full_direct_clause_count_for_row'], int(rec['full_direct_clause_count_for_row']))
        if 'row_candidate_count' in rec:
            st['row_candidate_count_values'].add(int(rec['row_candidate_count']))
    out = []
    for st in stats.values():
        st = dict(st)
        st['round_count'] = len(st.pop('rounds'))
        st['residual_values'] = sorted(st['residual_values'])
        st['source_values'] = sorted(st['source_values'])
        st['row_candidate_count_values'] = sorted(st['row_candidate_count_values'])
        out.append(st)
    # Prefer rows that appear in many rounds; among them, many witness clauses and high excess.
    out.sort(key=lambda s: (s['round_count'], s['witness_record_count'], s['record_count'], s['max_excess'], s['max_selection_count']), reverse=True)
    return out


def choose_rows(records: Sequence[dict], lut: Dict[int, int], base: dict, var_map: Dict[int, int], promote_count: int, min_rounds: int, min_residual: int, max_residual: int, max_row_points: int) -> Tuple[List[dict], List[dict]]:
    fixed_prefix = [int(x) for x in base['fixed_prefix']]
    survivors = [int(x) for x in base['base']['survivors']]
    eligible_keys = set()
    row_values = {}
    # Only rows that appeared in witness/full learned records can be "implicated" by prior separation.
    for rec in records:
        key = int(rec['key'])
        if key in row_values:
            rv = row_values[key]
        else:
            rv = wang_values_for_key(lut, key, fixed_prefix, survivors)
            row_values[key] = rv
        residual = int(rv['residual'])
        row_count = int(rv['row_candidate_count'])
        if residual < min_residual or residual > max_residual:
            continue
        if residual >= row_count:
            continue
        if max_row_points > 0 and row_count > max_row_points:
            continue
        # Complete promotion is aimed at rows not already complete in the base graph.
        if residual <= 1:
            continue
        eligible_keys.add(key)
    ranked = row_score_records(records, eligible_keys)
    selected = []
    for st in ranked:
        if st['round_count'] < min_rounds:
            continue
        rv = row_values[int(st['key'])]
        st = {**st, **{k: (list(v) if isinstance(v, tuple) else v) for k, v in rv.items() if k != 'row_points'},
              'row_points_head': list(rv['row_points'][:20])}
        selected.append(st)
        if len(selected) >= promote_count:
            break
    return selected, ranked


def add_promotions(clauses: List[List[int]], var_map: Dict[int, int], top_id: int, lut: Dict[int, int], base: dict, selected_rows: Sequence[dict]) -> Tuple[List[List[int]], int, List[dict]]:
    fixed_prefix = [int(x) for x in base['fixed_prefix']]
    survivors = [int(x) for x in base['base']['survivors']]
    promotion_records = []
    for order, row in enumerate(selected_rows):
        key = int(row['key'])
        rv = wang_values_for_key(lut, key, fixed_prefix, survivors)
        residual = int(rv['residual'])
        row_points = tuple(int(p) for p in rv['row_points'])
        if residual < 0:
            new_clauses = [[]]
            top_before = top_id
            top_after = top_id
        elif residual >= len(row_points):
            continue
        else:
            row_lits = [var_map[p] for p in row_points]
            top_before = top_id
            new_clauses, top_id = atmost_pysat(row_lits, residual, top_id)
            top_after = top_id
        clauses.extend(new_clauses)
        rec = {
            'schema': 'promoted_wang_row_v1',
            'promotion_order': int(order),
            'key': key,
            'lb': int(rv['lb']),
            'cap': int(rv['cap']),
            'fixed_count': int(rv['fixed_count']),
            'residual': residual,
            'row_points': list(row_points),
            'row_lits': [var_map[p] for p in row_points],
            'row_candidate_count': len(row_points),
            'aux_top_before': int(top_before),
            'aux_top_after': int(top_after),
            'aux_start': int(top_before + 1) if top_after > top_before else None,
            'aux_end': int(top_after) if top_after > top_before else None,
            'promotion_clause_count': len(new_clauses),
            'source_selection_stats': row,
        }
        promotion_records.append(rec)
    return clauses, top_id, promotion_records


def solve_and_scan(cnf_path: pathlib.Path, clauses: Sequence[Sequence[int]], top_id: int, args, lut: Dict[int, int], base: dict, var_map: Dict[int, int], out_dir: pathlib.Path) -> dict:
    write_cnf(clauses, top_id, cnf_path)
    sol = run_cadical(cnf_path, args.solve_time, with_drat=False)
    result = {
        'cadical_exit': sol['exit'],
        'cadical_sec': round(sol['elapsed_sec'], 2),
        'cnf': str(cnf_path),
        'cnf_sha256': sha256_file(cnf_path),
        'variables': top_id,
        'clauses': len(clauses),
    }
    if sol['unsat']:
        drat_sol = run_cadical(cnf_path, args.drat_solve_time, with_drat=True)
        result.update({
            'status': 'UNSAT',
            'drat_cadical_exit': drat_sol['exit'],
            'drat_cadical_sec': round(drat_sol['elapsed_sec'], 2),
            'drat': drat_sol.get('drat'),
            'drat_sha256': sha256_file(pathlib.Path(drat_sol['drat'])) if drat_sol.get('drat') else None,
        })
        if drat_sol['unsat'] and drat_sol.get('drat'):
            trim = run_drat_trim(cnf_path, pathlib.Path(drat_sol['drat']), args.drat_time)
        else:
            trim = {'verified': False, 'reason': 'drat-producing solve did not return UNSAT'}
        result['drat_trim'] = trim
        return result
    if sol['sat'] and sol['has_model']:
        selected = parse_model_from_log(pathlib.Path(sol['log']), var_map)
        scan_info = {'model_found': selected is not None}
        if selected is not None:
            fixed_prefix = [int(x) for x in base['fixed_prefix']]
            survivors = [int(x) for x in base['base']['survivors']]
            t0 = time.time()
            violations = list(full_lut_violations(lut, fixed_prefix, selected, survivors))
            scan_info.update({
                'selected_size': len(selected),
                'target': int(base['target']),
                'support_size': len(set(fixed_prefix) | set(selected)),
                'full_lut_violation_count': len(violations),
                'scan_sec': round(time.time() - t0, 2),
                'max_excess': max((int(v['excess']) for v in violations), default=0),
                'violations_by_residual': {},
                'violations_head': [
                    {k: (list(vv)[:20] if isinstance(vv, tuple) else vv)
                     for k, vv in v.items() if k != 'row_survivors'}
                    for v in violations[:20]
                ],
                'selected': selected,
            })
            by_res = defaultdict(int)
            for v in violations:
                by_res[str(int(v['residual']))] += 1
            scan_info['violations_by_residual'] = dict(sorted(by_res.items(), key=lambda kv: int(kv[0])))
            (out_dir / 'sat_model_scan.json').write_text(json.dumps(scan_info, indent=2, sort_keys=True) + '\n')
        result.update({'status': 'SAT_AFTER_PROMOTION', 'sat_model_scan': scan_info})
        return result
    result.update({'status': 'SOLVER_UNKNOWN', 'cadical_log': sol.get('log')})
    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed-run-dir', required=True)
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--promote-count', type=int, default=10)
    ap.add_argument('--min-rounds', type=int, default=2)
    ap.add_argument('--min-residual', type=int, default=2)
    ap.add_argument('--max-residual', type=int, default=15)
    ap.add_argument('--max-row-points', type=int, default=0, help='0 means no cap')
    ap.add_argument('--solve-time', type=int, default=300)
    ap.add_argument('--drat-solve-time', type=int, default=900)
    ap.add_argument('--drat-time', type=int, default=900)
    args = ap.parse_args()

    seed_dir = pathlib.Path(args.seed_run_dir)
    out_dir = pathlib.Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    print(f'Loading seed run {seed_dir}...')
    base, seed_summary, learned = read_base_and_summary(seed_dir)
    print(f'  learned records: {len(learned):,}')
    print(f'Loading LUT {args.lut}...')
    lut = load_lut(pathlib.Path(args.lut))
    print(f'  rows: {len(lut):,}')

    base_clauses, var_map, top_id, base_formula_meta = build_base_formula(base)
    learned_clauses, learned_meta = validate_learned_records(
        learned, lut, [int(x) for x in base['fixed_prefix']], [int(x) for x in base['base']['survivors']], var_map)
    clauses = list(base_clauses) + learned_clauses
    seed_clause_count = len(clauses)
    selected, ranked = choose_rows(
        learned, lut, base, var_map,
        promote_count=args.promote_count,
        min_rounds=args.min_rounds,
        min_residual=args.min_residual,
        max_residual=args.max_residual,
        max_row_points=args.max_row_points,
    )
    (out_dir / 'row_ranking_head.json').write_text(json.dumps(ranked[:200], indent=2, sort_keys=True) + '\n')
    if not selected:
        raise SystemExit('no eligible rows selected for promotion')
    print('Selected rows for complete promotion:')
    for st in selected:
        print(f"  key={st['key']} rounds={st['round_count']} recs={st['record_count']} wit={st['witness_record_count']} residual={st['residual']} row_pts={st['row_candidate_count']}")

    clauses, final_top, promotion_records = add_promotions(clauses, var_map, top_id, lut, base, selected)
    (out_dir / 'promoted_rows.json').write_text(json.dumps({
        'schema': 'promoted_rows_v1',
        'seed_run_dir': str(seed_dir),
        'seed_summary_status': seed_summary.get('status'),
        'seed_current_cnf': seed_summary.get('current_cnf'),
        'promotion_count_requested': args.promote_count,
        'promotion_count_encoded': len(promotion_records),
        'promotions': promotion_records,
    }, indent=2, sort_keys=True) + '\n')

    cnf_path = out_dir / 'promoted.cnf'
    solve_result = solve_and_scan(cnf_path, clauses, final_top, args, lut, base, var_map, out_dir)
    result = {
        'schema': 'selective_promotion_result_v1',
        'seed_run_dir': str(seed_dir),
        'seed_summary_status': seed_summary.get('status'),
        'branch': base.get('branch'),
        'idx': base.get('idx'),
        'fixed_prefix': base.get('fixed_prefix'),
        'target': base.get('target'),
        'survivor_count': base.get('survivor_count'),
        'base_formula_meta': base_formula_meta,
        'learned_meta': learned_meta,
        'seed_clause_count_before_promotion': seed_clause_count,
        'seed_top_before_promotion': top_id,
        'promotion_count': len(promotion_records),
        'promotion_clause_count': sum(int(r['promotion_clause_count']) for r in promotion_records),
        'final_variables': final_top,
        'final_clauses': len(clauses),
        'promotion_metadata': str(out_dir / 'promoted_rows.json'),
        **solve_result,
    }
    (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'status': result['status'],
        'promotions': result['promotion_count'],
        'promotion_clauses': result['promotion_clause_count'],
        'final_clauses': result['final_clauses'],
        'final_variables': result['final_variables'],
        'drat_verified': result.get('drat_trim', {}).get('verified'),
        'sat_violations': result.get('sat_model_scan', {}).get('full_lut_violation_count'),
    }, sort_keys=True))


if __name__ == '__main__':
    main()
