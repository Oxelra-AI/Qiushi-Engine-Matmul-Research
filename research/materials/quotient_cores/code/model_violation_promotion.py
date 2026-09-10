#!/usr/bin/env python3
"""Wave-based selective promotion from the *current* SAT model's Wang violations.

Unlike selective_promotion.py, which selects historical rows from a seed
JSONL, this script repeatedly solves the accumulated formula, scans the returned
support against the full Wang LUT, and promotes a small number of currently
violated rows to complete residual at-most constraints using compact sequential
counters.  It is meant as a controlled comparison against unbounded witness learning: do a
few complete inequalities chosen from the present obstruction improve bounded
SAT/UNSAT/proof behavior or close the branch?  The number of unencoded
full-LUT violations in the next arbitrary SAT model is descriptive candidate
information, not a monotone proof-progress measure.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys
import time
from collections import defaultdict
from typing import Dict, List, Sequence, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))

from graph_coloring_certificate import load_lut, make_pivot_dict, in_span_piv  # noqa:E402
from wang_capacity_lazy import unpack_basis  # noqa:E402
from witness_subset_separation import (  # noqa:E402
    atmost_pysat, write_cnf, run_cadical, run_drat_trim, parse_model_from_log,
    full_lut_violations, sha256_file,
)
from selective_promotion import (  # noqa:E402
    read_base_and_summary, build_base_formula, validate_learned_records,
    wang_values_for_key, add_promotions,
)


def compact_violation(v: dict, row_points: Sequence[int]) -> dict:
    return {
        'key': int(v['key']),
        'lb': int(v['lb']),
        'cap': int(v['cap']),
        'fixed_count': int(v['fixed_count']),
        'residual': int(v['residual']),
        'selection_count': int(v['selection_count']),
        'excess': int(v['excess']),
        'selected_in_row': list(int(x) for x in v['selected_in_row']),
        'row_candidate_count': len(row_points),
        'row_points_head': list(int(x) for x in row_points[:30]),
    }


def select_violated_rows(violations: Sequence[dict], lut: Dict[int, int], fixed_prefix: Sequence[int], survivors: Sequence[int], promoted_keys: set, per_wave: int, min_residual: int, max_residual: int, max_row_points: int, prefer: str) -> Tuple[List[dict], List[dict]]:
    candidates = []
    for v in violations:
        key = int(v['key'])
        if key in promoted_keys:
            continue
        residual = int(v['residual'])
        if residual < min_residual or residual > max_residual:
            continue
        rv = wang_values_for_key(lut, key, fixed_prefix, survivors)
        row_points = rv['row_points']
        if residual >= len(row_points):
            continue
        if max_row_points > 0 and len(row_points) > max_row_points:
            continue
        rec = compact_violation(v, row_points)
        # Approximate cost of sequential counter by regenerating only if needed?  Use a cheap proxy n*r.
        rec['seqcounter_cost_proxy'] = int(len(row_points) * max(1, min(residual, len(row_points) - residual)))
        rec['source_values'] = ['current_model_violation']
        rec['round_count'] = 1
        rec['record_count'] = 1
        rec['witness_record_count'] = 0
        rec['full_record_count'] = 0
        rec['max_excess'] = int(v['excess'])
        rec['max_selection_count'] = int(v['selection_count'])
        rec['residual_values'] = [residual]
        rec['row_candidate_count_values'] = [len(row_points)]
        candidates.append(rec)
    if prefer == 'low_residual':
        candidates.sort(key=lambda r: (r['residual'], -r['excess'], r['row_candidate_count'], r['key']))
    elif prefer == 'excess':
        candidates.sort(key=lambda r: (-r['excess'], r['residual'], r['row_candidate_count'], r['key']))
    elif prefer == 'cheap':
        candidates.sort(key=lambda r: (r['seqcounter_cost_proxy'], r['residual'], -r['excess'], r['key']))
    else:
        raise ValueError(prefer)
    return candidates[:per_wave], candidates


def violations_summary(violations: Sequence[dict]) -> dict:
    by_res = defaultdict(int)
    by_excess = defaultdict(int)
    for v in violations:
        by_res[str(int(v['residual']))] += 1
        by_excess[str(int(v['excess']))] += 1
    return {
        'count': len(violations),
        'max_excess': max((int(v['excess']) for v in violations), default=0),
        'by_residual': dict(sorted(by_res.items(), key=lambda kv: int(kv[0]))),
        'by_excess': dict(sorted(by_excess.items(), key=lambda kv: int(kv[0]))),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed-run-dir', required=True)
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--waves', type=int, default=5)
    ap.add_argument('--promote-per-wave', type=int, default=8)
    ap.add_argument('--min-residual', type=int, default=2)
    ap.add_argument('--max-residual', type=int, default=15)
    ap.add_argument('--max-row-points', type=int, default=0)
    ap.add_argument('--prefer', choices=['low_residual', 'excess', 'cheap'], default='low_residual')
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

    fixed_prefix = [int(x) for x in base['fixed_prefix']]
    survivors = [int(x) for x in base['base']['survivors']]
    target = int(base['target'])
    base_clauses, var_map, top_id, base_meta = build_base_formula(base)
    learned_clauses, learned_meta = validate_learned_records(learned, lut, fixed_prefix, survivors, var_map)
    clauses: List[List[int]] = list(base_clauses) + learned_clauses
    seed_top = top_id
    seed_clause_count = len(clauses)
    promoted_keys = set()
    all_promotions = []
    wave_log = []
    status = 'MAX_WAVES'
    final_cnf = None
    drat_info = None
    final_support = None

    for wave in range(args.waves + 1):
        cnf_path = out_dir / f'wave{wave:03d}.cnf'
        write_cnf(clauses, top_id, cnf_path)
        sol = run_cadical(cnf_path, args.solve_time, with_drat=False)
        wi = {
            'wave': wave,
            'cnf': str(cnf_path),
            'cnf_sha256': sha256_file(cnf_path),
            'variables': top_id,
            'clauses': len(clauses),
            'cadical_exit': sol['exit'],
            'cadical_sec': round(sol['elapsed_sec'], 2),
            'promoted_rows_so_far': len(all_promotions),
        }
        if sol['unsat']:
            status = 'UNSAT'
            wi['result'] = 'UNSAT'
            wave_log.append(wi)
            final_cnf = cnf_path
            print(f'Wave {wave}: UNSAT with {len(all_promotions)} promotions, {len(clauses)} clauses')
            drat_sol = run_cadical(cnf_path, args.drat_solve_time, with_drat=True)
            trim = {'verified': False, 'reason': 'drat-producing solve did not return UNSAT'}
            if drat_sol['unsat'] and drat_sol.get('drat'):
                trim = run_drat_trim(cnf_path, pathlib.Path(drat_sol['drat']), args.drat_time)
            drat_info = {
                'drat_cadical_exit': drat_sol['exit'],
                'drat_cadical_sec': round(drat_sol['elapsed_sec'], 2),
                'drat': drat_sol.get('drat'),
                'drat_sha256': sha256_file(pathlib.Path(drat_sol['drat'])) if drat_sol.get('drat') else None,
                'drat_trim': trim,
            }
            break
        if not sol['sat'] or not sol['has_model']:
            status = 'SOLVER_UNKNOWN'
            wi['result'] = 'SOLVER_UNKNOWN'
            wi['cadical_log'] = sol.get('log')
            wave_log.append(wi)
            final_cnf = cnf_path
            print(f'Wave {wave}: solver unknown')
            break
        selected = parse_model_from_log(pathlib.Path(sol['log']), var_map)
        if selected is None or len(selected) != target:
            status = 'BAD_MODEL'
            wi['result'] = 'BAD_MODEL'
            wi['selected_size'] = None if selected is None else len(selected)
            wave_log.append(wi)
            final_cnf = cnf_path
            break
        t0 = time.time()
        violations = list(full_lut_violations(lut, fixed_prefix, selected, survivors))
        scan_sec = time.time() - t0
        wi.update({
            'result': 'SAT_SCANNED',
            'selected_size': len(selected),
            'support_size': len(set(fixed_prefix) | set(selected)),
            'selected': selected,
            'scan_sec': round(scan_sec, 2),
            'violations': violations_summary(violations),
            'violations_head': [
                {k: (list(vv)[:20] if isinstance(vv, tuple) else vv) for k, vv in v.items() if k != 'row_survivors'}
                for v in violations[:20]
            ],
        })
        print(f"Wave {wave}: SAT; violations={len(violations)} max_ex={wi['violations']['max_excess']} clauses={len(clauses)}")
        if not violations:
            status = 'LUT_ADMISSIBLE_SUPPORT_FOUND'
            final_support = sorted(set(fixed_prefix) | set(selected))
            wi['result'] = 'LUT_ADMISSIBLE'
            wave_log.append(wi)
            final_cnf = cnf_path
            break
        if wave == args.waves:
            wave_log.append(wi)
            final_cnf = cnf_path
            break
        selected_rows, ranking = select_violated_rows(
            violations, lut, fixed_prefix, survivors, promoted_keys,
            per_wave=args.promote_per_wave,
            min_residual=args.min_residual,
            max_residual=args.max_residual,
            max_row_points=args.max_row_points,
            prefer=args.prefer,
        )
        wi['selected_promotions'] = selected_rows
        wi['promotion_candidates_head'] = ranking[:50]
        if not selected_rows:
            status = 'NO_ELIGIBLE_PROMOTIONS'
            wave_log.append(wi)
            final_cnf = cnf_path
            break
        before_clause = len(clauses)
        clauses, top_id, new_promotions = add_promotions(clauses, var_map, top_id, lut, base, selected_rows)
        for rec in new_promotions:
            rec['promotion_wave'] = wave
            promoted_keys.add(int(rec['key']))
        all_promotions.extend(new_promotions)
        wi['new_promotion_count'] = len(new_promotions)
        wi['new_promotion_clause_count'] = len(clauses) - before_clause
        wi['top_after_promotions'] = top_id
        wave_log.append(wi)
        (out_dir / 'run_state.json').write_text(json.dumps({
            'schema': 'model_violation_promotion_state_v1',
            'status': 'RUNNING',
            'last_wave': wave,
            'promotions': len(all_promotions),
            'clauses': len(clauses),
            'variables': top_id,
            'last_violation_count': len(violations),
            'wave_log': wave_log,
        }, indent=2, sort_keys=True) + '\n')

    promoted_payload = {
        'schema': 'promoted_rows_v1',
        'seed_run_dir': str(seed_dir),
        'seed_summary_status': seed_summary.get('status'),
        'promotion_count_requested': {'waves': args.waves, 'promote_per_wave': args.promote_per_wave},
        'promotion_count_encoded': len(all_promotions),
        'promotions': all_promotions,
    }
    (out_dir / 'promoted_rows.json').write_text(json.dumps(promoted_payload, indent=2, sort_keys=True) + '\n')
    result = {
        'schema': 'model_violation_promotion_result_v1',
        'seed_run_dir': str(seed_dir),
        'seed_summary_status': seed_summary.get('status'),
        'branch': base.get('branch'),
        'idx': base.get('idx'),
        'fixed_prefix': fixed_prefix,
        'target': target,
        'survivor_count': len(survivors),
        'base_formula_meta': base_meta,
        'learned_meta': learned_meta,
        'seed_clause_count_before_promotion': seed_clause_count,
        'seed_top_before_promotion': seed_top,
        'promotion_count': len(all_promotions),
        'promotion_clause_count': sum(int(r['promotion_clause_count']) for r in all_promotions),
        'final_variables': top_id,
        'final_clauses': len(clauses),
        'status': status,
        'wave_log': wave_log,
        'cnf': str(final_cnf) if final_cnf else None,
        'cnf_sha256': sha256_file(final_cnf) if final_cnf else None,
        'promotion_metadata': str(out_dir / 'promoted_rows.json'),
    }
    if final_support is not None:
        result['support'] = final_support
        result['meaning'] = 'A-support satisfying Wang occupation rows, not a tensor decomposition.'
    if drat_info:
        result.update(drat_info)
    (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'status': status,
        'waves_logged': len(wave_log),
        'promotions': len(all_promotions),
        'promotion_clauses': result['promotion_clause_count'],
        'final_clauses': result['final_clauses'],
        'final_variables': result['final_variables'],
        'last_violations': wave_log[-1].get('violations', {}).get('count') if wave_log else None,
        'drat_verified': result.get('drat_trim', {}).get('verified'),
    }, sort_keys=True))


if __name__ == '__main__':
    main()
