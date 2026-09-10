#!/usr/bin/env python3
"""Witness-subset separation for an arbitrary fixed A-support prefix.

This is a small wrapper around the repaired analysis separator.  It is intended
for symmetry-marked rep2 subbranches: after fixing the adjacent pair {1,2}, mark
one additional selected point by an orbit representative, and ask whether the
remaining target completion is already excluded by Wang occupation rows.

The script builds the same residual-0/1 base graph and then delegates to
run_branch-like logic adapted locally so all usual provenance, learned clauses,
exact cardinality, and DRAT replay machinery are retained.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys
import time
from collections import defaultdict
from itertools import combinations
from math import comb
from typing import Dict, List, Sequence

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))

from graph_coloring_certificate import load_lut  # noqa:E402
from witness_subset_separation import (  # noqa:E402
    process_rep2, build_base_cnf, write_cnf, run_cadical, run_drat_trim,
    parse_model_from_log, full_lut_violations, choose_violation_order,
    append_jsonl, sha256_file,
)


def read_int_list(s: str) -> List[int]:
    return [int(x) for x in s.replace(';', ',').split(',') if x.strip()]


def source_counts(records: Sequence[dict]) -> dict:
    c = defaultdict(int)
    for r in records:
        c[r['source']] += 1
    return dict(sorted(c.items()))


def residual_counts(records: Sequence[dict]) -> dict:
    c = defaultdict(int)
    for r in records:
        c[int(r['residual'])] += 1
    return {str(k): v for k, v in sorted(c.items())}


def run_fixed_prefix(args, lut: Dict[int, int], prefix: Sequence[int], out_dir: pathlib.Path) -> dict:
    prefix = [int(x) for x in prefix]
    candidates = sorted(m for m in range(1, 512) if m not in set(prefix))
    info = process_rep2(lut, prefix, candidates)
    meta = {
        'branch': 'fixed_prefix_projective_support',
        'prefix_label': args.prefix_label,
        'fixed_prefix': prefix,
        'k': len(prefix),
        'candidate_kind': 'all_projective_points_except_prefix',
    }
    out_dir.mkdir(parents=True, exist_ok=True)
    if info.get('impossible_rows'):
        result = {**meta, 'status': 'FIXED_PREFIX_VIOLATES', 'violating_row': info['impossible_rows'][0]}
        (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
        return result

    base_clauses, var_map, top_id, base_meta = build_base_cnf(info)
    survivors = [int(x) for x in info['survivors']]
    target = int(info['target'])
    base_payload = {
        'schema': 'fixed_prefix_witness_base_v1',
        **meta,
        'rank_budget': 20,
        'candidate_count': len(candidates),
        'candidate_universe': candidates,
        'survivor_count': len(survivors),
        'target': target,
        'direct_clause_threshold': args.direct_clause_threshold,
        'max_witness_clauses_per_round': args.max_witness_clauses_per_round,
        'max_new_clauses_per_round': args.max_new_clauses_per_round,
        'base': base_meta,
    }
    (out_dir / 'base_metadata.json').write_text(json.dumps(base_payload, indent=2, sort_keys=True) + '\n')

    clauses = list(base_clauses)
    known_clause_points = {tuple(sorted(edge['points'])) for edge in base_meta['base_edges']}
    learned_path = out_dir / 'learned_clauses.jsonl'
    if learned_path.exists():
        learned_path.unlink()
    round_log = []
    learned_count = 0
    learned_by_source = defaultdict(int)
    learned_by_residual = defaultdict(int)

    for rnd in range(args.max_rounds):
        cnf_path = out_dir / f'round{rnd:03d}.cnf'
        write_cnf(clauses, top_id, cnf_path)
        sol = run_cadical(cnf_path, args.solve_time, with_drat=False)
        ri = {'round': rnd, 'cnf': str(cnf_path), 'clauses': len(clauses), 'variables': top_id,
              'cadical_exit': sol['exit'], 'cadical_sec': round(sol['elapsed_sec'], 2)}
        if sol['unsat']:
            ri['result'] = 'UNSAT'
            round_log.append(ri)
            final_cnf = out_dir / 'final.cnf'
            write_cnf(clauses, top_id, final_cnf)
            drat_sol = run_cadical(final_cnf, args.solve_time * args.drat_solve_multiplier, with_drat=True)
            trim = {'verified': False, 'elapsed_sec': 0, 'log': None}
            if drat_sol['unsat'] and drat_sol.get('drat'):
                trim = run_drat_trim(final_cnf, pathlib.Path(drat_sol['drat']), args.drat_time)
            result = {
                'schema': 'fixed_prefix_witness_result_v1', **meta,
                'status': 'UNSAT', 'rounds': rnd + 1, 'survivor_count': len(survivors),
                'target': target, 'final_clauses': len(clauses), 'final_variables': top_id,
                'learned_clause_count': learned_count,
                'learned_by_source': dict(sorted(learned_by_source.items())),
                'learned_by_residual': {str(k): v for k, v in sorted(learned_by_residual.items())},
                'round_log': round_log, 'final_cnf': str(final_cnf),
                'final_cnf_sha256': sha256_file(final_cnf),
                'drat_cadical_exit': drat_sol['exit'],
                'drat_cadical_sec': round(drat_sol['elapsed_sec'], 2),
                'drat': drat_sol.get('drat'),
                'drat_sha256': sha256_file(pathlib.Path(drat_sol['drat'])) if drat_sol.get('drat') else None,
                'drat_trim': trim,
                'learned_clause_provenance': str(learned_path),
                'learned_clause_provenance_sha256': sha256_file(learned_path),
                'base_metadata': str(out_dir / 'base_metadata.json'),
            }
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
            print(json.dumps({'status': result['status'], 'rounds': result['rounds'], 'drat_verified': trim.get('verified'), 'final_clauses': len(clauses)}, sort_keys=True))
            return result
        if not sol['sat'] or not sol['has_model']:
            ri['result'] = 'SOLVER_UNKNOWN_OR_NO_MODEL'
            round_log.append(ri)
            result = {
                'schema': 'fixed_prefix_witness_result_v1', **meta,
                'status': 'SOLVER_UNKNOWN', 'rounds': rnd + 1, 'survivor_count': len(survivors),
                'target': target, 'round_log': round_log, 'learned_clause_count': learned_count,
                'learned_clause_provenance': str(learned_path), 'base_metadata': str(out_dir / 'base_metadata.json'),
            }
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
            print(json.dumps({'status': result['status'], 'rounds': result['rounds']}, sort_keys=True))
            return result
        selected = parse_model_from_log(pathlib.Path(sol['log']), var_map)
        if selected is None or len(selected) != target:
            ri['result'] = f'BAD_MODEL_size_{0 if selected is None else len(selected)}'
            round_log.append(ri)
            result = {'schema': 'fixed_prefix_witness_result_v1', **meta, 'status': 'BAD_MODEL',
                      'rounds': rnd + 1, 'selected_size': 0 if selected is None else len(selected),
                      'target': target, 'round_log': round_log}
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
            return result
        violations = list(full_lut_violations(lut, prefix, selected, survivors))
        violations.sort(key=choose_violation_order)
        ri['model_size'] = len(selected)
        ri['support_size'] = len(set(prefix) | set(selected))
        ri['lut_violations'] = len(violations)
        ri['max_excess'] = max((int(v['excess']) for v in violations), default=0)
        if not violations:
            support = sorted(set(prefix) | set(selected))
            ri['result'] = 'LUT_ADMISSIBLE'
            round_log.append(ri)
            result = {'schema': 'fixed_prefix_witness_result_v1', **meta,
                      'status': 'LUT_ADMISSIBLE_SUPPORT_FOUND', 'support': support,
                      'support_size': len(support), 'selected': selected, 'rounds': rnd + 1,
                      'round_log': round_log, 'learned_clause_count': learned_count,
                      'learned_clause_provenance': str(learned_path), 'base_metadata': str(out_dir / 'base_metadata.json'),
                      'meaning': 'A-support satisfies Wang occupation rows; not a tensor decomposition.'}
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
            print(json.dumps({'status': result['status'], 'rounds': result['rounds'], 'support_size': len(support)}, sort_keys=True))
            return result

        new_records = []
        new_clause_count = 0
        skipped_duplicate = 0
        skipped_budget = 0
        cheap_full_rows = 0
        witness_rows = 0
        for v in violations:
            residual = int(v['residual'])
            if residual < 0:
                raise RuntimeError('negative residual inside fixed-prefix learning loop')
            row_points = tuple(int(x) for x in v['row_survivors'])
            row_lits = [var_map[p] for p in row_points if p in var_map]
            full_clause_count = comb(len(row_lits), residual + 1) if residual >= 0 and len(row_lits) > residual else 0
            can_full = 0 < full_clause_count <= args.direct_clause_threshold
            candidate_clause_records = []
            source = 'full_row_direct' if can_full else 'witness_subset'
            if can_full:
                cheap_full_rows += 1
                for pts in combinations(row_points, residual + 1):
                    pts = tuple(int(p) for p in pts)
                    if pts in known_clause_points:
                        skipped_duplicate += 1
                        continue
                    candidate_clause_records.append({
                        'round': rnd, 'source': source, 'key': int(v['key']), 'lb': int(v['lb']),
                        'cap': int(v['cap']), 'fixed_count': int(v['fixed_count']), 'residual': residual,
                        'row_candidate_count': len(row_points), 'full_direct_clause_count_for_row': full_clause_count,
                        'selection_count': int(v['selection_count']), 'excess': int(v['excess']),
                        'points': list(pts), 'lits': [-var_map[p] for p in pts],
                    })
            else:
                if args.max_witness_clauses_per_round is not None and witness_rows >= args.max_witness_clauses_per_round:
                    skipped_budget += 1
                    continue
                sel_in_row = sorted(int(p) for p in v['selected_in_row'])
                multi_count = comb(len(sel_in_row), residual + 1)
                for pts in combinations(sel_in_row, residual + 1):
                    pts = tuple(int(p) for p in pts)
                    if pts in known_clause_points:
                        skipped_duplicate += 1
                        continue
                    candidate_clause_records.append({
                        'round': rnd, 'source': source, 'key': int(v['key']), 'lb': int(v['lb']),
                        'cap': int(v['cap']), 'fixed_count': int(v['fixed_count']), 'residual': residual,
                        'row_candidate_count': len(row_points), 'full_direct_clause_count_for_row': full_clause_count,
                        'selection_count': int(v['selection_count']), 'excess': int(v['excess']),
                        'multi_witness_total': multi_count,
                        'points': list(pts), 'lits': [-var_map[p] for p in pts],
                    })
                witness_rows += 1
            for rec in candidate_clause_records:
                if args.max_new_clauses_per_round is not None and new_clause_count >= args.max_new_clauses_per_round:
                    skipped_budget += 1
                    break
                pts_tuple = tuple(sorted(int(p) for p in rec['points']))
                if pts_tuple in known_clause_points:
                    skipped_duplicate += 1
                    continue
                known_clause_points.add(pts_tuple)
                clauses.append([int(x) for x in rec['lits']])
                new_records.append(rec)
                new_clause_count += 1
                learned_by_source[rec['source']] += 1
                learned_by_residual[int(rec['residual'])] += 1
            if args.max_new_clauses_per_round is not None and new_clause_count >= args.max_new_clauses_per_round:
                break
        append_jsonl(learned_path, new_records)
        learned_count += len(new_records)
        ri['new_clauses'] = len(new_records)
        ri['new_by_source'] = source_counts(new_records)
        ri['new_by_residual'] = residual_counts(new_records)
        ri['cheap_full_rows_used'] = cheap_full_rows
        ri['witness_rows_used'] = witness_rows
        ri['skipped_duplicate'] = skipped_duplicate
        ri['skipped_budget'] = skipped_budget
        ri['result'] = 'SAT_SEPARATED'
        round_log.append(ri)
        print(f'  Rnd {rnd}: viol={len(violations)} max_excess={ri["max_excess"]} new={len(new_records)} full_rows={cheap_full_rows} witness={witness_rows} clauses={len(clauses)} sat_sec={sol["elapsed_sec"]:.1f}')
        (out_dir / 'run_state.json').write_text(json.dumps({
            'schema': 'fixed_prefix_witness_state_v1', **meta, 'status': 'RUNNING',
            'last_round': rnd, 'clauses': len(clauses), 'variables': top_id,
            'learned_clause_count': learned_count, 'round_log': round_log,
            'learned_clause_provenance': str(learned_path),
        }, indent=2, sort_keys=True) + '\n')
        if not new_records:
            break

    current_cnf = out_dir / 'current.cnf'
    write_cnf(clauses, top_id, current_cnf)
    result = {
        'schema': 'fixed_prefix_witness_result_v1', **meta,
        'status': 'MAX_ROUNDS', 'rounds': args.max_rounds, 'survivor_count': len(survivors),
        'target': target, 'final_clauses': len(clauses), 'final_variables': top_id,
        'learned_clause_count': learned_count,
        'learned_by_source': dict(sorted(learned_by_source.items())),
        'learned_by_residual': {str(k): v for k, v in sorted(learned_by_residual.items())},
        'round_log': round_log, 'learned_clause_provenance': str(learned_path),
        'learned_clause_provenance_sha256': sha256_file(learned_path),
        'current_cnf': str(current_cnf), 'current_cnf_sha256': sha256_file(current_cnf),
        'base_metadata': str(out_dir / 'base_metadata.json'),
    }
    (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': result['status'], 'rounds': result['rounds'], 'final_clauses': len(clauses), 'learned_clause_count': learned_count}, sort_keys=True))
    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--prefix', required=True, help='comma-separated nonzero projective A-points')
    ap.add_argument('--prefix-label', default='fixed_prefix')
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--max-rounds', type=int, default=20)
    ap.add_argument('--solve-time', type=int, default=300)
    ap.add_argument('--drat-time', type=int, default=900)
    ap.add_argument('--drat-solve-multiplier', type=int, default=5)
    ap.add_argument('--direct-clause-threshold', type=int, default=20)
    ap.add_argument('--max-witness-clauses-per-round', type=int, default=5000)
    ap.add_argument('--max-new-clauses-per-round', type=int, default=20000)
    args = ap.parse_args()
    prefix = read_int_list(args.prefix)
    if len(prefix) != len(set(prefix)):
        raise SystemExit('prefix has duplicate points')
    print(f'Loading LUT from {args.lut}...')
    lut = load_lut(pathlib.Path(args.lut))
    print(f'  {len(lut):,} rows')
    run_fixed_prefix(args, lut, prefix, pathlib.Path(args.out_dir))


if __name__ == '__main__':
    main()
