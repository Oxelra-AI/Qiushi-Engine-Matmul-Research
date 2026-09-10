#!/usr/bin/env python3
"""Continue rep2 witness-subset separation with transported ruling-line clauses.

This exploratory/proof-engineering script starts from a validated rep2 learned
JSONL seed, adds the 98 ruling-line clauses transported from the verified
[1,2,3] local exclusion, then performs bounded model-driven Wang-row separation.

It is deliberately separate from the analysis proof verifier: learned Wang clauses
remain recorded with ordinary row provenance, while ruling-line clauses are a
separate derived-geometry input whose proof provenance must be bound separately
before any UNSAT result is promoted to a proof object.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import sys
import time
from collections import defaultdict
from itertools import combinations
from math import comb
from typing import Dict, List, Sequence, Set, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))

from witness_subset_separation import (  # noqa:E402
    load_lut,
    process_rep2,
    build_base_cnf,
    validate_and_reencode_learned_record,
    write_cnf,
    run_cadical,
    parse_model_from_log,
    full_lut_violations,
    choose_violation_order,
    append_jsonl,
    sha256_file,
)
from ruling_line_transport import all_ruling_triples, simplify_ruling  # noqa:E402


def normalize_points_clause(rec_or_clause, inv_var: Dict[int, int] | None = None) -> Tuple[int, ...]:
    if isinstance(rec_or_clause, dict):
        return tuple(sorted(int(p) for p in rec_or_clause['points']))
    if inv_var is None:
        raise ValueError('inv_var needed for DIMACS clause')
    pts = []
    for lit in rec_or_clause:
        lit = int(lit)
        if lit < 0 and -lit in inv_var:
            pts.append(inv_var[-lit])
    return tuple(sorted(pts))


def load_seed_records(seed_path: pathlib.Path, lut: Dict[int, int], fixed_prefix: Sequence[int],
                      survivors: Sequence[int], var_map: Dict[int, int]) -> List[dict]:
    out: List[dict] = []
    seen: Set[Tuple[int, ...]] = set()
    with seed_path.open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            raw = json.loads(line)
            rec = validate_and_reencode_learned_record(raw, lut, fixed_prefix, survivors, var_map, seed_path)
            pts = tuple(sorted(int(p) for p in rec['points']))
            if pts in seen:
                continue
            seen.add(pts)
            out.append(rec)
    return out


def ruling_clauses(prefix: Sequence[int], var_map: Dict[int, int]) -> Tuple[List[List[int]], List[dict], dict]:
    rc = simplify_ruling(all_ruling_triples(), set(int(x) for x in prefix))
    clauses: List[List[int]] = []
    records: List[dict] = []
    for kind, seq in [('unit', rc['unit']), ('binary', rc['binary']), ('ternary', rc['ternary'])]:
        for item in seq:
            pts = [int(item)] if kind == 'unit' else [int(x) for x in item]
            if all(p in var_map for p in pts):
                cl = [-var_map[p] for p in pts]
                clauses.append(cl)
                records.append({'source': 'transported_ruling_line', 'kind': kind, 'points': pts, 'lits': cl})
    meta = {
        'simplified_counts': {
            'unit': len(rc['unit']), 'binary': len(rc['binary']), 'ternary': len(rc['ternary']),
            'contradictions': int(rc['contradictions']),
        },
        'encoded_clause_count': len(clauses),
        'encoded_by_kind': {k: sum(1 for r in records if r['kind'] == k) for k in ['unit', 'binary', 'ternary']},
        'unit_points': rc['unit'],
        'binary_pairs': [list(x) for x in rc['binary']],
        'ternary_count': len(rc['ternary']),
        'proof_source': 'transport of the analysis fixed-prefix [1,2,3] Wang/DRAT exclusion under Segre ruling-line equivariance; see independent-verification-record and rep2_rep003_promotion/lowres_12w8/strict_verification.json',
    }
    return clauses, records, meta


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed-learned-jsonl', required=True)
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--max-rounds', type=int, default=10)
    ap.add_argument('--solve-time', type=int, default=300)
    ap.add_argument('--direct-clause-threshold', type=int, default=20)
    ap.add_argument('--max-witness-clauses-per-round', type=int, default=5000)
    ap.add_argument('--max-new-clauses-per-round', type=int, default=20000)
    args = ap.parse_args()

    out_dir = pathlib.Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    seed_path = pathlib.Path(args.seed_learned_jsonl)

    print(f'Loading LUT {args.lut}...')
    lut = load_lut(pathlib.Path(args.lut))
    print(f'  rows: {len(lut):,}')
    fixed_prefix = [1, 2]
    candidates = [p for p in range(1, 512) if p not in set(fixed_prefix)]
    info = process_rep2(lut, fixed_prefix, candidates)
    base_clauses, var_map, top_id, base_meta = build_base_cnf(info)
    survivors = [int(x) for x in info['survivors']]
    inv_var = {v: p for p, v in var_map.items()}

    seed_records = load_seed_records(seed_path, lut, fixed_prefix, survivors, var_map)
    seed_clauses = [[int(x) for x in rec['lits']] for rec in seed_records]
    ruling_cls, ruling_records, ruling_meta = ruling_clauses(fixed_prefix, var_map)

    known_clause_points: Set[Tuple[int, ...]] = set()
    for rec in seed_records:
        known_clause_points.add(tuple(sorted(int(p) for p in rec['points'])))
    existing_dimacs = {tuple(sorted(int(x) for x in cl)) for cl in base_clauses + seed_clauses}
    new_ruling_clauses: List[List[int]] = []
    new_ruling_records: List[dict] = []
    for cl, rec in zip(ruling_cls, ruling_records):
        key = tuple(sorted(int(x) for x in cl))
        pts = tuple(sorted(int(p) for p in rec['points']))
        if key in existing_dimacs:
            continue
        new_ruling_clauses.append(cl)
        new_ruling_records.append(rec)
        known_clause_points.add(pts)

    clauses: List[List[int]] = list(base_clauses) + list(seed_clauses) + list(new_ruling_clauses)
    learned_path = out_dir / 'learned_clauses.jsonl'
    append_jsonl(learned_path, seed_records)
    ruling_path = out_dir / 'ruling_clauses.json'
    ruling_path.write_text(json.dumps({'meta': ruling_meta, 'records': new_ruling_records}, indent=2, sort_keys=True) + '\n')
    shutil.copyfile(seed_path, out_dir / 'seed_input_learned_clauses.jsonl')

    base_payload = {
        'branch': 'rep2_adjacent_pair_with_ruling_transport',
        'fixed_prefix': fixed_prefix,
        'target': int(info['target']),
        'candidate_kind': 'all_projective_points_except_prefix',
        'survivor_count': len(survivors),
        'base_meta': base_meta,
        'base_row_counts': {str(k): int(v) for k, v in info['row_counts'].items()},
        'seed_input': str(seed_path),
        'seed_input_sha256': sha256_file(seed_path),
        'seed_imported_records': len(seed_records),
        'ruling_meta': ruling_meta,
        'ruling_new_clause_count': len(new_ruling_clauses),
    }
    (out_dir / 'base_metadata.json').write_text(json.dumps(base_payload, indent=2, sort_keys=True) + '\n')

    learned_count = len(seed_records)
    learned_by_source = defaultdict(int)
    learned_by_residual = defaultdict(int)
    for rec in seed_records:
        learned_by_source[rec.get('source', 'seeded')] += 1
        learned_by_residual[int(rec['residual'])] += 1

    round_log = []
    for rnd in range(args.max_rounds):
        cnf_path = out_dir / f'round{rnd:03d}.cnf'
        write_cnf(clauses, top_id, cnf_path)
        sol = run_cadical(cnf_path, args.solve_time, with_drat=False)
        ri = {'round': rnd, 'cnf': str(cnf_path), 'clauses': len(clauses), 'variables': top_id,
              'cadical_exit': sol['exit'], 'cadical_sec': round(sol['elapsed_sec'], 3)}
        if sol.get('unsat'):
            ri['result'] = 'UNSAT_NO_DRAT_YET'
            round_log.append(ri)
            final_cnf = out_dir / 'final.cnf'
            write_cnf(clauses, top_id, final_cnf)
            status = 'UNSAT'
            break
        if not sol.get('sat') or not sol.get('has_model'):
            ri['result'] = 'SOLVER_UNKNOWN_OR_NO_MODEL'
            round_log.append(ri)
            final_cnf = out_dir / 'current.cnf'
            write_cnf(clauses, top_id, final_cnf)
            status = 'SOLVER_UNKNOWN'
            break
        selected = parse_model_from_log(pathlib.Path(sol['log']), var_map)
        if selected is None or len(selected) != int(info['target']):
            ri['result'] = f'BAD_MODEL_size_{0 if selected is None else len(selected)}'
            round_log.append(ri)
            final_cnf = out_dir / 'current.cnf'
            write_cnf(clauses, top_id, final_cnf)
            status = 'BAD_MODEL'
            break
        violations = list(full_lut_violations(lut, fixed_prefix, selected, survivors))
        violations.sort(key=choose_violation_order)
        ri['model_size'] = len(selected)
        ri['support_size'] = len(set(fixed_prefix) | set(selected))
        ri['lut_violations'] = len(violations)
        ri['max_excess'] = max((int(v['excess']) for v in violations), default=0)
        if not violations:
            ri['result'] = 'LUT_ADMISSIBLE'
            round_log.append(ri)
            (out_dir / 'lut_admissible_support.json').write_text(json.dumps(sorted(set(fixed_prefix) | set(selected)), indent=2) + '\n')
            final_cnf = out_dir / 'current.cnf'
            write_cnf(clauses, top_id, final_cnf)
            status = 'LUT_ADMISSIBLE_SUPPORT_FOUND'
            break

        new_records: List[dict] = []
        new_clause_count = 0
        skipped_duplicate = 0
        skipped_budget = 0
        cheap_full_rows = 0
        witness_rows = 0
        for v in violations:
            residual = int(v['residual'])
            if residual < 0:
                ri['result'] = 'INTERNAL_FIXED_PREFIX_VIOLATES'
                break
            if len(v['selected_in_row']) <= residual:
                continue
            row_points = tuple(int(x) for x in v['row_survivors'])
            row_lits = [var_map[p] for p in row_points if p in var_map]
            full_clause_count = comb(len(row_lits), residual + 1) if residual >= 0 and len(row_lits) > residual else 0
            can_full = 0 < full_clause_count <= args.direct_clause_threshold
            candidate_records = []
            source = 'full_row_direct' if can_full else 'witness_subset'
            if can_full:
                cheap_full_rows += 1
                iter_pts = combinations(row_points, residual + 1)
            else:
                if witness_rows >= args.max_witness_clauses_per_round:
                    skipped_budget += 1
                    continue
                sel_in_row = sorted(int(p) for p in v['selected_in_row'])
                iter_pts = combinations(sel_in_row, residual + 1)
                witness_rows += 1
            for pts in iter_pts:
                pts = tuple(int(p) for p in pts)
                if pts in known_clause_points:
                    skipped_duplicate += 1
                    continue
                lits = [-var_map[p] for p in pts]
                candidate_records.append({
                    'round': rnd,
                    'source': source,
                    'key': int(v['key']),
                    'lb': int(v['lb']),
                    'cap': int(v['cap']),
                    'fixed_count': int(v['fixed_count']),
                    'residual': residual,
                    'row_candidate_count': len(row_points),
                    'full_direct_clause_count_for_row': full_clause_count,
                    'selection_count': int(v['selection_count']),
                    'excess': int(v['excess']),
                    'points': list(pts),
                    'lits': lits,
                })
            for rec in candidate_records:
                if new_clause_count >= args.max_new_clauses_per_round:
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
            if new_clause_count >= args.max_new_clauses_per_round:
                break
        else:
            # no internal break
            pass
        append_jsonl(learned_path, new_records)
        learned_count += len(new_records)
        ri['new_clauses'] = len(new_records)
        ri['cheap_full_rows_used'] = cheap_full_rows
        ri['witness_rows_used'] = witness_rows
        ri['skipped_duplicate'] = skipped_duplicate
        ri['skipped_budget'] = skipped_budget
        by_res = defaultdict(int)
        by_src = defaultdict(int)
        for rec in new_records:
            by_res[int(rec['residual'])] += 1
            by_src[rec['source']] += 1
        ri['new_by_residual'] = {str(k): int(v) for k, v in sorted(by_res.items())}
        ri['new_by_source'] = {str(k): int(v) for k, v in sorted(by_src.items())}
        ri.setdefault('result', 'SAT_SEPARATED')
        round_log.append(ri)
        print(f"Rnd {rnd}: viol={ri['lut_violations']} max_excess={ri['max_excess']} new={len(new_records)} clauses={len(clauses)}")
        if not new_records:
            final_cnf = out_dir / 'current.cnf'
            write_cnf(clauses, top_id, final_cnf)
            status = 'NO_NEW_CLAUSES'
            break
    else:
        final_cnf = out_dir / 'current.cnf'
        write_cnf(clauses, top_id, final_cnf)
        status = 'MAX_ROUNDS'

    result = {
        'schema': 'rep2_ruling_witness_continue_v1',
        'status': status,
        'fixed_prefix': fixed_prefix,
        'target': int(info['target']),
        'survivor_count': len(survivors),
        'base_metadata': str(out_dir / 'base_metadata.json'),
        'seed_learned_jsonl': str(seed_path),
        'seeded_clause_count': len(seed_records),
        'ruling_clause_path': str(ruling_path),
        'ruling_new_clause_count': len(new_ruling_clauses),
        'learned_clause_count': learned_count,
        'learned_clause_provenance': str(learned_path),
        'learned_clause_provenance_sha256': sha256_file(learned_path),
        'final_cnf': str(final_cnf),
        'final_cnf_sha256': sha256_file(final_cnf),
        'final_clauses': len(clauses),
        'final_variables': top_id,
        'learned_by_source': dict(sorted(learned_by_source.items())),
        'learned_by_residual': {str(k): int(v) for k, v in sorted(learned_by_residual.items())},
        'round_log': round_log,
        'meaning': 'Bounded rep2 adjacent-pair separator with transported ruling-line clauses added. Nonterminal status is not a support exclusion; UNSAT would still require DRAT replay and separate verification of ruling-line provenance.',
    }
    (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'final_clauses', 'learned_clause_count', 'ruling_new_clause_count']}, sort_keys=True))


if __name__ == '__main__':
    main()
