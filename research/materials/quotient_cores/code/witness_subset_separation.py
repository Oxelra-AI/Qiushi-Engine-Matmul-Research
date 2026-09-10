#!/usr/bin/env python3
r"""Witness-subset iterative separation for Wang-support branches over F2.

This script strengthens the analysis separator.  Cheap violated Wang rows are still
encoded by all direct at-most clauses.  For a violated row whose full direct
encoding is too large, the script learns one valid clause from the current model:
if the row has residual capacity r and the current selected candidate set contains
more than r points in that row, any deterministic (r+1)-subset of those selected
points is forbidden in every completion.  The learned clause is therefore a
mathematical consequence of the single Wang row, but avoids expanding all
binomially many subsets of the row.

Every learned clause is appended to learned_clauses.jsonl with its Wang row key,
lower bound, fixed-prefix occupancy, residual capacity, candidate-row size, point
subset, and DIMACS literals.  This file is part of the proof object: a DRAT proof
only certifies the generated CNF, while the JSONL provenance certifies why each
learned clause belongs to the Wang occupation system.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import subprocess
import sys
import time
from collections import defaultdict
from itertools import combinations
from math import comb
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from wang_capacity_lazy import unpack_basis, subspace_points_from_basis  # noqa:E402
from graph_coloring_certificate import (  # noqa:E402
    rank1_points, load_lut, iter_strata, process_stratum,
    make_pivot_dict, in_span_piv,
)


def sha256_file(path: pathlib.Path) -> Optional[str]:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------------------
# Cardinality and CNF helpers


def atmost_direct(lits: Sequence[int], bound: int) -> List[List[int]]:
    lits = list(lits)
    if bound < 0:
        return [[]]
    if bound >= len(lits):
        return []
    if bound == 0:
        return [[-x] for x in lits]
    return [[-x for x in subset] for subset in combinations(lits, bound + 1)]


def atleast_pysat(lits: Sequence[int], bound: int, top_id: int) -> Tuple[List[List[int]], int]:
    from pysat.card import CardEnc, EncType
    lits = list(lits)
    if bound <= 0:
        return [], top_id
    if bound > len(lits):
        return [[]], top_id
    enc = CardEnc.atleast(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
    return [list(cl) for cl in enc.clauses], int(enc.nv)


def atmost_pysat(lits: Sequence[int], bound: int, top_id: int) -> Tuple[List[List[int]], int]:
    from pysat.card import CardEnc, EncType
    lits = list(lits)
    if bound >= len(lits):
        return [], top_id
    if bound < 0:
        return [[]], top_id
    if bound == 0:
        return [[-x] for x in lits], top_id
    enc = CardEnc.atmost(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
    return [list(cl) for cl in enc.clauses], int(enc.nv)


def write_cnf(clauses: Sequence[Sequence[int]], top_id: int, path: pathlib.Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('w') as f:
        f.write(f'p cnf {top_id} {len(clauses)}\n')
        for cl in clauses:
            f.write(' '.join(map(str, cl)) + ' 0\n')


def read_cnf_clauses(path: pathlib.Path) -> Tuple[int, List[List[int]]]:
    top = 0
    clauses: List[List[int]] = []
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c'):
                continue
            if line.startswith('p '):
                parts = line.split()
                top = int(parts[2])
                continue
            xs = [int(x) for x in line.split()]
            if xs and xs[-1] == 0:
                xs = xs[:-1]
            clauses.append(xs)
    return top, clauses


# ---------------------------------------------------------------------------
# Branch construction


def process_rep2(lut: Dict[int, int], prefix: Sequence[int], candidates: Sequence[int]) -> dict:
    """Residual-0/1 graph for the adjacent-pair branch with arbitrary candidates."""
    cand_set = set(int(x) for x in candidates)
    prefix = [int(x) for x in prefix]
    k = len(prefix)
    target = 20 - k
    lb_min = max(20 - k - 1, 0)

    vertex_key: Dict[int, int] = {}
    edge_key: Dict[Tuple[int, int], int] = {}
    impossible = []
    row_counts = {'filtered': 0, 'res_neg': 0, 'res0': 0, 'res1': 0}

    for key, lb in lut.items():
        lb = int(lb)
        if lb < lb_min:
            continue
        cap = 20 - lb
        if cap - 1 > k:
            continue
        basis = unpack_basis(int(key))
        piv = make_pivot_dict(basis)
        cnt = sum(1 for p in prefix if in_span_piv(piv, int(p)))
        residual = cap - cnt
        if residual > 1:
            continue
        row_counts['filtered'] += 1
        if residual < 0:
            row_counts['res_neg'] += 1
            impossible.append({'key': int(key), 'lb': lb, 'cap': cap, 'fixed_count': cnt})
            continue
        pts = [int(x) for x in subspace_points_from_basis(basis) if int(x) in cand_set]
        if residual == 0:
            row_counts['res0'] += 1
            for h in pts:
                vertex_key.setdefault(h, int(key))
        elif residual == 1:
            row_counts['res1'] += 1
            for i, a in enumerate(pts):
                for b in pts[i + 1:]:
                    x, y = (int(a), int(b)) if int(a) < int(b) else (int(b), int(a))
                    edge_key.setdefault((x, y), int(key))

    survivors = [int(c) for c in candidates if int(c) not in vertex_key]
    ss = set(survivors)
    survivor_edges = {p: key for p, key in edge_key.items() if p[0] in ss and p[1] in ss}
    return {
        'target': target,
        'impossible_rows': impossible,
        'vertex_key': vertex_key,
        'survivors': survivors,
        'edge_key': survivor_edges,
        'row_counts': row_counts,
    }


def branch_info(args, lut: Dict[int, int], stratum: Optional[dict] = None) -> Tuple[List[int], List[int], dict, dict]:
    """Return fixed prefix, candidate universe, process info, and branch metadata."""
    if args.branch == 'matching':
        assert stratum is not None
        prefix = [int(x) for x in stratum['canonical']]
        r1 = rank1_points()
        hr_list = sorted(m for m in range(1, 512) if m not in r1)
        hr_set = set(hr_list)
        info = process_stratum(lut, prefix, hr_set, hr_list)
        meta = {
            'branch': 'matching',
            'idx': int(stratum['_idx']),
            'k': int(stratum['k']),
            'orbit_size': int(stratum.get('orbit_image_count', stratum.get('enumerated_members', 0))),
            'candidate_kind': 'higher_rank_only',
        }
        return prefix, hr_list, info, meta

    if args.branch == 'rep2':
        prefix = [1, 2]
        candidates = sorted(m for m in range(1, 512) if m not in set(prefix))
        info = process_rep2(lut, prefix, candidates)
        meta = {
            'branch': 'rep2_adjacent_pair',
            'idx': None,
            'k': len(prefix),
            'orbit_size': None,
            'candidate_kind': 'all_projective_points_except_prefix',
        }
        return prefix, candidates, info, meta

    raise ValueError(args.branch)


def build_base_cnf(info: dict) -> Tuple[List[List[int]], Dict[int, int], int, dict]:
    survivors = [int(x) for x in info['survivors']]
    target = int(info['target'])
    var_map = {h: i + 1 for i, h in enumerate(survivors)}
    top_id = len(var_map)
    clauses: List[List[int]] = []

    base_edges = []
    for (a, b), row_key in sorted(info['edge_key'].items()):
        if a in var_map and b in var_map:
            cl = [-var_map[a], -var_map[b]]
            clauses.append(cl)
            base_edges.append({'points': [int(a), int(b)], 'lits': cl, 'key': int(row_key)})

    card_start_top = top_id
    al, top_id = atleast_pysat(list(var_map.values()), target, top_id)
    clauses.extend(al)
    after_atleast_top = top_id
    am, top_id = atmost_pysat(list(var_map.values()), target, top_id)
    clauses.extend(am)

    base_meta = {
        'survivors': survivors,
        'target': target,
        'initial_variables': len(var_map),
        'final_base_variables': top_id,
        'base_edge_clause_count': len(base_edges),
        'cardinality_atleast_clause_count': len(al),
        'cardinality_atmost_clause_count': len(am),
        'cardinality_top_ids': {
            'candidate_top': card_start_top,
            'after_atleast': after_atleast_top,
            'after_atmost': top_id,
        },
        'base_edges': base_edges,
        'vertex_exclusions': [[int(p), int(k)] for p, k in sorted(info.get('vertex_key', {}).items())],
        'row_counts': info.get('row_counts', {}),
    }
    return clauses, var_map, top_id, base_meta


# ---------------------------------------------------------------------------
# Solving and row scanning


def run_cadical(cnf_path: pathlib.Path, timeout: int, with_drat: bool = False) -> dict:
    drat_path = cnf_path.with_suffix('.drat') if with_drat else None
    log_path = cnf_path.with_suffix('.cadical.log')
    cmd = ['cadical']
    if timeout > 0:
        cmd += ['-t', str(timeout)]
    cmd.append(str(cnf_path))
    if with_drat:
        cmd.append(str(drat_path))
    t0 = time.time()
    with log_path.open('w') as f:
        proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, text=True)
    elapsed = time.time() - t0
    text = log_path.read_text(errors='ignore')
    # Prefer return code; the text fallback helps if a wrapper changes codes.
    rc = proc.returncode
    if rc not in (10, 20):
        if 's UNSATISFIABLE' in text:
            rc = 20
        elif 's SATISFIABLE' in text:
            rc = 10
    return {
        'exit': rc,
        'elapsed_sec': elapsed,
        'unsat': rc == 20,
        'sat': rc == 10,
        'log': str(log_path),
        'drat': str(drat_path) if drat_path else None,
        'has_model': rc == 10 and any(line.startswith('v ') for line in text.splitlines()),
    }


def run_drat_trim(cnf_path: pathlib.Path, drat_path: pathlib.Path, timeout: int) -> dict:
    log_path = cnf_path.with_suffix('.drat_trim.log')
    t0 = time.time()
    try:
        with log_path.open('w') as f:
            proc = subprocess.run(['drat-trim', str(cnf_path), str(drat_path)],
                                  stdout=f, stderr=subprocess.STDOUT, text=True,
                                  timeout=timeout)
        elapsed = time.time() - t0
        text = log_path.read_text(errors='ignore')
        return {
            'exit': proc.returncode,
            'elapsed_sec': elapsed,
            'verified': proc.returncode == 0 and 'VERIFIED' in text,
            'log': str(log_path),
        }
    except subprocess.TimeoutExpired:
        return {'exit': None, 'elapsed_sec': timeout, 'verified': False,
                'timeout': True, 'log': str(log_path)}


def parse_model_from_log(log_path: pathlib.Path, var_map: Dict[int, int]) -> Optional[List[int]]:
    inv = {v: p for p, v in var_map.items()}
    text = log_path.read_text(errors='ignore')
    selected = []
    for line in text.splitlines():
        if not line.startswith('v '):
            continue
        for tok in line.split()[1:]:
            try:
                lit = int(tok)
            except ValueError:
                continue
            if lit > 0 and lit in inv:
                selected.append(inv[lit])
    return sorted(set(selected)) if selected else None


def full_lut_violations(lut: Dict[int, int], fixed_prefix: Sequence[int],
                        selected: Sequence[int], survivors: Sequence[int]) -> Iterable[dict]:
    support = set(int(x) for x in fixed_prefix) | set(int(x) for x in selected)
    fixed_prefix = [int(x) for x in fixed_prefix]
    selected = [int(x) for x in selected]
    survivors = [int(x) for x in survivors]
    for key, lb in lut.items():
        lb = int(lb)
        cap = 20 - lb
        if cap >= len(support):
            continue
        basis = unpack_basis(int(key))
        piv = make_pivot_dict(basis)
        cnt = sum(1 for p in support if in_span_piv(piv, int(p)))
        if cnt <= cap:
            continue
        fixed_count = sum(1 for p in fixed_prefix if in_span_piv(piv, int(p)))
        residual = cap - fixed_count
        selected_in_row = [int(p) for p in selected if in_span_piv(piv, int(p))]
        row_survivors = tuple(sorted(int(s) for s in survivors if in_span_piv(piv, int(s))))
        yield {
            'key': int(key),
            'lb': lb,
            'cap': cap,
            'fixed_count': int(fixed_count),
            'residual': residual,
            'row_survivors': row_survivors,
            'selected_in_row': tuple(sorted(selected_in_row)),
            'selection_count': len(selected_in_row),
            'excess': int(len(selected_in_row) - residual),
        }


def validate_and_reencode_learned_record(rec: dict, lut: Dict[int, int],
                                         fixed_prefix: Sequence[int],
                                         survivors: Sequence[int],
                                         var_map: Dict[int, int],
                                         seed_path: Optional[pathlib.Path] = None) -> dict:
    """Validate a learned-clause record against the current branch and recompute literals.

    This makes --seed-learned-jsonl safe only when the old clause is still a valid
    Wang consequence for the current fixed prefix, survivor set, and variable
    ordering.  The returned record preserves the original Wang-row provenance but
    uses freshly computed literals.
    """
    key = int(rec['key'])
    if key not in lut:
        raise ValueError(f'seed row key {key} is absent from LUT')
    lb = int(lut[key])
    cap = 20 - lb
    basis = unpack_basis(key)
    piv = make_pivot_dict(basis)
    fixed_count = sum(1 for p in fixed_prefix if in_span_piv(piv, int(p)))
    residual = cap - fixed_count
    if residual < 0:
        raise ValueError(f'seed row {key} has negative residual for this fixed prefix')
    pts = [int(p) for p in rec['points']]
    if len(set(pts)) != len(pts):
        raise ValueError(f'seed row {key} has duplicate points {pts}')
    if len(pts) != residual + 1:
        raise ValueError(f'seed row {key} has {len(pts)} points but residual+1={residual+1}')
    survivor_set = set(int(s) for s in survivors)
    for p in pts:
        if p not in survivor_set:
            raise ValueError(f'seed row {key} point {p} is not a current survivor')
        if p not in var_map:
            raise ValueError(f'seed row {key} point {p} has no current variable')
        if not in_span_piv(piv, p):
            raise ValueError(f'seed row {key} point {p} is not in the named Wang row')
    row_points = tuple(sorted(int(s) for s in survivors if in_span_piv(piv, int(s))))
    full_count = comb(len(row_points), residual + 1) if len(row_points) > residual else 0
    out = dict(rec)
    out['key'] = key
    out['lb'] = lb
    out['cap'] = cap
    out['fixed_count'] = int(fixed_count)
    out['residual'] = int(residual)
    out['row_candidate_count'] = len(row_points)
    out['full_direct_clause_count_for_row'] = int(full_count)
    out['points'] = pts
    out['lits'] = [-var_map[p] for p in pts]
    if seed_path is not None:
        out['seeded_from'] = str(seed_path)
    return out



def choose_violation_order(v: dict) -> Tuple[int, int, int, int]:
    # Strong small residual rows first; among expensive rows, larger excess first.
    return (int(v['residual']), len(v['row_survivors']), -int(v['excess']), int(v['key']))


def append_jsonl(path: pathlib.Path, records: Sequence[dict]) -> None:
    if not records:
        return
    with path.open('a') as f:
        for rec in records:
            f.write(json.dumps(rec, sort_keys=True) + '\n')


# ---------------------------------------------------------------------------
# Main iteration


def run_branch(args, lut: Dict[int, int], stratum: Optional[dict], out_dir: pathlib.Path) -> dict:
    fixed_prefix, candidates, info, branch_meta = branch_info(args, lut, stratum)
    if info.get('impossible_rows'):
        return {
            **branch_meta,
            'fixed_prefix': fixed_prefix,
            'status': 'FIXED_PREFIX_VIOLATES',
            'violating_row': info['impossible_rows'][0],
        }

    base_clauses, var_map, top_id, base_meta = build_base_cnf(info)
    survivors = [int(x) for x in info['survivors']]
    target = int(info['target'])

    out_dir.mkdir(parents=True, exist_ok=True)
    learned_path = out_dir / 'learned_clauses.jsonl'
    if learned_path.exists() and not args.append:
        learned_path.unlink()

    base_payload = {
        'schema': 'witness_subset_base_v1',
        **branch_meta,
        'fixed_prefix': fixed_prefix,
        'rank_budget': 20,
        'candidate_count': len(candidates),
        'candidate_universe': [int(x) for x in candidates],
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
    known_full_rows: Dict[Tuple[Tuple[int, ...], int], int] = {}
    round_log = []
    learned_count = 0
    learned_by_source = defaultdict(int)
    learned_by_residual = defaultdict(int)

    seed_count = 0
    if args.seed_learned_jsonl:
        seed_path = pathlib.Path(args.seed_learned_jsonl)
        if not seed_path.exists():
            raise FileNotFoundError(seed_path)
        seeded_records = []
        with seed_path.open() as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                raw = json.loads(line)
                rec = validate_and_reencode_learned_record(raw, lut, fixed_prefix, survivors, var_map, seed_path)
                pts_tuple = tuple(sorted(int(p) for p in rec['points']))
                if pts_tuple in known_clause_points:
                    continue
                known_clause_points.add(pts_tuple)
                clauses.append([int(x) for x in rec['lits']])
                learned_count += 1
                seed_count += 1
                learned_by_source[rec.get('source', 'seeded')] += 1
                learned_by_residual[int(rec['residual'])] += 1
                seeded_records.append(rec)
        append_jsonl(learned_path, seeded_records)

    for rnd in range(args.max_rounds):
        cnf_path = out_dir / f'round{rnd:03d}.cnf'
        write_cnf(clauses, top_id, cnf_path)
        sol = run_cadical(cnf_path, args.solve_time, with_drat=False)
        ri = {
            'round': rnd,
            'cnf': str(cnf_path),
            'clauses': len(clauses),
            'variables': top_id,
            'cadical_exit': sol['exit'],
            'cadical_sec': round(sol['elapsed_sec'], 2),
        }

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
                'schema': 'witness_subset_result_v1',
                **branch_meta,
                'fixed_prefix': fixed_prefix,
                'status': 'UNSAT',
                'rounds': rnd + 1,
                'survivor_count': len(survivors),
                'target': target,
                'final_clauses': len(clauses),
                'final_variables': top_id,
                'learned_clause_count': learned_count,
                'seeded_clause_count': seed_count,
                'seed_learned_jsonl': args.seed_learned_jsonl or None,
                'learned_by_source': dict(sorted(learned_by_source.items())),
                'learned_by_residual': {str(k): v for k, v in sorted(learned_by_residual.items())},
                'round_log': round_log,
                'final_cnf': str(final_cnf),
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
            print(json.dumps({k: result[k] for k in ['branch', 'idx', 'status', 'rounds', 'drat_cadical_exit', 'final_clauses', 'learned_clause_count'] if k in result}, sort_keys=True))
            return result

        if not sol['sat'] or not sol['has_model']:
            ri['result'] = 'SOLVER_UNKNOWN_OR_NO_MODEL'
            round_log.append(ri)
            result = {
                'schema': 'witness_subset_result_v1',
                **branch_meta,
                'fixed_prefix': fixed_prefix,
                'status': 'SOLVER_UNKNOWN',
                'rounds': rnd + 1,
                'survivor_count': len(survivors),
                'target': target,
                'round_log': round_log,
                'learned_clause_count': learned_count,
                'learned_clause_provenance': str(learned_path),
                'base_metadata': str(out_dir / 'base_metadata.json'),
            }
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
            print(json.dumps({k: result[k] for k in ['branch', 'idx', 'status', 'rounds'] if k in result}, sort_keys=True))
            return result

        selected = parse_model_from_log(pathlib.Path(sol['log']), var_map)
        if selected is None or len(selected) != target:
            ri['result'] = f'BAD_MODEL_size_{0 if selected is None else len(selected)}'
            round_log.append(ri)
            result = {
                'schema': 'witness_subset_result_v1',
                **branch_meta,
                'fixed_prefix': fixed_prefix,
                'status': 'BAD_MODEL',
                'rounds': rnd + 1,
                'selected_size': 0 if selected is None else len(selected),
                'target': target,
                'round_log': round_log,
            }
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
            return result

        violations = list(full_lut_violations(lut, fixed_prefix, selected, survivors))
        violations.sort(key=choose_violation_order)
        negative_residual = next((v for v in violations if int(v['residual']) < 0), None)
        if negative_residual is not None:
            ri['result'] = 'INTERNAL_FIXED_PREFIX_VIOLATES'
            round_log.append(ri)
            result = {
                'schema': 'witness_subset_result_v2',
                **branch_meta,
                'fixed_prefix': fixed_prefix,
                'status': 'INTERNAL_FIXED_PREFIX_VIOLATES',
                'violating_row': {k: (list(v) if isinstance(v, tuple) else v) for k, v in negative_residual.items() if k != 'row_survivors'},
                'rounds': rnd + 1,
                'round_log': round_log,
            }
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
            return result
        ri['model_size'] = len(selected)
        ri['support_size'] = len(set(fixed_prefix) | set(selected))
        ri['lut_violations'] = len(violations)
        ri['max_excess'] = max((int(v['excess']) for v in violations), default=0)

        if not violations:
            support = sorted(set(fixed_prefix) | set(selected))
            ri['result'] = 'LUT_ADMISSIBLE'
            round_log.append(ri)
            result = {
                'schema': 'witness_subset_result_v1',
                **branch_meta,
                'fixed_prefix': fixed_prefix,
                'status': 'LUT_ADMISSIBLE_SUPPORT_FOUND',
                'support': support,
                'support_size': len(support),
                'selected': selected,
                'rounds': rnd + 1,
                'round_log': round_log,
                'learned_clause_count': learned_count,
                'learned_clause_provenance': str(learned_path),
                'base_metadata': str(out_dir / 'base_metadata.json'),
                'meaning': 'This is an A-support satisfying Wang occupation rows; it is not a tensor decomposition.',
            }
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
            print(json.dumps({k: result[k] for k in ['branch', 'idx', 'status', 'rounds', 'support_size'] if k in result}, sort_keys=True))
            return result

        new_records: List[dict] = []
        new_clause_count = 0
        skipped_duplicate = 0
        skipped_budget = 0
        cheap_full_rows = 0
        witness_rows = 0
        witness_limit = args.max_witness_clauses_per_round
        total_limit = args.max_new_clauses_per_round

        for v in violations:
            residual = int(v['residual'])
            if residual < 0:
                raise RuntimeError('negative residual reached clause-learning loop; fixed prefix should have been rejected')
            elif len(v['selected_in_row']) <= residual:
                continue
            else:
                subset_points = list(v['selected_in_row'])[:residual + 1]

            row_points = tuple(int(x) for x in v['row_survivors'])
            row_lits = [var_map[p] for p in row_points if p in var_map]
            full_clause_count = comb(len(row_lits), residual + 1) if residual >= 0 and len(row_lits) > residual else 0
            can_full = 0 < full_clause_count <= args.direct_clause_threshold

            candidate_clause_records = []
            source = 'full_row_direct' if can_full else 'witness_subset'
            if can_full:
                # Do not mark a full row as complete before all its clauses survive
                # duplicate and per-round budget checks.  Duplicate point-clauses
                # are handled by known_clause_points, so revisiting a row is safe.
                cheap_full_rows += 1
                for pts in combinations(row_points, residual + 1):
                    pts = tuple(int(p) for p in pts)
                    if pts in known_clause_points:
                        skipped_duplicate += 1
                        continue
                    lits = [-var_map[p] for p in pts]
                    candidate_clause_records.append({
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
            else:
                if witness_limit is not None and witness_rows >= witness_limit:
                    skipped_budget += 1
                    continue
                # Multi-witness: learn ALL C(selected, r+1) subsets from model's
                # selected points in this row, not just one.  This is vastly more
                # aggressive than single-witness while remaining a valid consequence
                # of the same Wang row.
                sel_in_row = sorted(int(p) for p in v['selected_in_row'])
                multi_count = comb(len(sel_in_row), residual + 1)
                for pts in combinations(sel_in_row, residual + 1):
                    pts = tuple(int(p) for p in pts)
                    if pts in known_clause_points:
                        skipped_duplicate += 1
                        continue
                    lits = [-var_map[p] for p in pts]
                    candidate_clause_records.append({
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
                        'multi_witness_total': multi_count,
                        'points': list(pts),
                        'lits': lits,
                    })
                witness_rows += 1

            for rec in candidate_clause_records:
                if total_limit is not None and new_clause_count >= total_limit:
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
            if total_limit is not None and new_clause_count >= total_limit:
                break

        append_jsonl(learned_path, new_records)
        learned_count += len(new_records)
        ri['new_clauses'] = len(new_records)
        ri['new_by_source'] = dict(sorted((k, sum(1 for r in new_records if r['source'] == k)) for k in {r['source'] for r in new_records}))
        by_res = defaultdict(int)
        for r in new_records:
            by_res[int(r['residual'])] += 1
        ri['new_by_residual'] = {str(k): v for k, v in sorted(by_res.items())}
        ri['cheap_full_rows_used'] = cheap_full_rows
        ri['witness_rows_used'] = witness_rows
        ri['skipped_duplicate'] = skipped_duplicate
        ri['skipped_budget'] = skipped_budget
        ri['result'] = 'SAT_SEPARATED'
        round_log.append(ri)
        (out_dir / 'run_state.json').write_text(json.dumps({
            'schema': 'witness_subset_run_state_v1',
            **branch_meta,
            'fixed_prefix': fixed_prefix,
            'status': 'RUNNING',
            'last_round': rnd,
            'clauses': len(clauses),
            'variables': top_id,
            'learned_clause_count': learned_count,
            'round_log': round_log,
            'learned_clause_provenance': str(learned_path),
        }, indent=2, sort_keys=True) + '\n')
        print(f"  Rnd {rnd}: viol={len(violations)} max_excess={ri['max_excess']} "
              f"new={len(new_records)} full_rows={cheap_full_rows} witness={witness_rows} "
              f"clauses={len(clauses)} sat_sec={sol['elapsed_sec']:.1f}")

        if not new_records:
            open_cnf = out_dir / 'current.cnf'
            write_cnf(clauses, top_id, open_cnf)
            result = {
                'schema': 'witness_subset_result_v1',
                **branch_meta,
                'fixed_prefix': fixed_prefix,
                'status': 'NO_NEW_CLAUSES',
                'rounds': rnd + 1,
                'survivor_count': len(survivors),
                'target': target,
                'round_log': round_log,
                'learned_clause_count': learned_count,
                'seeded_clause_count': seed_count,
                'seed_learned_jsonl': args.seed_learned_jsonl or None,
                'learned_clause_provenance': str(learned_path),
                'learned_clause_provenance_sha256': sha256_file(learned_path),
                'current_cnf': str(open_cnf),
                'current_cnf_sha256': sha256_file(open_cnf),
                'base_metadata': str(out_dir / 'base_metadata.json'),
            }
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
            return result

    open_cnf = out_dir / 'current.cnf'
    write_cnf(clauses, top_id, open_cnf)
    result = {
        'schema': 'witness_subset_result_v1',
        **branch_meta,
        'fixed_prefix': fixed_prefix,
        'status': 'MAX_ROUNDS',
        'rounds': args.max_rounds,
        'survivor_count': len(survivors),
        'target': target,
        'final_clauses': len(clauses),
        'final_variables': top_id,
        'learned_clause_count': learned_count,
        'seeded_clause_count': seed_count,
        'seed_learned_jsonl': args.seed_learned_jsonl or None,
        'learned_by_source': dict(sorted(learned_by_source.items())),
        'learned_by_residual': {str(k): v for k, v in sorted(learned_by_residual.items())},
        'round_log': round_log,
        'learned_clause_provenance': str(learned_path),
        'learned_clause_provenance_sha256': sha256_file(learned_path),
        'current_cnf': str(open_cnf),
        'current_cnf_sha256': sha256_file(open_cnf),
        'base_metadata': str(out_dir / 'base_metadata.json'),
    }
    (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--branch', choices=['matching', 'rep2'], required=True)
    ap.add_argument('--strata', default='workspace/data/matching_strata/anchored_matching_strata.json')
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--indices', default='', help='comma-separated stratum indices for --branch matching')
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--max-rounds', type=int, default=50)
    ap.add_argument('--solve-time', type=int, default=300)
    ap.add_argument('--drat-time', type=int, default=900)
    ap.add_argument('--drat-solve-multiplier', type=int, default=5)
    ap.add_argument('--direct-clause-threshold', type=int, default=20,
                    help='full direct row encoding when binomial(row_size,residual+1) is at most this')
    ap.add_argument('--max-witness-clauses-per-round', type=int, default=5000,
                    help='maximum witness-subset clauses from expensive rows per round')
    ap.add_argument('--max-new-clauses-per-round', type=int, default=20000,
                    help='maximum learned clauses total per round')
    ap.add_argument('--seed-learned-jsonl', default='',
                    help='optional prior learned_clauses.jsonl to import before continuing')
    ap.add_argument('--append', action='store_true', help='deprecated unsafe mode; currently rejected')
    args = ap.parse_args()
    if args.append:
        raise SystemExit('--append is disabled: use --seed-learned-jsonl into a fresh output directory')

    out_root = pathlib.Path(args.out_dir)
    out_root.mkdir(parents=True, exist_ok=True)
    print(f'Loading LUT from {args.lut}...')
    lut = load_lut(pathlib.Path(args.lut))
    print(f'  {len(lut):,} rows')

    results = []
    if args.branch == 'matching':
        if not args.indices:
            raise SystemExit('--indices is required for matching branch')
        wanted = {int(x) for x in args.indices.replace(';', ',').split(',') if x.strip()}
        strata = []
        for idx, st in iter_strata(pathlib.Path(args.strata), 0):
            if idx in wanted:
                st = dict(st)
                st['_idx'] = int(idx)
                strata.append(st)
        if {int(s['_idx']) for s in strata} != wanted:
            raise SystemExit(f'missing requested strata: {sorted(wanted - {int(s["_idx"]) for s in strata})}')
        for st in strata:
            idx = int(st['_idx'])
            sub = out_root / f'idx{idx:03d}'
            print(f'\n=== matching idx={idx} k={st["k"]} canonical={st["canonical"]} ===')
            t0 = time.time()
            res = run_branch(args, lut, st, sub)
            res['total_elapsed_sec'] = round(time.time() - t0, 2)
            results.append(res)
    else:
        print('\n=== adjacent-pair rep2 branch ===')
        t0 = time.time()
        res = run_branch(args, lut, None, out_root / 'rep2')
        res['total_elapsed_sec'] = round(time.time() - t0, 2)
        results.append(res)

    summary = {'schema': 'witness_subset_batch_v1', 'records': results}
    (out_root / 'summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(f'\nSaved {out_root / "summary.json"}')
    for res in results:
        compact = {k: res[k] for k in ['branch', 'idx', 'status', 'rounds', 'survivor_count',
                                       'target', 'learned_clause_count', 'final_clauses',
                                       'drat_cadical_exit', 'total_elapsed_sec'] if k in res}
        if 'drat_trim' in res:
            compact['drat_verified'] = res['drat_trim'].get('verified', False)
        print(json.dumps(compact, sort_keys=True))


if __name__ == '__main__':
    main()
