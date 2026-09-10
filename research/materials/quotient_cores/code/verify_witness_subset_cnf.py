#!/usr/bin/env python3
"""Verify analysis witness-subset CNF provenance and exact regeneration.

For a completed run directory produced by witness_subset_separation.py,
this checker verifies:
  * structural consistency: prefix/candidate disjointness, target = 20-|prefix|,
    survivor ⊆ candidate, edge points are distinct survivors, vertex-excluded
    points are candidates not in survivors;
  * every residual-1 base edge clause is justified by its stored Wang row;
  * every residual-0 vertex exclusion in base metadata is justified;
  * every learned clause in learned_clauses.jsonl is an (r+1)-subset contained
    in its Wang row after the fixed-prefix occupancy is subtracted;
  * the final/current CNF is exactly regenerated from base edges, the PySAT exact
    cardinality constraints, and the learned clauses in JSONL order;
  * an optional DRAT-trim replay requiring return code 0 AND 'VERIFIED'.

The checker does not prove LUT correctness or orbit coverage; it checks the local
connection between a generated CNF and the Wang occupation rows named in the run.
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
from wang_capacity_lazy import unpack_basis  # noqa:E402
from graph_coloring_certificate import load_lut, make_pivot_dict, in_span_piv  # noqa:E402
from witness_subset_separation import atleast_pysat, atmost_pysat  # noqa:E402


def read_jsonl(path: pathlib.Path) -> List[dict]:
    if not path.exists():
        return []
    out = []
    with path.open() as f:
        for line_no, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            rec['_line'] = line_no
            out.append(rec)
    return out


def read_cnf(path: pathlib.Path) -> Tuple[int, List[List[int]]]:
    top = None
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
    if top is None:
        raise ValueError(f'no DIMACS header in {path}')
    if declared != len(clauses):
        raise ValueError(f'clause count mismatch in {path}: declared {declared}, actual {len(clauses)}')
    return top, clauses


def wang_row_values(lut: Dict[int, int], key: int, fixed_prefix: Sequence[int]):
    if key not in lut:
        raise AssertionError(f'row key {key} absent from LUT')
    lb = int(lut[key])
    cap = 20 - lb
    basis = unpack_basis(int(key))
    piv = make_pivot_dict(basis)
    fixed_count = sum(1 for p in fixed_prefix if in_span_piv(piv, int(p)))
    residual = cap - fixed_count
    return lb, cap, fixed_count, residual, piv


# ---- Structural consistency checks ----

def verify_structure(base: dict, lut: Dict[int, int]) -> dict:
    """Check prefix/candidate/survivor/target consistency."""
    problems = []
    fixed_prefix = [int(x) for x in base['fixed_prefix']]
    target = int(base['target'])
    survivors = [int(x) for x in base['base']['survivors']]
    survivor_set = set(survivors)
    prefix_set = set(fixed_prefix)

    # Target = 20 - |prefix|
    expected_target = 20 - len(fixed_prefix)
    if target != expected_target:
        problems.append(f'target {target} != 20 - |prefix|={expected_target}')

    # Prefix / survivor disjointness
    overlap = prefix_set & survivor_set
    if overlap:
        problems.append(f'prefix/survivor overlap: {sorted(overlap)}')

    # Candidate universe when stored
    if 'candidate_universe' in base:
        candidates = [int(x) for x in base['candidate_universe']]
        cand_set = set(candidates)
        # Candidates should be disjoint from prefix
        cand_prefix_overlap = cand_set & prefix_set
        if cand_prefix_overlap:
            problems.append(f'candidate/prefix overlap: {sorted(cand_prefix_overlap)[:10]}')
        # Survivors ⊆ candidates
        surv_outside = survivor_set - cand_set
        if surv_outside:
            problems.append(f'{len(surv_outside)} survivors not in candidate universe')
        # Vertex-excluded = candidates \ survivors
        vertex_excluded_pts = {int(p) for p, _ in base['base'].get('vertex_exclusions', [])}
        expected_excluded = cand_set - survivor_set
        if vertex_excluded_pts != expected_excluded:
            diff = (vertex_excluded_pts ^ expected_excluded)
            problems.append(f'vertex_exclusions != candidates\\survivors: {len(diff)} mismatches')
    else:
        problems.append('no candidate_universe in base metadata (older format)')

    # No duplicate survivors
    if len(survivors) != len(survivor_set):
        problems.append(f'duplicate survivors: {len(survivors)} listed, {len(survivor_set)} unique')

    # Check base-edge point distinctness
    for i, edge in enumerate(base['base'].get('base_edges', [])):
        pts = [int(x) for x in edge['points']]
        if len(pts) != 2 or pts[0] == pts[1]:
            problems.append(f'base edge {i}: non-distinct points {pts}')
            if i > 5:
                problems.append(f'... and possibly more bad edges')
                break

    return {
        'prefix_count': len(fixed_prefix),
        'target': target,
        'survivor_count': len(survivors),
        'problems': problems,
        'structure_ok': len(problems) == 0,
    }


def verify_base(base: dict, lut: Dict[int, int]) -> dict:
    fixed_prefix = [int(x) for x in base['fixed_prefix']]
    survivors = [int(x) for x in base['base']['survivors']]
    survivor_set = set(survivors)
    var_map = {p: i + 1 for i, p in enumerate(survivors)}
    edge_bad = []
    for i, edge in enumerate(base['base'].get('base_edges', [])):
        pts = [int(x) for x in edge['points']]
        key = int(edge['key'])
        lb, cap, fixed_count, residual, piv = wang_row_values(lut, key, fixed_prefix)
        if residual != 1 or len(pts) != 2:
            edge_bad.append({'i': i, 'key': key, 'points': pts, 'residual': residual})
            continue
        for p in pts:
            if p not in survivor_set or not in_span_piv(piv, p):
                edge_bad.append({'i': i, 'key': key, 'point': p, 'reason': 'point_not_survivor_or_not_in_row'})
        if pts[0] == pts[1]:
            edge_bad.append({'i': i, 'key': key, 'points': pts, 'reason': 'non_distinct_edge_points'})
        expected_lits = [-var_map[pts[0]], -var_map[pts[1]]]
        if [int(x) for x in edge['lits']] != expected_lits:
            edge_bad.append({'i': i, 'key': key, 'points': pts, 'reason': 'literal_mismatch', 'expected': expected_lits, 'got': edge['lits']})

    vertex_bad = []
    for i, pair in enumerate(base['base'].get('vertex_exclusions', [])):
        p, key = int(pair[0]), int(pair[1])
        lb, cap, fixed_count, residual, piv = wang_row_values(lut, key, fixed_prefix)
        if residual != 0 or not in_span_piv(piv, p):
            vertex_bad.append({'i': i, 'key': key, 'point': p, 'residual': residual})

    return {
        'base_edges_checked': len(base['base'].get('base_edges', [])),
        'base_edge_bad_count': len(edge_bad),
        'base_edge_bad_head': edge_bad[:10],
        'vertex_exclusions_checked': len(base['base'].get('vertex_exclusions', [])),
        'vertex_bad_count': len(vertex_bad),
        'vertex_bad_head': vertex_bad[:10],
    }


def verify_learned(base: dict, records: List[dict], lut: Dict[int, int]) -> dict:
    fixed_prefix = [int(x) for x in base['fixed_prefix']]
    survivors = [int(x) for x in base['base']['survivors']]
    survivor_set = set(survivors)
    var_map = {p: i + 1 for i, p in enumerate(survivors)}
    bad = []
    by_source = {}
    by_residual = {}
    for rec in records:
        source = rec.get('source', '?')
        by_source[source] = by_source.get(source, 0) + 1
        key = int(rec['key'])
        lb, cap, fixed_count, residual, piv = wang_row_values(lut, key, fixed_prefix)
        pts = [int(x) for x in rec['points']]
        lits = [int(x) for x in rec['lits']]
        by_residual[str(residual)] = by_residual.get(str(residual), 0) + 1
        problems = []
        if int(rec['lb']) != lb:
            problems.append(f'lb {rec["lb"]} != {lb}')
        if int(rec['cap']) != cap:
            problems.append(f'cap {rec["cap"]} != {cap}')
        if int(rec['fixed_count']) != fixed_count:
            problems.append(f'fixed_count {rec["fixed_count"]} != {fixed_count}')
        if int(rec['residual']) != residual:
            problems.append(f'residual {rec["residual"]} != {residual}')
        if residual < 0:
            problems.append('negative residual should be represented by fixed-prefix contradiction, not learned point clause')
        elif len(pts) != residual + 1:
            problems.append(f'len(points) {len(pts)} != residual+1 {residual+1}')
        if len(set(pts)) != len(pts):
            problems.append('duplicate points in learned clause')
        for p in pts:
            if p not in survivor_set:
                problems.append(f'point {p} not in survivors')
            if not in_span_piv(piv, p):
                problems.append(f'point {p} not in Wang row')
        expected_lits = [-var_map[p] for p in pts]
        if lits != expected_lits:
            problems.append(f'lits mismatch expected {expected_lits} got {lits}')
        if source == 'full_row_direct':
            row_cand = [p for p in survivors if in_span_piv(piv, p)]
            if int(rec.get('row_candidate_count', -1)) != len(row_cand):
                problems.append('row_candidate_count mismatch')
            if residual >= 0 and len(row_cand) > residual:
                expected_full = comb(len(row_cand), residual + 1)
                if int(rec.get('full_direct_clause_count_for_row', -1)) != expected_full:
                    problems.append('full_direct_clause_count_for_row mismatch')
        if problems:
            bad.append({'line': rec.get('_line'), 'key': key, 'points': pts, 'problems': problems})
    return {
        'learned_checked': len(records),
        'learned_bad_count': len(bad),
        'learned_bad_head': bad[:20],
        'learned_by_source': by_source,
        'learned_by_residual': dict(sorted(by_residual.items(), key=lambda kv: int(kv[0]))),
    }


def regenerate_cnf(base: dict, learned: List[dict]) -> Tuple[int, List[List[int]]]:
    survivors = [int(x) for x in base['base']['survivors']]
    target = int(base['target'])
    var_map = {p: i + 1 for i, p in enumerate(survivors)}
    top_id = len(var_map)
    clauses: List[List[int]] = []
    clauses.extend([[int(x) for x in edge['lits']] for edge in base['base'].get('base_edges', [])])
    al, top_id = atleast_pysat(list(var_map.values()), target, top_id)
    clauses.extend(al)
    am, top_id = atmost_pysat(list(var_map.values()), target, top_id)
    clauses.extend(am)
    for rec in learned:
        clauses.append([int(x) for x in rec['lits']])
    return top_id, clauses


def run_drat_trim(cnf: pathlib.Path, drat: pathlib.Path, timeout: int) -> dict:
    t0 = time.time()
    try:
        proc = subprocess.run(['drat-trim', str(cnf), str(drat)], capture_output=True, text=True, timeout=timeout)
        text = (proc.stdout or '') + '\n' + (proc.stderr or '')
        verified = proc.returncode == 0 and 'VERIFIED' in text
        return {'exit': proc.returncode, 'elapsed_sec': round(time.time() - t0, 2),
                'verified': verified}
    except subprocess.TimeoutExpired:
        return {'exit': None, 'elapsed_sec': timeout, 'verified': False, 'timeout': True}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--run-dir', required=True, help='Subdirectory containing base_metadata.json, learned_clauses.jsonl, and summary.json')
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--drat-replay', action='store_true')
    ap.add_argument('--drat-time', type=int, default=900)
    ap.add_argument('--out', default='')
    args = ap.parse_args()

    run_dir = pathlib.Path(args.run_dir)
    base_path = run_dir / 'base_metadata.json'
    learned_path = run_dir / 'learned_clauses.jsonl'
    summary_path = run_dir / 'summary.json'
    base = json.loads(base_path.read_text())
    summary = json.loads(summary_path.read_text()) if summary_path.exists() else {}
    learned = read_jsonl(learned_path)
    lut = load_lut(pathlib.Path(args.lut))

    structure_check = verify_structure(base, lut)
    base_check = verify_base(base, lut)
    learned_check = verify_learned(base, learned, lut)
    regen_top, regen_clauses = regenerate_cnf(base, learned)

    cnf_name = summary.get('final_cnf') or summary.get('current_cnf') or str(run_dir / 'final.cnf')
    cnf_path = pathlib.Path(cnf_name)
    cnf_check = {'checked_cnf': str(cnf_path), 'exists': cnf_path.exists()}
    if cnf_path.exists():
        cnf_top, cnf_clauses = read_cnf(cnf_path)
        exact = (cnf_top == regen_top and cnf_clauses == regen_clauses)
        cnf_check.update({
            'cnf_variables': cnf_top,
            'cnf_clauses': len(cnf_clauses),
            'regenerated_variables': regen_top,
            'regenerated_clauses': len(regen_clauses),
            'exact_sequence_match': exact,
            'header_matches_summary': (not summary) or (int(summary.get('final_variables', cnf_top)) == cnf_top and int(summary.get('final_clauses', len(cnf_clauses))) == len(cnf_clauses)),
        })
        if not exact:
            first = None
            for i, (a, b) in enumerate(zip(cnf_clauses, regen_clauses)):
                if a != b:
                    first = {'index': i, 'cnf': a, 'regen': b}
                    break
            if first is None and len(cnf_clauses) != len(regen_clauses):
                first = {'index': min(len(cnf_clauses), len(regen_clauses)), 'reason': 'length mismatch'}
            cnf_check['first_mismatch'] = first

    drat_check = None
    if args.drat_replay and summary.get('drat') and cnf_path.exists():
        drat_path = pathlib.Path(summary['drat'])
        if drat_path.exists():
            drat_check = run_drat_trim(cnf_path, drat_path, args.drat_time)
        else:
            drat_check = {'verified': False, 'reason': f'DRAT file not found: {drat_path}'}

    ok = (structure_check.get('structure_ok', False) and
          base_check['base_edge_bad_count'] == 0 and base_check['vertex_bad_count'] == 0 and
          learned_check['learned_bad_count'] == 0 and cnf_check.get('exact_sequence_match', False))
    if args.drat_replay:
        ok = ok and bool(drat_check and drat_check.get('verified'))

    result = {
        'schema': 'verify_witness_subset_cnf_v2',
        'run_dir': str(run_dir),
        'status': 'verified' if ok else 'failed',
        'summary_status': summary.get('status'),
        'structure_check': structure_check,
        'base_check': base_check,
        'learned_check': learned_check,
        'cnf_check': cnf_check,
        'drat_replay': drat_check,
    }
    out_path = pathlib.Path(args.out) if args.out else (run_dir / 'strict_verification.json')
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'status': result['status'],
        'run_dir': str(run_dir),
        'structure_ok': structure_check.get('structure_ok'),
        'learned_checked': learned_check['learned_checked'],
        'exact_sequence_match': cnf_check.get('exact_sequence_match'),
        'drat_verified': None if drat_check is None else drat_check.get('verified'),
    }, sort_keys=True))
    if not ok:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
