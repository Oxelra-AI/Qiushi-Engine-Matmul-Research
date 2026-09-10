#!/usr/bin/env python3
"""analysis: extract a compact UNSAT core for the fixed repeated E11-core branch.

This script targets the fixed representative p=1 (E12 in the E11 quotient).
It builds the same compact necessary-condition model as analysis's CNF, but first
uses OR-Tools CP-SAT assumptions at the high-level linear-constraint layer to
identify a much smaller contradictory subset.  It then emits a clean DIMACS CNF
for only that subset, with hard total/fixed-repeat constraints, so CaDiCaL can
produce an independently checkable DRAT proof.

The CP-SAT core is a size-reduction device, not a mathematical proof by itself.
Only the clean CNF plus DRAT replay establishes the fixed-representative compact
branch exclusion.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient
from fixed_A_saturation import mat_rank_f2
from complete_core_and_transversal import ROOT, build_core_constraints
from quotient_rank_cuts import build_contractions, point_mask_for_q
from core_repeat_symmetry_and_cnf import analyze_symmetry, extract_compact_constraints, label8, sha256
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis

OUTDIR = ROOT / 'workspace/data/repeat_branch_certificate'
ALLMASK = (1 << 255) - 1


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}, payload.get('meta', {})


def build_high_level_constraints(source: Path, fixed_repeat: int):
    s = 19
    core = CoreQuotient(1)
    lut, lut_meta = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records, core_meta = build_core_constraints(core, lut)
    record_by_key = {int(r['key8']): r for r in records}
    T = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    contractions = build_contractions(T)
    masks = {q: point_mask_for_q(q) for q in contractions}
    points = list(range(1, 256))
    point_cap = {}
    for p in points:
        key8 = core.key8_from_rows([p])
        key9 = core.key9_from_key8(key8)
        point_cap[p] = max(0, min(s, s - int(lut[key9])))
    if point_cap.get(fixed_repeat, 0) < 2:
        raise ValueError(f'fixed point {fixed_repeat} has cap {point_cap.get(fixed_repeat)}')

    wang_keys, qcuts = extract_compact_constraints(source, records, core, lut)

    constraints = []
    # Wang rows.
    for key8 in sorted(wang_keys):
        rec = record_by_key[int(key8)]
        pts = subspace_points_from_basis(unpack_basis(int(key8)))
        constraints.append({
            'kind': 'wang',
            'key8': int(key8),
            'key9': int(rec['key9']),
            'basis8': [int(z) for z in unpack_basis(int(key8))],
            'dim8': int(rec['dim8']),
            'L': int(rec['L']),
            'cap': s - int(rec['L']),
            'sense': '<=',
            'coeffs': {int(p): 1 for p in pts},
            'rhs': s - int(rec['L']),
        })
    # Contraction lower bounds.
    for q, c in contractions.items():
        rk = int(c['rank'])
        if rk <= 0:
            continue
        constraints.append({
            'kind': 'contraction_lower',
            'q': int(q),
            'rank': rk,
            'sense': '>=',
            'coeffs': {int(p): 1 for p in points if ((q & p).bit_count() & 1)},
            'rhs': rk,
        })
    # Unconditional quotient-rank inequalities.
    for c in qcuts:
        q1, q2 = int(c['sources'][0]), int(c['sources'][1])
        q1, q2 = min(q1, q2), max(q1, q2)
        target = int(c['target'])
        req = int(c['requirement'])
        rq1 = int(contractions[q1]['rank'])
        rq2 = int(contractions[q2]['rank'])
        source_union = masks[q1] | masks[q2]
        outside_mask = masks[target] & (~source_union) & ALLMASK
        coeffs = {}
        for p in points:
            coeff = 0
            if (outside_mask >> (p - 1)) & 1:
                coeff += 1
            if ((q1 & p).bit_count() & 1):
                coeff += 1
            if ((q2 & p).bit_count() & 1):
                coeff += 1
            if coeff:
                coeffs[int(p)] = coeff
        constraints.append({
            'kind': 'unconditional_qcut',
            'side': str(c['side']),
            'sources': [q1, q2],
            'target': target,
            'source_ranks': [rq1, rq2],
            'requirement': req,
            'rhs': req + rq1 + rq2,
            'sense': '>=',
            'coeffs': coeffs,
            'W_dim': int(c.get('W_dim', -1)),
            'outside_point_count': int(c.get('outside_point_count', -1)),
        })
    return {
        's': s,
        'core': core,
        'lut_meta': lut_meta,
        'core_meta': core_meta,
        'points': points,
        'point_cap': point_cap,
        'constraints': constraints,
        'constraint_input_counts': {
            'wang': len(wang_keys),
            'contraction_lower': sum(1 for c in contractions.values() if int(c['rank']) > 0),
            'unconditional_qcut': len(qcuts),
        },
    }


def cp_sat_extract_core(data: dict, fixed_repeat: int, time_limit: float):
    from ortools.sat.python import cp_model
    s = data['s']
    model = cp_model.CpModel()
    x = {p: model.NewIntVar(0, int(data['point_cap'][p]), f'x_{p}') for p in data['points']}
    model.Add(sum(x[p] for p in data['points']) == s)
    model.Add(x[fixed_repeat] == 2)

    assumptions = []
    idx_by_bool = {}
    for i, c in enumerate(data['constraints']):
        b = model.NewBoolVar(f'a_{i}_{c["kind"]}')
        expr = sum(int(coef) * x[int(p)] for p, coef in c['coeffs'].items())
        if c['sense'] == '<=':
            model.Add(expr <= int(c['rhs'])).OnlyEnforceIf(b)
        else:
            model.Add(expr >= int(c['rhs'])).OnlyEnforceIf(b)
        model.AddAssumption(b)
        assumptions.append(b)
        idx_by_bool[b.Index()] = i

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = 8
    t0 = time.time()
    status = solver.Solve(model)
    elapsed = time.time() - t0
    status_name = solver.StatusName(status)
    core_indices = []
    raw_core = []
    if status == cp_model.INFEASIBLE:
        raw_core = list(solver.SufficientAssumptionsForInfeasibility())
        for lit in raw_core:
            idx = idx_by_bool.get(abs(int(lit)))
            if idx is not None:
                core_indices.append(idx)
    return {
        'status': status_name,
        'solve_sec': round(elapsed, 3),
        'raw_core_literals': [int(z) for z in raw_core],
        'core_indices': sorted(set(core_indices)),
        'core_size': len(set(core_indices)),
        'total_assumed_constraints': len(assumptions),
    }


def emit_clean_cnf(data: dict, fixed_repeat: int, core_indices: List[int], outdir: Path, stem: str,
                   card_encoding: str = 'seqcounter', pb_encoding: str = 'best') -> dict:
    from pysat.card import CardEnc, EncType as CardEncType
    from pysat.formula import CNF
    from pysat.pb import PBEnc, EncType as PBEncType

    card_enc_map = {
        'seqcounter': CardEncType.seqcounter,
        'totalizer': CardEncType.totalizer,
        'cardnetwrk': CardEncType.cardnetwrk,
        'sortnetwrk': CardEncType.sortnetwrk,
    }
    pb_enc_map = {
        'best': PBEncType.best,
        'bdd': PBEncType.bdd,
        'seqcounter': PBEncType.seqcounter,
        'sortnetwrk': PBEncType.sortnetwrk,
        'adder': PBEncType.adder,
        'binmerge': PBEncType.binmerge,
    }
    s = data['s']
    points = data['points']
    point_cap = data['point_cap']
    fixed_counts = {fixed_repeat: 2}

    token_point = {}
    tokens_by_point = defaultdict(list)
    next_var = 0
    for p in points:
        for _ in range(point_cap[p] - fixed_counts.get(p, 0)):
            next_var += 1
            token_point[next_var] = p
            tokens_by_point[p].append(next_var)

    cnf = CNF()
    top = next_var
    stats = Counter()
    impossible = []

    def add_atmost(lits: List[int], bound: int, label: str):
        nonlocal top
        stats[f'{label}_constraints'] += 1
        if bound < 0:
            cnf.append([]); stats[f'{label}_empty'] += 1; impossible.append({'label': label, 'sense': '<=', 'bound': bound}); return
        if bound >= len(lits):
            stats[f'{label}_taut'] += 1; return
        if bound == 0:
            for lit in lits:
                cnf.append([-lit])
            stats[f'{label}_clauses'] += len(lits); return
        enc = CardEnc.atmost(lits=lits, bound=bound, top_id=top, encoding=card_enc_map[card_encoding])
        cnf.extend(enc.clauses)
        stats[f'{label}_clauses'] += len(enc.clauses)
        top = max(top, enc.nv)

    def add_atleast(lits: List[int], bound: int, label: str):
        nonlocal top
        stats[f'{label}_constraints'] += 1
        if bound <= 0:
            stats[f'{label}_taut'] += 1; return
        if bound > len(lits):
            cnf.append([]); stats[f'{label}_empty'] += 1; impossible.append({'label': label, 'sense': '>=', 'bound': bound, 'available': len(lits)}); return
        if bound == len(lits):
            for lit in lits:
                cnf.append([lit])
            stats[f'{label}_clauses'] += len(lits); return
        enc = CardEnc.atleast(lits=lits, bound=bound, top_id=top, encoding=card_enc_map[card_encoding])
        cnf.extend(enc.clauses)
        stats[f'{label}_clauses'] += len(enc.clauses)
        top = max(top, enc.nv)

    def add_pb_atleast(lits: List[int], weights: List[int], bound: int, label: str):
        nonlocal top
        stats[f'{label}_constraints'] += 1
        if bound <= 0:
            stats[f'{label}_taut'] += 1; return
        if bound > sum(weights):
            cnf.append([]); stats[f'{label}_empty'] += 1; impossible.append({'label': label, 'sense': '>=', 'bound': bound, 'available_weight': sum(weights)}); return
        if all(w == 1 for w in weights):
            add_atleast(lits, bound, label + '_card')
            return
        enc = PBEnc.atleast(lits=lits, weights=weights, bound=bound, top_id=top, encoding=pb_enc_map[pb_encoding])
        cnf.extend(enc.clauses)
        stats[f'{label}_clauses'] += len(enc.clauses)
        top = max(top, enc.nv)

    def fixed_contrib(coeffs: Dict[int, int]) -> int:
        return sum(int(coeffs.get(p, 0)) * c for p, c in fixed_counts.items())

    # Hard total multiplicity after fixing p twice.
    all_lits = sorted(token_point)
    add_atmost(all_lits, s - 2, 'hard_total')
    add_atleast(all_lits, s - 2, 'hard_total')

    used = [data['constraints'][i] for i in core_indices]
    by_kind = Counter(c['kind'] for c in used)
    for c in used:
        lits = []
        weights = []
        for p, coef in c['coeffs'].items():
            for lit in tokens_by_point.get(int(p), []):
                lits.append(lit)
                weights.append(int(coef))
        rhs = int(c['rhs']) - fixed_contrib(c['coeffs'])
        if c['sense'] == '<=':
            # all Wang coeffs are one, so atmost cardinality is enough
            add_atmost(lits, rhs, c['kind'])
        else:
            add_pb_atleast(lits, weights, rhs, c['kind'])

    outdir.mkdir(parents=True, exist_ok=True)
    cnf_path = outdir / f'{stem}.cnf'
    cnf.to_file(str(cnf_path))
    meta = {
        'schema': 'fixed_repeat_core_cnf_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': s,
        'fixed_repeat_point': fixed_repeat,
        'fixed_repeat_label': label8(data['core'], fixed_repeat),
        'fixed_multiplicity': 2,
        'core_indices': core_indices,
        'core_constraint_count': len(core_indices),
        'core_constraints_by_kind': dict(by_kind),
        'card_encoding': card_encoding,
        'pb_encoding': pb_encoding,
        'token_variables_before_aux': next_var,
        'cnf_variables': top,
        'cnf_clauses': len(cnf.clauses),
        'encoding_stats': dict(stats),
        'impossible_constraints': impossible[:20],
        'impossible_constraint_count': len(impossible),
        'files': {'cnf': str(cnf_path)},
    }
    meta_path = outdir / f'{stem}.meta.json'
    meta['files']['cnf_sha256'] = sha256(cnf_path)
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + '\n')
    meta['files']['meta'] = str(meta_path)
    meta['files']['meta_sha256_before_insertion'] = sha256(meta_path)
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + '\n')
    return meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', type=Path, default=ROOT / 'workspace/data/quotient_rank_cuts/core_e11_multiset_quotient_sep_24r_fullstored.json')
    ap.add_argument('--fixed-repeat', type=int, default=1)
    ap.add_argument('--time-limit', type=float, default=300.0)
    ap.add_argument('--outdir', type=Path, default=OUTDIR / 'core_extract_p1')
    ap.add_argument('--stem', default='fixed_repeat_p1_core')
    args = ap.parse_args()

    t0 = time.time()
    data = build_high_level_constraints(args.source, args.fixed_repeat)
    print(f"high-level constraints: {len(data['constraints'])} input_counts={data['constraint_input_counts']}")
    cp = cp_sat_extract_core(data, args.fixed_repeat, args.time_limit)
    print(f"CP-SAT status={cp['status']} time={cp['solve_sec']} core={cp['core_size']}/{cp['total_assumed_constraints']}")

    sym = analyze_symmetry(data['core'], data['point_cap'])
    result = {
        'schema': 'fixed_repeat_core_extraction_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': data['s'],
        'fixed_repeat_point': args.fixed_repeat,
        'fixed_repeat_label': label8(data['core'], args.fixed_repeat),
        'source': str(args.source),
        'source_sha256': sha256(args.source),
        'point_cap_distribution': {str(k): int(v) for k, v in sorted(Counter(data['point_cap'].values()).items())},
        'constraint_input_counts': data['constraint_input_counts'],
        'cp_sat_assumption_core': cp,
        'symmetry': sym,
        'total_elapsed_before_cnf_sec': round(time.time() - t0, 3),
    }
    args.outdir.mkdir(parents=True, exist_ok=True)
    summary_path = args.outdir / 'core_extraction_summary.json'

    if cp['status'] == 'INFEASIBLE' and cp['core_indices']:
        meta = emit_clean_cnf(data, args.fixed_repeat, cp['core_indices'], args.outdir, args.stem)
        result['clean_cnf'] = meta
        print(f"clean CNF: vars={meta['cnf_variables']} clauses={meta['cnf_clauses']} constraints={meta['core_constraint_count']} by_kind={meta['core_constraints_by_kind']}")
    else:
        result['clean_cnf'] = None

    result['total_elapsed_sec'] = round(time.time() - t0, 3)
    summary_path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'Saved {summary_path}')
    print(json.dumps({
        'summary': str(summary_path),
        'status': cp['status'],
        'core_size': cp['core_size'],
        'cnf': None if result['clean_cnf'] is None else result['clean_cnf']['files']['cnf'],
        'clauses': None if result['clean_cnf'] is None else result['clean_cnf']['cnf_clauses'],
    }, sort_keys=True))


if __name__ == '__main__':
    main()
