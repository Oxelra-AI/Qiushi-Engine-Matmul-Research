#!/usr/bin/env python3
"""Build a complete Wang-occupation CNF for a given branch by precomputing
all constraints up to a residual threshold.

Unlike the iterative separator, this encodes ALL relevant Wang rows at once:
- residual 0: unit clauses (vertex exclusions) 
- residual 1: binary clauses (edge exclusions)
- residual 2: ternary clauses C(row_cand, 3) for each row
- residual r: (r+1)-clauses C(row_cand, r+1) for each row

This gives CaDiCaL the full constraint set from the start.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import subprocess
import sys
import time
from itertools import combinations
from math import comb
from typing import Dict, List, Sequence, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from wang_capacity_lazy import unpack_basis  # noqa:E402
from graph_coloring_certificate import (  # noqa:E402
    load_lut, iter_strata, process_stratum, make_pivot_dict, in_span_piv, rank1_points,
)
from witness_subset_separation import (  # noqa:E402
    process_rep2, atleast_pysat, atmost_pysat, write_cnf, sha256_file,
    run_cadical, run_drat_trim, append_jsonl,
)


def precompute_constraints(lut: Dict[int, int], fixed_prefix: List[int],
                           survivors: List[int], max_residual: int) -> dict:
    """Scan the full LUT and collect all constraints up to max_residual."""
    surv_set = set(survivors)
    constraints = []
    by_res = {}
    impossible = []
    t0 = time.time()
    
    for key, lb in lut.items():
        lb = int(lb)
        cap = 20 - lb
        # Quick filter: even with fc=0, residual = cap > max_residual → skip
        if cap > max_residual + len(fixed_prefix):
            continue
        basis = unpack_basis(int(key))
        piv = make_pivot_dict(basis)
        fc = sum(1 for p in fixed_prefix if in_span_piv(piv, int(p)))
        res = cap - fc
        if res < 0:
            impossible.append({'key': int(key), 'lb': lb, 'cap': cap, 'fc': fc, 'res': res})
            continue
        if res > max_residual:
            continue
        # Find survivor candidates in this row
        row_cands = [s for s in survivors if in_span_piv(piv, int(s))]
        if len(row_cands) <= res:
            continue
        constraints.append({
            'key': int(key),
            'lb': lb,
            'residual': res,
            'row_cands': row_cands,
        })
        by_res[res] = by_res.get(res, 0) + 1
    
    elapsed = time.time() - t0
    return {
        'constraints': constraints,
        'by_residual': dict(sorted(by_res.items())),
        'total': len(constraints),
        'impossible': impossible,
        'scan_sec': round(elapsed, 1),
    }


def build_complete_cnf(survivors: List[int], target: int, constraints: list,
                       max_clause_residual: int) -> Tuple[List[List[int]], int, dict]:
    """Build CNF from precomputed constraints."""
    var_map = {h: i + 1 for i, h in enumerate(survivors)}
    top_id = len(var_map)
    clauses: List[List[int]] = []
    provenance = []
    
    # Residual-0: unit clauses (vertex exclusions)
    # Residual-1: binary clauses (edge exclusions)
    # Residual-r: (r+1)-ary clauses
    for c in constraints:
        res = c['residual']
        if res > max_clause_residual:
            continue
        row_lits = [var_map[p] for p in c['row_cands'] if p in var_map]
        n_clauses = comb(len(row_lits), res + 1)
        if n_clauses > 500000:  # Safety: skip enormous rows
            continue
        for subset in combinations(row_lits, res + 1):
            clauses.append([-x for x in subset])
        provenance.append({
            'key': c['key'],
            'lb': c['lb'],
            'residual': res,
            'row_size': len(c['row_cands']),
            'clauses_added': n_clauses,
        })
    
    occupation_clauses = len(clauses)
    
    # Cardinality constraints
    al, top_id = atleast_pysat(list(var_map.values()), target, top_id)
    clauses.extend(al)
    am, top_id = atmost_pysat(list(var_map.values()), target, top_id)
    clauses.extend(am)
    
    meta = {
        'survivor_count': len(survivors),
        'target': target,
        'occupation_clauses': occupation_clauses,
        'cardinality_clauses': len(al) + len(am),
        'total_clauses': len(clauses),
        'total_variables': top_id,
        'provenance_rows': len(provenance),
    }
    return clauses, top_id, meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--branch', choices=['matching', 'rep2'], required=True)
    ap.add_argument('--strata', default='workspace/data/matching_strata/anchored_matching_strata.json')
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--indices', default='')
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--max-residual', type=int, default=3, help='maximum Wang-row residual to encode')
    ap.add_argument('--solve-time', type=int, default=600)
    ap.add_argument('--drat-time', type=int, default=900)
    args = ap.parse_args()

    out_root = pathlib.Path(args.out_dir)
    out_root.mkdir(parents=True, exist_ok=True)
    
    print(f'Loading LUT from {args.lut}...')
    lut = load_lut(pathlib.Path(args.lut))
    print(f'  {len(lut):,} rows')

    # Determine branch
    if args.branch == 'matching':
        wanted = {int(x) for x in args.indices.split(',') if x.strip()}
        strata = []
        for idx, st in iter_strata(pathlib.Path(args.strata), 0):
            if idx in wanted:
                st = dict(st)
                st['_idx'] = int(idx)
                strata.append(st)
        
        for st in strata:
            idx = int(st['_idx'])
            prefix = [int(x) for x in st['canonical']]
            r1 = rank1_points()
            hr_list = sorted(m for m in range(1, 512) if m not in r1)
            hr_set = set(hr_list)
            info = process_stratum(lut, prefix, hr_set, hr_list)
            survivors = [int(x) for x in info['survivors']]
            target = int(info['target'])
            
            out_dir = out_root / f'idx{idx:03d}'
            out_dir.mkdir(parents=True, exist_ok=True)
            
            print(f'\n=== idx={idx} k={st["k"]} survivors={len(survivors)} target={target} ===')
            
            if info.get('impossible_rows'):
                print('  IMPOSSIBLE from fixed-prefix row')
                continue
            
            print(f'  Precomputing constraints (max_residual={args.max_residual})...')
            pc = precompute_constraints(lut, prefix, survivors, args.max_residual)
            print(f'  {pc["total"]} constraints in {pc["scan_sec"]}s: {pc["by_residual"]}')
            
            print(f'  Building complete CNF...')
            clauses, top_id, meta = build_complete_cnf(survivors, target, pc['constraints'], args.max_residual)
            print(f'  {meta["total_clauses"]} clauses, {meta["total_variables"]} variables')
            print(f'  Occupation: {meta["occupation_clauses"]}, Cardinality: {meta["cardinality_clauses"]}')
            
            cnf_path = out_dir / 'complete.cnf'
            write_cnf(clauses, top_id, cnf_path)
            
            print(f'  Solving with CaDiCaL (timeout={args.solve_time}s)...')
            sol = run_cadical(cnf_path, args.solve_time, with_drat=True)
            print(f'  Result: {"UNSAT" if sol["unsat"] else "SAT" if sol["sat"] else "UNKNOWN"} in {sol["elapsed_sec"]:.1f}s')
            
            result = {
                'schema': 'complete_encoding_v1',
                'idx': idx,
                'k': int(st['k']),
                'prefix': prefix,
                'survivor_count': len(survivors),
                'target': target,
                'max_residual': args.max_residual,
                'precompute': {k: v for k, v in pc.items() if k != 'constraints'},
                'encoding': meta,
                'cadical_exit': sol['exit'],
                'cadical_sec': round(sol['elapsed_sec'], 2),
                'cnf': str(cnf_path),
                'cnf_sha256': sha256_file(cnf_path),
            }
            
            if sol['unsat'] and sol.get('drat'):
                print(f'  Verifying DRAT...')
                trim = run_drat_trim(cnf_path, pathlib.Path(sol['drat']), args.drat_time)
                result['drat'] = sol['drat']
                result['drat_sha256'] = sha256_file(pathlib.Path(sol['drat']))
                result['drat_trim'] = trim
                result['status'] = 'UNSAT_DRAT_VERIFIED' if trim['verified'] else 'UNSAT_DRAT_UNVERIFIED'
                print(f'  DRAT: {"VERIFIED" if trim["verified"] else "NOT VERIFIED"} in {trim["elapsed_sec"]:.1f}s')
            elif sol['unsat']:
                result['status'] = 'UNSAT_NO_PROOF'
            elif sol['sat']:
                result['status'] = 'SAT_RELAXATION'
            else:
                result['status'] = 'UNKNOWN'
            
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
            print(f'  Status: {result["status"]}')

    elif args.branch == 'rep2':
        prefix = [1, 2]
        candidates = sorted(m for m in range(1, 512) if m not in set(prefix))
        info = process_rep2(lut, prefix, candidates)
        survivors = [int(x) for x in info['survivors']]
        target = int(info['target'])
        
        out_dir = out_root / 'rep2'
        out_dir.mkdir(parents=True, exist_ok=True)
        
        print(f'\n=== rep2 survivors={len(survivors)} target={target} ===')
        
        print(f'  Precomputing constraints (max_residual={args.max_residual})...')
        pc = precompute_constraints(lut, prefix, survivors, args.max_residual)
        print(f'  {pc["total"]} constraints in {pc["scan_sec"]}s: {pc["by_residual"]}')
        
        print(f'  Building complete CNF...')
        clauses, top_id, meta = build_complete_cnf(survivors, target, pc['constraints'], args.max_residual)
        print(f'  {meta["total_clauses"]} clauses, {meta["total_variables"]} variables')
        
        cnf_path = out_dir / 'complete.cnf'
        write_cnf(clauses, top_id, cnf_path)
        
        print(f'  Solving (timeout={args.solve_time}s)...')
        sol = run_cadical(cnf_path, args.solve_time, with_drat=True)
        sn = 'UNSAT' if sol['unsat'] else 'SAT' if sol['sat'] else 'UNKNOWN'
        print(f'  Result: {sn} in {sol["elapsed_sec"]:.1f}s')
        
        result = {
            'schema': 'complete_encoding_v1',
            'branch': 'rep2',
            'prefix': prefix,
            'survivor_count': len(survivors),
            'target': target,
            'max_residual': args.max_residual,
            'precompute': {k: v for k, v in pc.items() if k != 'constraints'},
            'encoding': meta,
            'cadical_exit': sol['exit'],
            'cadical_sec': round(sol['elapsed_sec'], 2),
        }
        
        if sol['unsat'] and sol.get('drat'):
            trim = run_drat_trim(cnf_path, pathlib.Path(sol['drat']), args.drat_time)
            result.update({'drat': sol['drat'], 'drat_trim': trim,
                          'status': 'UNSAT_DRAT_VERIFIED' if trim['verified'] else 'UNSAT_DRAT_UNVERIFIED'})
        elif sol['unsat']:
            result['status'] = 'UNSAT_NO_PROOF'
        elif sol['sat']:
            result['status'] = 'SAT_RELAXATION'
        else:
            result['status'] = 'UNKNOWN'
        
        (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
        print(f'  Status: {result["status"]}')

if __name__ == '__main__':
    main()
