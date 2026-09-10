#!/usr/bin/env python3
"""Iterative model-driven separation for the adjacent-pair (rep2) branch.

Adapts iterative_separation.py for the rep2 case where:
- Fixed prefix: {E11=1, E12=2}
- Candidates: ALL 509 nonzero masks except E11 and E12
- Target: 18
"""
import argparse
import json
import pathlib
import pickle
import subprocess
import sys
import time
from collections import defaultdict
from itertools import combinations
from math import comb
from typing import Dict, List, Optional, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from wang_capacity_lazy import unpack_basis, subspace_points_from_basis  # noqa:E402
from graph_coloring_certificate import load_lut, make_pivot_dict, in_span_piv  # noqa:E402

MAX_CLAUSE_PER_CONSTRAINT = 20


def atmost_direct(lits, bound):
    if bound < 0: return [[]]
    if bound >= len(lits): return []
    if bound == 0: return [[-x] for x in lits]
    return [[-x for x in subset] for subset in combinations(lits, bound + 1)]


def atleast_pysat(lits, bound, top_id):
    from pysat.card import CardEnc, EncType
    if bound <= 0: return [], top_id
    if bound > len(lits): return [[]], top_id
    enc = CardEnc.atleast(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
    return [list(cl) for cl in enc.clauses], enc.nv


def atmost_pysat(lits, bound, top_id):
    from pysat.card import CardEnc, EncType
    if bound >= len(lits): return [], top_id
    if bound < 0: return [[]], top_id
    if bound == 0: return [[-x] for x in lits], top_id
    enc = CardEnc.atmost(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
    return [list(cl) for cl in enc.clauses], enc.nv


def process_rep2(lut, prefix, candidates):
    """Compute residual-0/1 graph for prefix + candidates."""
    cand_set = set(candidates)
    k = len(prefix)
    target = 20 - k
    lb_min = max(20 - k - 1, 0)

    vertex_key = {}
    edge_key = {}
    impossible = []

    for key, lb in lut.items():
        lb = int(lb)
        cap = 20 - lb
        if lb < lb_min:
            continue
        needed = cap - 1
        if needed > k:
            continue

        basis = unpack_basis(int(key))
        piv = make_pivot_dict(basis)
        cnt = sum(1 for p in prefix if in_span_piv(piv, int(p)))
        residual = cap - cnt

        if residual < 0:
            impossible.append({'key': int(key), 'lb': lb, 'cap': cap, 'cnt': cnt})
            continue

        pts = [int(x) for x in subspace_points_from_basis(basis) if int(x) in cand_set]
        if residual == 0:
            for h in pts:
                vertex_key.setdefault(h, int(key))
        elif residual == 1:
            for i, a in enumerate(pts):
                for b in pts[i+1:]:
                    x, y = (min(a,b), max(a,b))
                    edge_key.setdefault((x,y), int(key))

    survivors = [c for c in candidates if c not in vertex_key]
    ss = set(survivors)
    surv_edges = {p: key for p, key in edge_key.items() if p[0] in ss and p[1] in ss}
    return {
        'target': target, 'impossible_rows': impossible,
        'vertex_key': vertex_key, 'survivors': survivors,
        'edge_key': surv_edges,
    }


def build_base_cnf(info):
    survivors = [int(x) for x in info['survivors']]
    target = int(info['target'])
    var_map = {h: i+1 for i, h in enumerate(survivors)}
    top_id = len(var_map)
    clauses = []
    for (a,b) in sorted(info['edge_key']):
        if a in var_map and b in var_map:
            clauses.append([-var_map[a], -var_map[b]])
    al, top_id = atleast_pysat(list(var_map.values()), target, top_id)
    clauses.extend(al)
    am, top_id = atmost_pysat(list(var_map.values()), target, top_id)
    clauses.extend(am)
    return clauses, var_map, top_id


def write_cnf(clauses, top_id, path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('w') as f:
        f.write(f'p cnf {top_id} {len(clauses)}\n')
        for cl in clauses:
            f.write(' '.join(map(str, cl)) + ' 0\n')


def parse_model(log_path, var_map):
    inv = {v: p for p, v in var_map.items()}
    text = log_path.read_text(errors='ignore')
    selected = []
    for line in text.splitlines():
        if line.startswith('v '):
            for tok in line.split()[1:]:
                try:
                    lit = int(tok)
                except ValueError:
                    continue
                if lit > 0 and lit in inv:
                    selected.append(inv[lit])
    return sorted(selected) if selected else None


def full_lut_violations(lut, prefix, selected, survivors):
    support = set(prefix) | set(selected)
    for key, lb in lut.items():
        cap = 20 - int(lb)
        if cap >= len(support): continue
        basis = unpack_basis(int(key))
        piv = make_pivot_dict(basis)
        cnt = sum(1 for p in support if in_span_piv(piv, int(p)))
        if cnt > cap:
            m_cnt = sum(1 for p in prefix if in_span_piv(piv, int(p)))
            residual = cap - m_cnt
            surv_in = tuple(sorted(s for s in survivors if in_span_piv(piv, int(s))))
            sel_in = sum(1 for s in selected if in_span_piv(piv, int(s)))
            yield {
                'key': int(key), 'lb': int(lb), 'cap': int(cap),
                'residual': int(residual), 'surv_mask': surv_in,
                'sel_count': int(sel_in), 'excess': int(sel_in - residual),
            }


def run_cadical(cnf_path, timeout, with_drat=False):
    drat_path = cnf_path.with_suffix('.drat') if with_drat else None
    log_path = cnf_path.with_suffix('.cadical.log')
    cmd = ['cadical']
    if timeout > 0: cmd += ['-t', str(timeout)]
    cmd.append(str(cnf_path))
    if with_drat: cmd.append(str(drat_path))
    t0 = time.time()
    with log_path.open('w') as f:
        subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, text=True)
    text = log_path.read_text(errors='ignore')
    rc = 10 if 'SATISFIABLE' in text and 'UNSATISFIABLE' not in text else (20 if 'UNSATISFIABLE' in text else 0)
    return {
        'exit': rc, 'elapsed_sec': time.time()-t0,
        'unsat': rc == 20, 'sat': rc == 10,
        'log': str(log_path), 'drat': str(drat_path) if drat_path else None,
        'has_model': 'v ' in text and rc == 10,
    }


def run_drat_trim(cnf_path, drat_path, timeout):
    log_path = cnf_path.with_suffix('.drat_trim.log')
    t0 = time.time()
    try:
        with log_path.open('w') as f:
            subprocess.run(['drat-trim', str(cnf_path), str(drat_path)],
                          stdout=f, stderr=subprocess.STDOUT, text=True, timeout=timeout)
        text = log_path.read_text(errors='ignore')
        return {'exit': 0, 'elapsed_sec': time.time()-t0, 'verified': 'VERIFIED' in text}
    except subprocess.TimeoutExpired:
        return {'exit': None, 'elapsed_sec': timeout, 'verified': False, 'timeout': True}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--max-rounds', type=int, default=200)
    ap.add_argument('--solve-time', type=int, default=300)
    ap.add_argument('--drat-time', type=int, default=900)
    args = ap.parse_args()

    out_dir = pathlib.Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    prefix = [1, 2]  # E11, E12
    candidates = sorted(m for m in range(1, 512) if m not in set(prefix))

    print(f'Loading LUT from {args.lut}...')
    lut = load_lut(pathlib.Path(args.lut))
    print(f'  {len(lut):,} entries')

    print(f'Processing rep2 prefix {prefix}...')
    t0 = time.time()
    info = process_rep2(lut, prefix, candidates)
    print(f'  survivors={len(info["survivors"])}, target={info["target"]}, edges={len(info["edge_key"])}')
    print(f'  impossible={len(info["impossible_rows"])}, vex={len(info["vertex_key"])}, {time.time()-t0:.1f}s')

    if info['impossible_rows']:
        result = {'status': 'PREFIX_VIOLATES', 'row': info['impossible_rows'][0]}
        (out_dir / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result, sort_keys=True))
        return

    base_clauses, var_map, base_top = build_base_cnf(info)
    survivors = [int(x) for x in info['survivors']]

    clauses = list(base_clauses)
    top = base_top
    known = {}
    added = []
    round_log = []

    for rnd in range(args.max_rounds):
        t0 = time.time()
        cnf_path = out_dir / f'rep2_round{rnd:03d}.cnf'
        write_cnf(clauses, top, cnf_path)
        sol = run_cadical(cnf_path, args.solve_time, with_drat=False)
        ri = {'round': rnd, 'clauses': len(clauses), 'variables': top,
              'cadical_sec': round(sol['elapsed_sec'], 2)}

        if sol['unsat']:
            ri['result'] = 'UNSAT'
            round_log.append(ri)
            print(f'  Rnd {rnd}: UNSAT in {sol["elapsed_sec"]:.1f}s')
            # Re-solve with DRAT
            drat_cnf = out_dir / 'rep2_final.cnf'
            write_cnf(clauses, top, drat_cnf)
            drat_sol = run_cadical(drat_cnf, args.solve_time * 5, with_drat=True)
            trim = {'verified': False}
            if drat_sol['unsat'] and drat_sol['drat']:
                trim = run_drat_trim(drat_cnf, pathlib.Path(drat_sol['drat']), args.drat_time)
            result = {
                'status': 'UNSAT', 'rounds': rnd+1, 'final_clauses': len(clauses),
                'final_variables': top, 'constraints_added': len(added),
                'drat_verified': trim.get('verified', False),
                'round_log': round_log,
            }
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
            print(json.dumps({k: result[k] for k in ['status','rounds','drat_verified','final_clauses']}, sort_keys=True))
            return

        if not sol['sat'] or not sol['has_model']:
            ri['result'] = 'UNKNOWN'
            round_log.append(ri)
            result = {'status': 'SOLVER_UNKNOWN', 'rounds': rnd+1, 'round_log': round_log}
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
            print(json.dumps(result, sort_keys=True))
            return

        selected = parse_model(pathlib.Path(sol['log']), var_map)
        if not selected or len(selected) < info['target']:
            ri['result'] = f'BAD_MODEL_{len(selected) if selected else 0}'
            round_log.append(ri)
            result = {'status': 'BAD_MODEL', 'rounds': rnd+1, 'round_log': round_log}
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
            return

        violations = list(full_lut_violations(lut, prefix, selected, survivors))
        violations.sort(key=lambda v: (v['residual'], len(v['surv_mask'])))
        ri['violations'] = len(violations)
        ri['max_excess'] = max((v['excess'] for v in violations), default=0)

        if not violations:
            ri['result'] = 'LUT_ADMISSIBLE'
            round_log.append(ri)
            support = sorted(set(prefix) | set(selected))
            result = {
                'status': 'LUT_ADMISSIBLE_SUPPORT_FOUND', 'support': support,
                'support_size': len(support), 'selected': selected,
                'rounds': rnd+1, 'round_log': round_log,
            }
            (out_dir / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
            print(f'*** LUT-ADMISSIBLE SUPPORT FOUND: {support}')
            return

        new_count = 0
        new_cls = 0
        for v in violations:
            mask = v['surv_mask']
            res = v['residual']
            if len(mask) <= res: continue
            if mask in known and known[mask] <= res: continue
            lits = [var_map[s] for s in mask if s in var_map]
            if len(lits) <= res: continue
            nc = comb(len(lits), res + 1)
            if nc > MAX_CLAUSE_PER_CONSTRAINT: continue
            known[mask] = res
            new = atmost_direct(lits, res)
            clauses.extend(new)
            new_cls += len(new)
            added.append({'key': v['key'], 'residual': res, 'mask_size': len(mask), 'round': rnd})
            new_count += 1

        ri['new'] = new_count
        ri['new_clauses'] = new_cls
        ri['result'] = 'SAT_SEPARATED'
        ri['sec'] = round(time.time()-t0, 1)
        round_log.append(ri)
        print(f'  Rnd {rnd}: {len(violations)} viols, {new_count} added ({new_cls} cls), '
              f'total={len(clauses)} cls, {time.time()-t0:.1f}s')

    result = {'status': 'MAX_ROUNDS', 'rounds': args.max_rounds,
              'final_clauses': len(clauses), 'constraints_added': len(added),
              'round_log': round_log}
    (out_dir / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
