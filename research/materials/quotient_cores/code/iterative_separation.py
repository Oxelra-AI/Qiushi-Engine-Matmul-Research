#!/usr/bin/env python3
r"""Iterative model-driven separation for fixed-matching Wang strata.

For strata where residual-0/1 graph constraints are insufficient (graph CNF is
SAT), this script iterates:

  1. Solve current CNF (initially base graph from residual-0/1).
  2. If UNSAT → done (re-run with DRAT for certification).
  3. Decode SAT model → selected HR points.
  4. Scan full Wang LUT for violated rows.
  5. If no violations → LUT-admissible support found! (save and exit)
  6. Add violated rows as at-most constraints and re-solve.

Encoding: at-most-r on m survivor variables uses direct encoding (all negated
(r+1)-subsets) when C(m,r+1) is small (no auxiliary variables).  For large
constraints, PySAT sequential counter is used with disjoint auxiliary ranges.
"""
import argparse
import hashlib
import json
import pathlib
import pickle
import subprocess
import sys
import time
from collections import defaultdict
from itertools import combinations
from math import comb
from typing import Dict, List, Optional, Sequence, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from wang_capacity_lazy import unpack_basis, subspace_points_from_basis  # noqa:E402
from graph_coloring_certificate import (  # noqa:E402
    rank1_points, load_lut, iter_strata, process_stratum,
    make_pivot_dict, in_span_piv,
)


# ---- Encoding helpers -------------------------------------------------------

MAX_DIRECT_CLAUSES = 5000  # per constraint: use direct encoding if C(m,r+1) <= this
MAX_CLAUSE_PER_CONSTRAINT = 20  # skip constraints exceeding this clause count


def atmost_direct(lits: List[int], bound: int) -> List[List[int]]:
    """Direct encoding: forbid every (bound+1)-subset from all being true.
    No auxiliary variables needed.
    """
    if bound < 0:
        return [[]]  # contradiction
    if bound >= len(lits):
        return []  # vacuous
    if bound == 0:
        return [[-x] for x in lits]
    return [[-x for x in subset] for subset in combinations(lits, bound + 1)]


def atmost_pysat(lits: List[int], bound: int, top_id: int) -> Tuple[List[List[int]], int]:
    """PySAT sequential counter for at-most-bound. Returns (clauses, new_top_id)."""
    from pysat.card import CardEnc, EncType
    n = len(lits)
    if bound >= n:
        return [], top_id
    if bound < 0:
        return [[]], top_id
    if bound == 0:
        return [[-x] for x in lits], top_id
    enc = CardEnc.atmost(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
    return [list(cl) for cl in enc.clauses], enc.nv


def atleast_pysat(lits: List[int], bound: int, top_id: int) -> Tuple[List[List[int]], int]:
    """PySAT sequential counter for at-least-bound."""
    from pysat.card import CardEnc, EncType
    n = len(lits)
    if bound <= 0:
        return [], top_id
    if bound > n:
        return [[]], top_id
    enc = CardEnc.atleast(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
    return [list(cl) for cl in enc.clauses], enc.nv


def encode_atmost(lits: List[int], bound: int, top_id: int) -> Tuple[Optional[List[List[int]]], int]:
    """Choose best encoding for at-most constraint.
    Returns (clauses, new_top_id), or (None, top_id) if too expensive.
    Only uses direct encoding (no auxiliary variables) for proof cleanliness.
    """
    m = len(lits)
    if bound >= m:
        return [], top_id
    if bound < 0:
        return [[]], top_id
    if bound == 0:
        return [[-x] for x in lits], top_id
    nc = comb(m, bound + 1)
    if nc <= MAX_CLAUSE_PER_CONSTRAINT:
        return atmost_direct(lits, bound), top_id  # no aux vars
    else:
        return None, top_id  # too expensive, skip


# ---- CNF construction -------------------------------------------------------

def build_base_cnf(info: dict) -> Tuple[List[List[int]], Dict[int, int], int]:
    """Build base graph CNF from residual-0/1 info.
    Includes at-least-target AND at-most-target (exact cardinality)."""
    survivors = [int(x) for x in info['survivors']]
    target = int(info['target'])
    var_map = {h: i + 1 for i, h in enumerate(survivors)}
    top_id = len(var_map)

    clauses = []
    # Edge clauses from residual-1 rows
    for (a, b) in sorted(info['edge_key']):
        if a in var_map and b in var_map:
            clauses.append([-var_map[a], -var_map[b]])

    # At-least-target constraint (sequential counter)
    al_clauses, top_id = atleast_pysat(list(var_map.values()), target, top_id)
    clauses.extend(al_clauses)

    # At-most-target constraint (sequential counter, disjoint aux range)
    am_clauses, top_id = atmost_pysat(list(var_map.values()), target, top_id)
    clauses.extend(am_clauses)

    return clauses, var_map, top_id


def write_cnf(clauses: List[List[int]], top_id: int, path: pathlib.Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('w') as f:
        f.write(f'p cnf {top_id} {len(clauses)}\n')
        for cl in clauses:
            f.write(' '.join(map(str, cl)) + ' 0\n')


def parse_model_from_log(log_path: pathlib.Path, var_map: Dict[int, int]) -> Optional[List[int]]:
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


def full_lut_violations(lut: Dict[int, int], matching: List[int],
                        selected_hr: List[int], survivors: List[int]) -> List[dict]:
    """Scan full LUT for violated rows, returning violation records."""
    support = set(matching) | set(selected_hr)
    for key, lb in lut.items():
        cap = 20 - int(lb)
        if cap >= len(support):
            continue
        basis = unpack_basis(int(key))
        piv = make_pivot_dict(basis)
        cnt = sum(1 for p in support if in_span_piv(piv, int(p)))
        if cnt > cap:
            m_cnt = sum(1 for p in matching if in_span_piv(piv, int(p)))
            residual = cap - m_cnt
            surv_in_row = tuple(sorted(s for s in survivors if in_span_piv(piv, int(s))))
            sel_in_row = sum(1 for s in selected_hr if in_span_piv(piv, int(s)))
            yield {
                'key': int(key), 'lb': int(lb), 'cap': int(cap),
                'matching_count': int(m_cnt), 'residual': int(residual),
                'surv_mask': surv_in_row, 'sel_count': int(sel_in_row),
                'excess': int(sel_in_row - residual),
            }


def sha256_file(path: pathlib.Path) -> Optional[str]:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


# ---- Solver interface --------------------------------------------------------

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
    return {
        'exit': proc.returncode, 'elapsed_sec': elapsed,
        'unsat': proc.returncode == 20, 'sat': proc.returncode == 10,
        'log': str(log_path), 'drat': str(drat_path) if drat_path else None,
        'has_model': 'v ' in text and proc.returncode == 10,
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
        return {'exit': proc.returncode, 'elapsed_sec': elapsed,
                'verified': 'VERIFIED' in text, 'log': str(log_path)}
    except subprocess.TimeoutExpired:
        return {'exit': None, 'elapsed_sec': timeout, 'verified': False,
                'log': str(log_path), 'timeout': True}


# ---- Main iteration ----------------------------------------------------------

def iterate_separation(idx: int, st: dict, info: dict, lut: Dict[int, int],
                        var_map: Dict[int, int], out_dir: pathlib.Path,
                        max_rounds: int, solve_time: int, drat_time: int) -> dict:
    matching = [int(x) for x in st['canonical']]
    survivors = [int(x) for x in info['survivors']]
    target = int(info['target'])

    base_clauses, _, base_top = build_base_cnf(info)
    accumulated_clauses = list(base_clauses)
    current_top = base_top
    added_constraints = []  # provenance
    known_masks = {}  # mask_tuple -> best_bound

    round_log = []
    total_direct_clauses = 0
    total_aux_clauses = 0

    for rnd in range(max_rounds):
        t0 = time.time()
        cnf_path = out_dir / f'idx{idx:03d}_round{rnd:03d}.cnf'
        write_cnf(accumulated_clauses, current_top, cnf_path)

        sol = run_cadical(cnf_path, solve_time, with_drat=False)

        ri = {'round': rnd, 'clauses': len(accumulated_clauses),
              'variables': current_top, 'cadical_exit': sol['exit'],
              'cadical_sec': round(sol['elapsed_sec'], 2)}

        if sol['unsat']:
            ri['result'] = 'UNSAT'
            round_log.append(ri)

            # Re-solve with DRAT proof
            drat_cnf = out_dir / f'idx{idx:03d}_final.cnf'
            write_cnf(accumulated_clauses, current_top, drat_cnf)
            drat_sol = run_cadical(drat_cnf, solve_time * 5, with_drat=True)

            trim = {'verified': False, 'elapsed_sec': 0}
            if drat_sol['unsat'] and drat_sol['drat']:
                trim = run_drat_trim(drat_cnf, pathlib.Path(drat_sol['drat']), drat_time)

            by_res = defaultdict(int)
            for c in added_constraints:
                by_res[c['residual']] += 1

            return {
                'idx': idx, 'k': int(st['k']), 'matching': matching,
                'status': 'UNSAT', 'rounds': rnd + 1,
                'final_clauses': len(accumulated_clauses), 'final_variables': current_top,
                'constraints_added': len(added_constraints),
                'drat_verified': trim.get('verified', False),
                'drat_trim_sec': round(trim.get('elapsed_sec', 0), 2),
                'drat_cadical_sec': round(drat_sol.get('elapsed_sec', 0), 2),
                'final_cnf': str(drat_cnf),
                'final_cnf_sha256': sha256_file(drat_cnf),
                'drat_sha256': sha256_file(pathlib.Path(drat_sol['drat'])) if drat_sol.get('drat') else None,
                'round_log': round_log,
                'constraint_summary_by_residual': dict(sorted(by_res.items())),
            }

        if not sol['sat'] or not sol['has_model']:
            ri['result'] = 'UNKNOWN_OR_NO_MODEL'
            round_log.append(ri)
            return {
                'idx': idx, 'k': int(st['k']), 'matching': matching,
                'status': 'SOLVER_UNKNOWN', 'rounds': rnd + 1,
                'round_log': round_log,
            }

        # Decode model
        selected = parse_model_from_log(pathlib.Path(sol['log']), var_map)
        if not selected or len(selected) < target:
            ri['result'] = f'BAD_MODEL_size_{len(selected) if selected else 0}'
            round_log.append(ri)
            return {
                'idx': idx, 'k': int(st['k']), 'matching': matching,
                'status': 'BAD_MODEL', 'rounds': rnd + 1, 'round_log': round_log,
            }

        # Scan full LUT for violations
        violations = list(full_lut_violations(lut, matching, selected, survivors))
        violations.sort(key=lambda v: (v['residual'], len(v['surv_mask'])))

        ri['model_size'] = len(selected)
        ri['lut_violations'] = len(violations)
        ri['max_excess'] = max((v['excess'] for v in violations), default=0)

        if not violations:
            ri['result'] = 'LUT_ADMISSIBLE'
            round_log.append(ri)
            support = sorted(set(matching) | set(selected))
            return {
                'idx': idx, 'k': int(st['k']), 'matching': matching,
                'status': 'LUT_ADMISSIBLE_SUPPORT_FOUND',
                'support': support, 'support_size': len(support),
                'selected_hr': selected, 'rounds': rnd + 1,
                'round_log': round_log,
                'meaning': 'A 20-point A-support satisfying ALL Wang occupation inequalities was found. '
                           'This does NOT prove rank-20; B/C factors must still be solved.',
            }

        # Add violated rows as at-most constraints (only small direct encodings)
        new_count = 0
        skipped_count = 0
        new_clause_count = 0
        new_by_res = defaultdict(int)
        for v in violations:
            mask = v['surv_mask']
            residual = v['residual']
            if len(mask) <= residual:
                continue
            if mask in known_masks and known_masks[mask] <= residual:
                continue

            lits = [var_map[s] for s in mask if s in var_map]
            if len(lits) <= residual:
                continue

            am_clauses, new_top = encode_atmost(lits, residual, current_top)
            if am_clauses is None:
                skipped_count += 1
                continue
            known_masks[mask] = residual
            accumulated_clauses.extend(am_clauses)
            new_clause_count += len(am_clauses)
            current_top = new_top
            added_constraints.append({
                'key': v['key'], 'residual': residual, 'mask_size': len(mask), 'round': rnd,
            })
            new_count += 1
            new_by_res[residual] += 1

        ri['new_constraints'] = new_count
        ri['skipped_large'] = skipped_count
        ri['new_clauses'] = new_clause_count
        ri['new_by_residual'] = dict(sorted(new_by_res.items()))
        ri['result'] = 'SAT_SEPARATED'
        ri['elapsed_sec'] = round(time.time() - t0, 2)
        round_log.append(ri)

        print(f'  Rnd {rnd}: {len(violations)} viols, {new_count} added ({new_clause_count} cls), '
              f'{skipped_count} skipped, vars={current_top}, total_cls={len(accumulated_clauses)}, '
              f'{round(time.time()-t0, 1)}s')

    return {
        'idx': idx, 'k': int(st['k']), 'matching': matching,
        'status': 'MAX_ROUNDS', 'rounds': max_rounds,
        'final_clauses': len(accumulated_clauses), 'final_variables': current_top,
        'constraints_added': len(added_constraints), 'round_log': round_log,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--strata', default='workspace/data/matching_strata/anchored_matching_strata.json')
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--indices', required=True, help='comma-separated stratum indices')
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--max-rounds', type=int, default=100)
    ap.add_argument('--solve-time', type=int, default=300)
    ap.add_argument('--drat-time', type=int, default=600)
    args = ap.parse_args()

    out_dir = pathlib.Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    wanted = {int(x) for x in args.indices.replace(';', ',').split(',') if x.strip()}

    r1 = rank1_points()
    hr_list = sorted(m for m in range(1, 512) if m not in r1)
    hr_set = set(hr_list)

    strata = [(idx, st) for idx, st in iter_strata(pathlib.Path(args.strata), 0) if idx in wanted]

    print(f'Loading LUT from {args.lut}...')
    lut = load_lut(pathlib.Path(args.lut))
    print(f'  {len(lut):,} entries')

    results = []
    for idx, st in strata:
        matching = [int(x) for x in st['canonical']]
        print(f'\n=== idx={idx} k={st["k"]} matching={matching} ===')

        t0 = time.time()
        info = process_stratum(lut, matching, hr_set, hr_list)

        if info['impossible_rows']:
            res = {'idx': idx, 'k': int(st['k']), 'matching': matching,
                   'status': 'MATCHING_VIOLATES', 'rounds': 0}
            results.append(res)
            print(json.dumps(res, sort_keys=True))
            continue

        survivors = [int(x) for x in info['survivors']]
        target = int(info['target'])
        _, var_map, _ = build_base_cnf(info)

        print(f'  survivors={len(survivors)}, target={target}, edges={len(info["edge_key"])}')

        res = iterate_separation(idx, st, info, lut, var_map, out_dir,
                                  args.max_rounds, args.solve_time, args.drat_time)
        res['total_elapsed_sec'] = round(time.time() - t0, 2)
        results.append(res)

        compact = {k: res[k] for k in ['idx', 'k', 'matching', 'status', 'rounds',
                                         'total_elapsed_sec'] if k in res}
        if 'drat_verified' in res:
            compact['drat_verified'] = res['drat_verified']
        if 'final_clauses' in res:
            compact['final_clauses'] = res['final_clauses']
            compact['final_variables'] = res['final_variables']
        print(json.dumps(compact, sort_keys=True))

    summary = {'schema': 'iterative_separation_v1', 'records': results}
    summary_path = out_dir / 'summary.json'
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(f'\nSaved {summary_path}')


if __name__ == '__main__':
    main()
