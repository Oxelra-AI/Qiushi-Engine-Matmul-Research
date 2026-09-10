#!/usr/bin/env python3
"""Find small projected Wang row families excluding fixed high prefixes.

For fixed higher-rank A-points H and exact K rank-1 points, the full Wang
occupation table compresses to rank-1 intersection masks with residual capacities.
This script tests filtered subsets of those compressed rows with CP-SAT so that
large all-row UNSAT runs can be replaced by smaller proof-producing CNFs.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, List, Sequence, Set, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_fixed_high_cnf import compress_for_fixed_high, load_lut, rank1_points, parse_ints  # noqa: E402
from wang_capacity_lazy import matrix_rank_of_mask  # noqa: E402


def parse_groups(spec: str) -> Set[Tuple[int, int]] | None:
    spec = spec.strip()
    if not spec:
        return None
    out: Set[Tuple[int, int]] = set()
    for part in spec.replace(';', ',').split(','):
        part = part.strip()
        if not part:
            continue
        if ':' in part:
            a, b = part.split(':', 1)
        elif '/' in part:
            a, b = part.split('/', 1)
        else:
            raise ValueError(f'bad group {part!r}')
        out.add((int(a), int(b)))
    return out


def filter_cons(cons, max_size: int | None = None, min_gap: int | None = None, groups: Set[Tuple[int,int]] | None = None):
    out = []
    for mask, cap, wit in cons:
        size = int(mask).bit_count(); cap = int(cap)
        if size <= cap:
            continue
        if groups is not None and (size, cap) not in groups:
            continue
        if groups is None and max_size is not None and size > max_size:
            continue
        if min_gap is not None and size - cap < min_gap:
            continue
        out.append((int(mask), cap, wit))
    return out


def solve_filtered(r1_pts: List[int], cons, exact_count: int, fixed_rank1: Sequence[int], time_limit: float, workers: int):
    from ortools.sat.python import cp_model
    t0 = time.time(); idx = {p: i for i, p in enumerate(r1_pts)}
    model = cp_model.CpModel(); x = [model.NewBoolVar(f'x_{p}') for p in r1_pts]
    model.Add(sum(x) == exact_count)
    for p in fixed_rank1:
        model.Add(x[idx[p]] == 1 if p in idx else False)
    hist = Counter(); row_var_hist = Counter(); cap_hist = Counter(); empty = 0; added = 0; witness_head = []
    for mask, cap, wit in cons:
        inds = [i for i in range(len(r1_pts)) if (int(mask) >> i) & 1]
        hist[(len(inds), int(cap))] += 1; row_var_hist[len(inds)] += 1; cap_hist[int(cap)] += 1
        if cap < 0:
            model.AddBoolOr([]); empty += 1; added += 1
        elif len(inds) > cap:
            model.Add(sum(x[i] for i in inds) <= int(cap)); added += 1
        if len(witness_head) < 40:
            w = dict(wit); w['intersection_size'] = len(inds); w['cap'] = int(cap); witness_head.append(w)
    build_elapsed = time.time() - t0
    solver = cp_model.CpSolver(); solver.parameters.max_time_in_seconds = time_limit; solver.parameters.num_search_workers = workers
    t1 = time.time(); st = solver.Solve(model); solve_elapsed = time.time() - t1
    names = {cp_model.OPTIMAL:'OPTIMAL', cp_model.FEASIBLE:'FEASIBLE', cp_model.INFEASIBLE:'INFEASIBLE', cp_model.UNKNOWN:'UNKNOWN', cp_model.MODEL_INVALID:'MODEL_INVALID'}
    sol = None
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = [r1_pts[i] for i in range(len(r1_pts)) if solver.Value(x[i])]
    return {
        'selected_constraint_count': len(cons),
        'selected_constraint_hist': {f'{a},{b}': c for (a,b),c in sorted(hist.items())},
        'rows_added': added, 'empty_rows': empty, 'row_var_hist': dict(sorted(row_var_hist.items())), 'cap_hist': dict(sorted(cap_hist.items())),
        'build_elapsed_sec': build_elapsed, 'solve_elapsed_sec': solve_elapsed,
        'solver_status': names.get(st, str(st)), 'solver_status_code': int(st), 'solver_walltime': float(solver.WallTime()), 'solver_num_conflicts': int(solver.NumConflicts()), 'solver_num_branches': int(solver.NumBranches()),
        'support_rank1': sol, 'support_rank1_size': None if sol is None else len(sol),
        'witness_head': witness_head,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank-s', type=int, default=20)
    ap.add_argument('--exact-rank1-count', type=int, default=18)
    ap.add_argument('--fixed-rank1', default='1')
    ap.add_argument('--fixed-high', required=True)
    ap.add_argument('--max-sizes', default='5,7,9,11,13,17,33,49')
    ap.add_argument('--include-groups', default='')
    ap.add_argument('--min-gap', type=int, default=None)
    ap.add_argument('--time-limit', type=float, default=60)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    fixed_rank1 = parse_ints(args.fixed_rank1); fixed_high = parse_ints(args.fixed_high)
    lut, lmeta = load_lut(args.lut); r1_pts = rank1_points()
    print(f'loaded LUT {len(lut):,}; fixed_high={fixed_high}', flush=True)
    cons, cmeta = compress_for_fixed_high(lut, args.rank_s, fixed_high, r1_pts)
    group_filter = parse_groups(args.include_groups)
    tests = []
    if group_filter is not None:
        tests.append({'name':'groups','max_size':None,'groups':group_filter})
    else:
        for x in args.max_sizes.replace(';', ',').split(','):
            x = x.strip()
            if x:
                tests.append({'name':f'maxsize{x}','max_size':int(x),'groups':None})
    records = []
    for t in tests:
        sub = filter_cons(cons, max_size=t['max_size'], min_gap=args.min_gap, groups=t['groups'])
        print(f"test {t['name']} selected={len(sub)}", flush=True)
        res = solve_filtered(r1_pts, sub, args.exact_rank1_count, fixed_rank1, args.time_limit, args.workers)
        res['test'] = {'name': t['name'], 'max_size': t['max_size'], 'groups': None if t['groups'] is None else sorted([list(g) for g in t['groups']]), 'min_gap': args.min_gap}
        records.append(res)
    payload = {
        'problem': 'fixed high rank-1 skeleton row-family ablation',
        'field': 'F2', 'rank_s_for_capacities': args.rank_s, 'exact_rank1_count': args.exact_rank1_count,
        'fixed_rank1_points': fixed_rank1, 'fixed_high_points': fixed_high,
        'fixed_high_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in fixed_high).items())),
        'compression': cmeta, 'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'records': records,
        'meaning': 'Small INFEASIBLE filtered systems identify CNF/DRAT targets; SAT supports are only rank-1 skeleton candidates under the fixed high prefix.'
    }
    args.out.parent.mkdir(parents=True, exist_ok=True); args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'statuses':[{'test':r['test']['name'],'selected':r['selected_constraint_count'],'status':r['solver_status'],'solve_elapsed_sec':r['solve_elapsed_sec']} for r in records], 'out':str(args.out)}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
