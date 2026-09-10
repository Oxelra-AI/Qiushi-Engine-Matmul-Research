#!/usr/bin/env python3
"""Full rank-1 projected Wang occupation with fixed adjacent pair [1,2].

This is a 49-variable projection: any full length-20 Wang-admissible A-support
has a rank-1 subset satisfying every projected Wang inequality.  We fix the
adjacent pair [1,2] and optionally add the 98 transported ruling-line clauses
from the verified [1,2,3] local exclusion.  Maximizing the rank-1 subset size
under these necessary constraints can guide rep2 branching by rank-1 count.

CP-SAT optimality here is a small exact integer-program result over the projected
necessary system. It is not a full support exclusion unless converted to a proof
object and combined with the remaining higher-rank completion analysis.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys
import time
from collections import Counter
from typing import List, Sequence

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))

from rank1_capacity_profile import load_or_build  # noqa:E402
from ruling_line_transport import all_ruling_triples, simplify_ruling  # noqa:E402


def add_ruling_constraints(model, x, idx, fixed_points: set[int]) -> dict:
    rc = simplify_ruling(all_ruling_triples(), fixed_points)
    counts = {'unit': 0, 'binary': 0, 'ternary': 0, 'contradictions': int(rc['contradictions']), 'skipped': 0}
    for p in rc['unit']:
        if p in idx:
            model.Add(x[idx[p]] == 0)
            counts['unit'] += 1
        else:
            counts['skipped'] += 1
    for a, b in rc['binary']:
        if a in idx and b in idx:
            model.Add(x[idx[a]] + x[idx[b]] <= 1)
            counts['binary'] += 1
        else:
            counts['skipped'] += 1
    for a, b, c in rc['ternary']:
        if a in idx and b in idx and c in idx:
            model.Add(x[idx[a]] + x[idx[b]] + x[idx[c]] <= 2)
            counts['ternary'] += 1
        else:
            counts['skipped'] += 1
    return counts


def solve_projection(pts: List[int], cons, fixed: Sequence[int], add_ruling: bool, exact_size: int | None,
                     maximize: bool, time_limit: float, workers: int) -> dict:
    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x_{p}') for p in pts]
    idx = {int(p): i for i, p in enumerate(pts)}
    fixed = [int(p) for p in fixed]
    for p in fixed:
        if p not in idx:
            model.AddBoolOr([])
        else:
            model.Add(x[idx[p]] == 1)
    # Projected Wang inequalities.
    row_hist = Counter()
    for mask, cap, key in cons:
        inds = [i for i in range(len(pts)) if (int(mask) >> i) & 1]
        if len(inds) > int(cap):
            model.Add(sum(x[i] for i in inds) <= int(cap))
            row_hist[(len(inds), int(cap))] += 1
    ruling_counts = None
    if add_ruling:
        ruling_counts = add_ruling_constraints(model, x, idx, set(fixed))
    if exact_size is not None:
        model.Add(sum(x) == int(exact_size))
    if maximize:
        model.Maximize(sum(x))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = int(workers)
    t0 = time.time()
    st = solver.Solve(model)
    elapsed = time.time() - t0
    names = {
        cp_model.OPTIMAL: 'OPTIMAL',
        cp_model.FEASIBLE: 'FEASIBLE',
        cp_model.INFEASIBLE: 'INFEASIBLE',
        cp_model.UNKNOWN: 'UNKNOWN',
        cp_model.MODEL_INVALID: 'MODEL_INVALID',
    }
    sol = None
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = [int(pts[i]) for i in range(len(pts)) if solver.Value(x[i])]
    return {
        'status': names.get(st, str(st)),
        'status_code': int(st),
        'elapsed_sec': round(elapsed, 3),
        'wall_time': float(solver.WallTime()),
        'num_conflicts': int(solver.NumConflicts()),
        'num_branches': int(solver.NumBranches()),
        'objective_value': None if not maximize or sol is None else float(solver.ObjectiveValue()),
        'best_objective_bound': None if not maximize else float(solver.BestObjectiveBound()),
        'solution': sol,
        'solution_size': None if sol is None else len(sol),
        'solution_orbit_notes': None,
        'projected_constraint_hist': {f'{a},{b}': int(c) for (a, b), c in sorted(row_hist.items())},
        'projected_constraint_count': int(sum(row_hist.values())),
        'ruling_counts': ruling_counts,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=pathlib.Path, default=pathlib.Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--cache', type=pathlib.Path, default=pathlib.Path('data/wang_capacity_rank1_only_cnf/rank1_intersection_cache.pkl'))
    ap.add_argument('--rank-s', type=int, default=20)
    ap.add_argument('--fixed', default='1,2')
    ap.add_argument('--exact-size', type=int, default=None)
    ap.add_argument('--maximize', action='store_true')
    ap.add_argument('--with-ruling', action='store_true')
    ap.add_argument('--time-limit', type=float, default=300)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--out', type=pathlib.Path, required=True)
    args = ap.parse_args()

    fixed = [int(x) for x in args.fixed.replace(';', ',').split(',') if x.strip()]
    pts, cons, cmeta, lmeta = load_or_build(args.cache, args.lut, args.rank_s, False)
    res = solve_projection(pts, cons, fixed, args.with_ruling, args.exact_size, args.maximize, args.time_limit, args.workers)
    payload = {
        'schema': 'rank1_projection_with_pair_v1',
        'rank_s_for_capacities': args.rank_s,
        'fixed': fixed,
        'with_ruling': args.with_ruling,
        'exact_size': args.exact_size,
        'maximize': args.maximize,
        'rank1_points': pts,
        'compression': cmeta,
        'lut_meta_brief': {
            'coverage_ok': lmeta.get('coverage_ok'),
            'conflict_count': lmeta.get('conflict_count'),
            'subspace_count': lmeta.get('subspace_count'),
        },
        'result': res,
        'meaning': 'Necessary rank-1 projected Wang system with fixed adjacent pair. Bounds only the rank-1 subset of a full support; it does not settle higher-rank completion or full tensor rank.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: res[k] for k in ['status','objective_value','best_objective_bound','solution_size','elapsed_sec','num_conflicts','num_branches']}, sort_keys=True))
    print(f'Saved {args.out}')


if __name__ == '__main__':
    main()
