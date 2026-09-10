#!/usr/bin/env python3
"""Rank-1 skeleton solver with fixed higher-rank prefix and branch exclusions.

This extends the exact-18 rank1 skeleton tool to the remaining fixed-E11
middle branches.  It fixes some rank-1 points and higher-rank points, restricts
all selected higher-rank points to the branch universe (for example the rep2 or
rep16 second-orbit branch after excluding earlier second orbits), and compresses
the complete Wang LUT to inequalities on the 49 rank-1 variables after subtracting
fixed higher-rank occupancy and worst-case/free branch higher-rank variables.

For the current use we normally fix all higher-rank points of a saved candidate;
then the solver asks whether any rank-1 skeleton can complete that high prefix
while satisfying the complete A-side Wang occupation table.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_cnf_e11_fixed import E11, stab_e11_orbits  # noqa: E402
from wang_capacity_lazy import in_rowspace, matrix_rank_of_mask, unpack_basis, subspace_points_from_basis  # noqa: E402


def parse_ints(spec: str) -> list[int]:
    return [int(x) for x in spec.replace(';', ',').split(',') if x.strip()]


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def rank1_points() -> list[int]:
    pts = [p for p in range(1, 512) if matrix_rank_of_mask(p) == 1]
    if len(pts) != 49:
        raise RuntimeError(f'expected 49 rank-1 points, got {len(pts)}')
    return pts


def parent_exclusions_for_second(second_rep: int | None) -> set[int]:
    if second_rep is None or second_rep == E11:
        return set()
    excluded = set()
    found = False
    for orb in stab_e11_orbits():
        if orb['rep'] == second_rep:
            found = True
            break
        excluded.update(int(p) for p in orb['members'])
    if not found:
        raise ValueError(f'{second_rep} is not a Stab(E11) representative')
    excluded.discard(E11)
    excluded.discard(second_rep)
    return excluded


def solve(lut, meta, *, rank_s: int, fixed_rank1: Sequence[int], fixed_high: Sequence[int],
          second_rep: int | None, exact_rank1_count: int, time_limit: float, workers: int):
    from ortools.sat.python import cp_model
    t0 = time.time()
    r1_pts = rank1_points()
    r1_index = {p: i for i, p in enumerate(r1_pts)}
    fixed_rank1 = [int(p) for p in fixed_rank1]
    fixed_high = [int(p) for p in fixed_high]
    fixed_high_set = set(fixed_high)
    parent_excluded = parent_exclusions_for_second(second_rep)
    bad_fixed_high = sorted(p for p in fixed_high if p in parent_excluded or matrix_rank_of_mask(p) == 1)
    if bad_fixed_high:
        raise ValueError(f'fixed_high outside branch or rank1: {bad_fixed_high}')
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x_{p}') for p in r1_pts]
    model.Add(sum(x) == exact_rank1_count)
    for p in fixed_rank1:
        if p not in r1_index:
            model.AddBoolOr([])
        else:
            model.Add(x[r1_index[p]] == 1)
    # The second-orbit branch excludes earlier rank-1 points if any; force them out
    # of the rank-1 skeleton so this compressed model matches the branch universe.
    excluded_rank1 = sorted(p for p in parent_excluded if p in r1_index and p not in fixed_rank1)
    for p in excluded_rank1:
        model.Add(x[r1_index[p]] == 0)

    tight: dict[int, int] = {}
    witness: dict[int, dict] = {}
    raw_by_dim = Counter()
    raw_by_lb = Counter()
    fixed_high_in_hist = Counter()
    fixed_rank1_in_hist = Counter()
    raw_residual_cap_hist = Counter()
    for idx0, (key, lb0) in enumerate(lut.items(), 1):
        basis = unpack_basis(int(key))
        rmask = 0
        high_in = 0
        fixed_r1_in = 0
        for p in subspace_points_from_basis(basis):
            j = r1_index.get(p)
            if j is not None:
                rmask |= 1 << j
            if p in fixed_high_set:
                high_in += 1
            if p in fixed_rank1:
                fixed_r1_in += 1
        cap = rank_s - int(lb0) - high_in
        old = tight.get(rmask)
        if old is None or cap < old:
            tight[rmask] = cap
            witness[rmask] = {'key': int(key), 'dim': int(key) & 0xF, 'lb': int(lb0),
                              'raw_cap': rank_s - int(lb0), 'fixed_high_in_row': high_in,
                              'fixed_rank1_in_row': fixed_r1_in, 'residual_cap': cap,
                              'basis': list(basis)}
        raw_by_dim[int(key) & 0xF] += 1
        raw_by_lb[int(lb0)] += 1
        fixed_high_in_hist[high_in] += 1
        fixed_rank1_in_hist[fixed_r1_in] += 1
        raw_residual_cap_hist[cap] += 1
        if idx0 % 1_000_000 == 0:
            print(f'compressed {idx0:,}/{len(lut):,}; distinct={len(tight):,}; elapsed={time.time()-t0:.1f}s', flush=True)

    cons = [(mask, cap, witness[mask]) for mask, cap in tight.items() if mask.bit_count() > cap]
    cons.sort(key=lambda t: (t[0].bit_count(), t[1], t[0]))
    row_hist = Counter()
    row_var_hist = Counter()
    cap_hist = Counter()
    added = 0
    skipped = 0
    empty = 0
    witness_head = []
    for mask, cap, wit in cons:
        inds = [i for i in range(len(r1_pts)) if (mask >> i) & 1]
        row_hist[(len(inds), int(cap))] += 1
        row_var_hist[len(inds)] += 1
        cap_hist[int(cap)] += 1
        if cap < 0:
            model.AddBoolOr([])
            added += 1
            empty += 1
        elif len(inds) <= cap:
            skipped += 1
        else:
            model.Add(sum(x[i] for i in inds) <= int(cap))
            added += 1
        if len(witness_head) < 80:
            w = dict(wit)
            w['intersection_size'] = len(inds)
            w['cap'] = int(cap)
            witness_head.append(w)
    build_elapsed = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = workers
    t1 = time.time()
    st = solver.Solve(model)
    solve_elapsed = time.time() - t1
    status = solver.StatusName(st)
    sol = None
    if status in ('OPTIMAL', 'FEASIBLE'):
        sol = [r1_pts[i] for i in range(len(r1_pts)) if solver.Value(x[i])]
    return {
        'problem': 'complete-LUT rank-1 skeleton with fixed high prefix and second-orbit branch exclusions',
        'field': 'F2',
        'rank_s_for_capacities': rank_s,
        'second_rep': second_rep,
        'fixed_rank1_points': fixed_rank1,
        'fixed_high_points': fixed_high,
        'fixed_high_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in fixed_high).items())),
        'exact_rank1_count': exact_rank1_count,
        'excluded_rank1_points_from_parent_branch': excluded_rank1,
        'rank1_points': r1_pts,
        'compression': {
            'compressed_intersections': len(tight),
            'nonvacuous_constraints': len(cons),
            'constraint_size_cap_hist': {f'{a},{b}': c for (a, b), c in sorted(row_hist.items())},
            'raw_by_dim': dict(sorted(raw_by_dim.items())),
            'raw_by_lb': dict(sorted(raw_by_lb.items())),
            'fixed_high_in_row_hist': dict(sorted(fixed_high_in_hist.items())),
            'fixed_rank1_in_row_hist': dict(sorted(fixed_rank1_in_hist.items())),
            'raw_residual_cap_hist': dict(sorted(raw_residual_cap_hist.items())),
        },
        'rows_added': added,
        'skipped_vacuous': skipped,
        'empty_rows': empty,
        'row_var_hist': dict(sorted(row_var_hist.items())),
        'cap_hist': dict(sorted(cap_hist.items())),
        'witness_head': witness_head,
        'solver_status': status,
        'solver_status_code': int(st),
        'solver_walltime': float(solver.WallTime()),
        'solver_num_conflicts': int(solver.NumConflicts()),
        'solver_num_branches': int(solver.NumBranches()),
        'build_elapsed_sec': build_elapsed,
        'solve_elapsed_sec': solve_elapsed,
        'support_rank1': sol,
        'support_rank1_size': None if sol is None else len(sol),
        'support_all_fixed_prefix': None if sol is None else sorted(list(sol) + list(fixed_high)),
        'support_all_size_with_fixed_high': None if sol is None else len(sol) + len(fixed_high),
        'support_rank_hist': None if sol is None else dict(sorted(Counter(matrix_rank_of_mask(p) for p in sorted(list(sol) + list(fixed_high))).items())),
        'lut_meta_brief': {'coverage_ok': meta.get('coverage_ok'), 'conflict_count': meta.get('conflict_count'), 'subspace_count': meta.get('subspace_count')},
        'meaning': 'SAT/OPTIMAL is a complete-LUT A-support with this fixed high prefix; INFEASIBLE is a strong full-Wang exclusion of this high-prefix slice but still needs CNF/DRAT if used formally.',
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank-s', type=int, default=20)
    ap.add_argument('--fixed-rank1', default='1')
    ap.add_argument('--fixed-high', required=True)
    ap.add_argument('--second-rep', type=int, default=None)
    ap.add_argument('--exact-rank1-count', type=int, required=True)
    ap.add_argument('--time-limit', type=float, default=300)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    fixed_rank1 = parse_ints(args.fixed_rank1)
    fixed_high = parse_ints(args.fixed_high)
    lut, meta = load_lut(args.lut)
    print(f'loaded LUT {len(lut):,} coverage={meta.get("coverage_ok")} conflicts={meta.get("conflict_count")} fixed_rank1={fixed_rank1} fixed_high={fixed_high} second_rep={args.second_rep}', flush=True)
    res = solve(lut, meta, rank_s=args.rank_s, fixed_rank1=fixed_rank1, fixed_high=fixed_high,
                second_rep=args.second_rep, exact_rank1_count=args.exact_rank1_count,
                time_limit=args.time_limit, workers=args.workers)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(res, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: res[k] for k in ['solver_status','support_rank1_size','support_all_size_with_fixed_high','support_rank_hist','fixed_rank1_points','fixed_high_points','rows_added','build_elapsed_sec','solve_elapsed_sec']}, indent=2, sort_keys=True))
    print('saved', args.out)


if __name__ == '__main__':
    main()
