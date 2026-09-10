#!/usr/bin/env python3
"""Row-core extraction for fixed-E11/rep10 exact-rank1-count Wang branches.

This is a proof-target instrument, not a theorem.  It keeps the original
fixed-E11/rep10 branch universe (including all non-excluded higher-rank
variables), adds an exact total rank-1 count k, and selects a sound Wang row
family (default dim 1 plus rows of dims 4,6 through the fixed pair).  With one
assumption literal per non-vacuous Wang row, OR-Tools can return a smaller
sufficient row set.  The row set then becomes a much smaller CNF/DRAT target;
no CP-SAT result here is final proof evidence.
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

from wang_capacity_cnf_e11_fixed import E11, parse_dims, stab_e11_orbits  # noqa: E402
from wang_capacity_lazy import (  # noqa: E402
    in_rowspace,
    matrix_rank_of_mask,
    subspace_points_from_basis,
    unpack_basis,
)


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def parse_ints(spec: str) -> list[int]:
    if not spec.strip():
        return []
    return [int(x) for x in spec.replace(';', ',').split(',') if x.strip()]


def branch_points(fixed_extra: Sequence[int], exclude_second_orbits_before: bool):
    fixed = [E11] + [int(p) for p in fixed_extra if int(p) != E11]
    if len(set(fixed)) != len(fixed):
        raise ValueError(f'duplicate fixed point in {fixed}')
    excluded = set()
    if exclude_second_orbits_before:
        if len(fixed_extra) != 1:
            raise ValueError('exclude_second_orbits_before requires one fixed extra point')
        second = int(fixed_extra[0])
        found = False
        for orb in stab_e11_orbits():
            if int(orb['rep']) == second:
                found = True
                break
            excluded.update(int(p) for p in orb['members'])
        if not found:
            raise ValueError(f'{second} is not a Stab(E11) representative')
        for p in fixed:
            excluded.discard(p)
    pts = [p for p in range(1, 512) if p not in excluded]
    idx = {p: i for i, p in enumerate(pts)}
    for p in fixed:
        if p not in idx:
            raise ValueError(f'fixed point {p} excluded')
    return fixed, excluded, pts, idx


def row_contains_all(points: Sequence[int], basis: Sequence[int]) -> bool:
    return all(in_rowspace(int(p), basis, n=9) for p in points)


def collect_rows(lut: dict[int, int], *, rank_s: int, fixed: Sequence[int], pts: Sequence[int],
                 include_dims: set[int], through_fixed_dims: set[int]):
    fixed_set = set(fixed)
    pset = set(pts)
    rows = []
    selected = 0
    skipped = 0
    hist = Counter()
    src_hist = Counter()
    for key, lb0 in lut.items():
        d = int(key) & 0xF
        basis = None
        source = None
        if d in include_dims:
            source = 'include_dim'
        elif d in through_fixed_dims:
            basis = unpack_basis(key)
            if row_contains_all(fixed, basis):
                source = 'through_fixed'
        if source is None:
            continue
        selected += 1
        if basis is None:
            basis = unpack_basis(key)
        pts_in = subspace_points_from_basis(basis)
        cap = rank_s - int(lb0)
        fixed_in = sum(1 for p in fixed if p in pts_in)
        cap_rem = cap - fixed_in
        vars_pts = tuple(p for p in pts_in if p in pset and p not in fixed_set)
        rec = {
            'key': int(key),
            'dim': d,
            'lb': int(lb0),
            'raw_cap': cap,
            'fixed_in': fixed_in,
            'cap_rem': cap_rem,
            'var_count': len(vars_pts),
            'vars': vars_pts,
            'basis': tuple(int(b) for b in basis),
            'source': source,
        }
        hist[(d, int(lb0), cap_rem, len(vars_pts), source)] += 1
        src_hist[(source, d)] += 1
        if cap_rem < 0 or len(vars_pts) > cap_rem:
            rows.append(rec)
        else:
            skipped += 1
    return rows, {
        'selected_rows_total': selected,
        'active_rows': len(rows),
        'skipped_vacuous': skipped,
        'row_signature_hist': {str(k): v for k, v in sorted(hist.items())},
        'source_by_dim': {f'{s},{d}': c for (s, d), c in sorted(src_hist.items())},
    }


def solve_with_assumptions(rows: Sequence[dict], *, pts: Sequence[int], idx: dict[int, int],
                           fixed: Sequence[int], rank_s: int, exact_rank1_count: int | None,
                           time_limit: float, workers: int, use_assumptions: bool):
    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x_{p}') for p in pts]
    model.Add(sum(x) == rank_s)
    for p in fixed:
        model.Add(x[idx[p]] == 1)
    if exact_rank1_count is not None:
        rank1_vars = [x[idx[p]] for p in pts if matrix_rank_of_mask(p) == 1]
        model.Add(sum(rank1_vars) == int(exact_rank1_count))
    assumptions = []
    amap = {}
    for j, r in enumerate(rows):
        vars_in = [x[idx[p]] for p in r['vars']]
        if use_assumptions:
            a = model.NewBoolVar(f'a_row_{j}')
            if r['cap_rem'] < 0:
                model.AddBoolOr([]).OnlyEnforceIf(a)
            else:
                model.Add(sum(vars_in) <= int(r['cap_rem'])).OnlyEnforceIf(a)
            assumptions.append(a)
            amap[a.Index()] = j
        else:
            if r['cap_rem'] < 0:
                model.AddBoolOr([])
            else:
                model.Add(sum(vars_in) <= int(r['cap_rem']))
    if use_assumptions:
        model.AddAssumptions(assumptions)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = int(workers)
    t0 = time.time()
    st = solver.Solve(model)
    elapsed = time.time() - t0
    status_name = solver.StatusName(st)
    core_indices = None
    if use_assumptions and st == cp_model.INFEASIBLE:
        raw = list(solver.SufficientAssumptionsForInfeasibility())
        core_indices = sorted({amap[int(i)] for i in raw if int(i) in amap})
    sol = None
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = [p for p in pts if solver.Value(x[idx[p]])]
    return {
        'status': status_name,
        'status_code': int(st),
        'elapsed_sec': elapsed,
        'solver_walltime': float(solver.WallTime()),
        'conflicts': int(solver.NumConflicts()),
        'branches': int(solver.NumBranches()),
        'core_indices': core_indices,
        'support': sol,
        'support_rank1_count': None if sol is None else sum(1 for p in sol if matrix_rank_of_mask(p) == 1),
        'support_rank_hist': None if sol is None else dict(sorted(Counter(matrix_rank_of_mask(p) for p in sol).items())),
    }


def shrink_by_solver_core(rows: list[dict], *, pts, idx, fixed, rank_s, exact_rank1_count,
                          time_limit, workers, rounds: int):
    history = []
    cur = list(rows)
    for r in range(rounds):
        res = solve_with_assumptions(cur, pts=pts, idx=idx, fixed=fixed, rank_s=rank_s,
                                     exact_rank1_count=exact_rank1_count,
                                     time_limit=time_limit, workers=workers,
                                     use_assumptions=True)
        ent = {k: res[k] for k in ['status', 'elapsed_sec', 'solver_walltime', 'conflicts', 'branches']}
        ent['input_rows'] = len(cur)
        if res['status'] == 'INFEASIBLE' and res['core_indices'] is not None:
            keep = res['core_indices']
            ent['core_rows'] = len(keep)
            history.append(ent)
            if len(keep) == len(cur):
                break
            cur = [cur[i] for i in keep]
        else:
            ent['core_rows'] = None
            history.append(ent)
            break
    return cur, history


def row_summary(rows: Sequence[dict]):
    return {
        'row_count': len(rows),
        'by_dim': dict(sorted(Counter(r['dim'] for r in rows).items())),
        'by_lb': dict(sorted(Counter(r['lb'] for r in rows).items())),
        'by_cap_rem': dict(sorted(Counter(r['cap_rem'] for r in rows).items())),
        'by_var_count': dict(sorted(Counter(r['var_count'] for r in rows).items())),
        'by_source_dim': {f'{s},{d}': c for (s, d), c in sorted(Counter((r['source'], r['dim']) for r in rows).items())},
    }


def representative_rows(rows: Sequence[dict], limit: int):
    out = []
    for r in rows[:limit]:
        out.append({k: (list(v) if isinstance(v, tuple) else v)
                    for k, v in r.items()
                    if k in ['key', 'dim', 'lb', 'raw_cap', 'fixed_in', 'cap_rem', 'var_count', 'basis', 'source']})
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', default='10')
    ap.add_argument('--exclude-second-orbits-before', action='store_true')
    ap.add_argument('--include-dims', default='1')
    ap.add_argument('--through-fixed-dims', default='4,6')
    ap.add_argument('--exact-rank1-count', type=int, required=True)
    ap.add_argument('--time-limit', type=float, default=120.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--core-rounds', type=int, default=4)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--preview-limit', type=int, default=80)
    args = ap.parse_args()

    t0 = time.time()
    lut, lmeta = load_lut(args.lut)
    fixed_extra = parse_ints(args.fixed_extra)
    fixed, excluded, pts, idx = branch_points(fixed_extra, args.exclude_second_orbits_before)
    rows, collect_meta = collect_rows(lut, rank_s=args.rank, fixed=fixed, pts=pts,
                                      include_dims=parse_dims(args.include_dims),
                                      through_fixed_dims=parse_dims(args.through_fixed_dims))
    core, history = shrink_by_solver_core(rows, pts=pts, idx=idx, fixed=fixed,
                                          rank_s=args.rank,
                                          exact_rank1_count=args.exact_rank1_count,
                                          time_limit=args.time_limit,
                                          workers=args.workers,
                                          rounds=args.core_rounds)
    final = solve_with_assumptions(core, pts=pts, idx=idx, fixed=fixed,
                                   rank_s=args.rank,
                                   exact_rank1_count=args.exact_rank1_count,
                                   time_limit=args.time_limit,
                                   workers=args.workers,
                                   use_assumptions=False)
    payload = {
        'problem': 'rep10 fixed-E11 exact-rank1-count row-core CP-SAT shrink',
        'field': 'F2',
        'rank_s': args.rank,
        'fixed_points': fixed,
        'fixed_extra': fixed_extra,
        'exclude_second_orbits_before': args.exclude_second_orbits_before,
        'exact_rank1_count': args.exact_rank1_count,
        'include_dims': sorted(parse_dims(args.include_dims)),
        'through_fixed_dims': sorted(parse_dims(args.through_fixed_dims)),
        'variable_point_count': len(pts),
        'variable_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in pts).items())),
        'excluded_point_count': len(excluded),
        'excluded_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in excluded).items())),
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'collect_meta': collect_meta,
        'initial_row_summary': row_summary(rows),
        'core_solver_history': history,
        'core_summary': row_summary(core),
        'core_keys': [int(r['key']) for r in core],
        'core_rows_preview': representative_rows(core, args.preview_limit),
        'final_check': {k: final[k] for k in ['status','elapsed_sec','solver_walltime','conflicts','branches','support_rank1_count','support_rank_hist']},
        'total_elapsed_sec': time.time() - t0,
        'meaning': 'CP-SAT row-core target only.  A formal branch leaf still needs a CNF/DRAT or equivalent proof for this row subset and exact rank-1 count.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'exact_rank1_count': args.exact_rank1_count,
        'initial_rows': len(rows),
        'core_rows': len(core),
        'core_summary': row_summary(core),
        'history': history,
        'final_status': final['status'],
        'final_elapsed_sec': final['elapsed_sec'],
        'out': str(args.out),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
