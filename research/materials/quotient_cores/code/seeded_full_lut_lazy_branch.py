#!/usr/bin/env python3
"""Seeded lazy CP-SAT for the remaining fixed-E11 Wang A-support branches.

This script starts from a chosen row family (for example all dim<=3, all rows
through E11 in dims 4..8, and optionally the rank-1 projection), adds seed cuts
from earlier complete-LUT violation scans, solves, then scans any support against
the entire expanded Wang LUT and adds the actual violated rows.  It is designed
to answer the scientific question: do the raw Wang A-side occupation constraints
themselves still admit a support in the rep2/rep16 branches?

The output is computation evidence.  UNSAT requires proof-producing replay for
formal use; SAT with zero full-LUT violations is an admissible A-support witness,
not a tensor decomposition.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Sequence, Set

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_capacity_profile import load_or_build as load_or_build_rank1_projection  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11, collect_violation_keys, parse_dims, stab_e11_orbits  # noqa: E402
from wang_capacity_lazy import in_rowspace, matrix_rank_of_mask, unpack_basis, subspace_points_from_basis  # noqa: E402


def parse_ints(spec: str) -> list[int]:
    return [int(x) for x in spec.replace(';', ',').split(',') if x.strip()]


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def branch_points(fixed_extra: Sequence[int], exclude_second_orbits_before: bool):
    fixed = [E11] + [int(p) for p in fixed_extra if int(p) != E11]
    excluded: Set[int] = set()
    if exclude_second_orbits_before:
        if len(fixed_extra) != 1:
            raise ValueError('exclude_second_orbits_before requires exactly one fixed extra point')
        second_rep = int(fixed_extra[0])
        found = False
        for orb in stab_e11_orbits():
            if orb['rep'] == second_rep:
                found = True
                break
            excluded.update(int(p) for p in orb['members'])
        if not found:
            raise ValueError(f'{second_rep} is not a Stab(E11) representative')
        for p in fixed:
            excluded.discard(p)
    pts = [p for p in range(1, 512) if p not in excluded]
    idx = {p: i for i, p in enumerate(pts)}
    for p in fixed:
        if p not in idx:
            raise ValueError(f'fixed point {p} excluded from branch')
    return fixed, excluded, pts, idx


def row_contains_all(points: Sequence[int], basis: Sequence[int]) -> bool:
    return all(in_rowspace(int(p), basis, n=9) for p in points)


def add_lut_cut(model, x, idx, fixed_set, lut, key: int, added: set[int], records: list[dict], reason: str, rank_s: int) -> bool:
    key = int(key)
    if key in added:
        return False
    lb = int(lut[key])
    basis = unpack_basis(key)
    pts_in = subspace_points_from_basis(basis)
    cap = rank_s - lb
    fixed_in = sum(1 for p in fixed_set if p in pts_in)
    cap_rem = cap - fixed_in
    vars_in = [x[idx[p]] for p in pts_in if p in idx and p not in fixed_set]
    if cap_rem < 0:
        model.AddBoolOr([])
    elif len(vars_in) > cap_rem:
        model.Add(sum(vars_in) <= cap_rem)
    else:
        pass
    added.add(key)
    records.append({'key': key, 'dim': key & 0xF, 'lb': lb, 'cap': cap, 'fixed_in': fixed_in,
                    'cap_rem': cap_rem, 'var_count': len(vars_in), 'reason': reason,
                    'vacuous_in_branch': len(vars_in) <= cap_rem and cap_rem >= 0})
    return True


def add_rank1_projection(model, x, idx: dict[int, int], rank1_cache: Path, lut_path: Path, rank_s: int,
                         fixed_set: set[int]):
    pts_r1, cons, cmeta, lmeta = load_or_build_rank1_projection(rank1_cache, lut_path, rank_s, False)
    fixed_r1 = {p: i for i, p in enumerate(pts_r1) if p in fixed_set}
    rows_added = 0
    skipped = 0
    empty = 0
    row_hist = Counter()
    cap_hist = Counter()
    row_var_hist = Counter()
    for mask0, cap0, key in cons:
        mask = int(mask0)
        cap = int(cap0)
        fixed_in = sum(1 for p, i in fixed_r1.items() if (mask >> i) & 1)
        cap_rem = cap - fixed_in
        vars_in = []
        y = mask
        while y:
            lb = y & -y
            i = lb.bit_length() - 1
            y ^= lb
            p = int(pts_r1[i])
            if p in idx and p not in fixed_set:
                vars_in.append(x[idx[p]])
        row_hist[(mask.bit_count(), cap)] += 1
        cap_hist[cap_rem] += 1
        row_var_hist[len(vars_in)] += 1
        if cap_rem < 0:
            model.AddBoolOr([])
            rows_added += 1
            empty += 1
        elif len(vars_in) <= cap_rem:
            skipped += 1
        else:
            model.Add(sum(vars_in) <= cap_rem)
            rows_added += 1
    return {
        'rank1_projection_rows_added': rows_added,
        'rank1_projection_skipped_vacuous': skipped,
        'rank1_projection_empty': empty,
        'rank1_projection_hist': {f'{a},{b}': c for (a, b), c in sorted(row_hist.items())},
        'rank1_projection_residual_cap_hist': dict(sorted(cap_hist.items())),
        'rank1_projection_row_var_hist': dict(sorted(row_var_hist.items())),
        'rank1_projection_cache_meta_brief': {
            'compressed_intersections': cmeta.get('compressed_intersections'),
            'nonvacuous_constraints': cmeta.get('nonvacuous_constraints'),
            'lut_coverage_ok': lmeta.get('coverage_ok'),
            'lut_conflict_count': lmeta.get('conflict_count'),
        },
    }


def full_lut_violations(lut: dict[int, int], support: Sequence[int], rank_s: int, max_add: int) -> tuple[list[dict], dict]:
    t0 = time.time()
    support_items = [(int(p), 1) for p in support]
    violations = []
    by_dim = Counter()
    by_lb = Counter()
    checked = 0
    for key, lb0 in lut.items():
        basis = unpack_basis(int(key))
        occ = 0
        for p, mult in support_items:
            if in_rowspace(p, basis, n=9):
                occ += mult
        cap = rank_s - int(lb0)
        if occ > cap:
            v = {'key': int(key), 'dim': int(key) & 0xF, 'lb': int(lb0), 'cap': int(cap),
                 'occupancy': int(occ), 'excess': int(occ - cap), 'basis': list(basis)}
            violations.append(v)
            by_dim[v['dim']] += 1
            by_lb[v['lb']] += 1
        checked += 1
    violations.sort(key=lambda v: (v['excess'], v['lb'], v['occupancy'], -v['dim']), reverse=True)
    selected = violations[:max_add] if max_add and len(violations) > max_add else violations
    stats = {
        'checked_subspaces': checked,
        'elapsed_sec': time.time() - t0,
        'violation_count': len(violations),
        'selected_violation_count': len(selected),
        'violations_by_dim': dict(sorted(by_dim.items())),
        'violations_by_lb': dict(sorted(by_lb.items())),
        'max_excess': max((v['excess'] for v in violations), default=0),
    }
    return selected, stats


def add_initial_rows(model, x, idx, fixed_set, lut, added, records, include_dims, through_dims, through_points, seed_dims, seed_keys, rank_s):
    source_by_dim = Counter()
    selected_initial = 0
    for key, lb0 in lut.items():
        d = int(key) & 0xF
        take = False
        reason = ''
        if d in include_dims:
            take = True
            reason = f'include_dim_{d}'
        elif d in through_dims:
            basis = unpack_basis(int(key))
            if row_contains_all(through_points, basis):
                take = True
                reason = f'through_{"_".join(map(str, through_points))}_dim_{d}'
        if take:
            selected_initial += 1
            if add_lut_cut(model, x, idx, fixed_set, lut, key, added, records, reason, rank_s):
                source_by_dim[(reason, d)] += 1
    initial_cut_count = len(added)
    seed_added = 0
    for key in sorted(seed_keys):
        if key in lut and ((int(key) & 0xF) in seed_dims):
            if add_lut_cut(model, x, idx, fixed_set, lut, key, added, records, 'seed_json', rank_s):
                seed_added += 1
    return {'selected_initial_rows': selected_initial, 'initial_cut_count': initial_cut_count,
            'initial_source_by_dim': {f'{s},{d}': c for (s, d), c in sorted(source_by_dim.items())},
            'seed_cut_count_added': seed_added}


def solve(lut, lmeta, args):
    from ortools.sat.python import cp_model
    fixed_extra = parse_ints(args.fixed_extra)
    fixed, excluded, pts, idx = branch_points(fixed_extra, args.exclude_second_orbits_before)
    fixed_set = set(fixed)
    through_points = parse_ints(args.through_points)
    if not through_points:
        through_points = fixed
    include_dims = parse_dims(args.include_dims)
    through_dims = parse_dims(args.through_dims)
    seed_dims = parse_dims(args.seed_dims)
    seed_keys: set[int] = set()
    for p in args.seed_json:
        got = collect_violation_keys(p)
        print(f'seed {p}: {len(got)} keys', flush=True)
        seed_keys.update(got)

    all_history = []
    final_status = None
    final_solution = None
    final_cuts_summary = None
    t_all = time.time()
    for outer in range(1, args.max_iters + 1):
        t0 = time.time()
        model = cp_model.CpModel()
        x = [model.NewBoolVar(f'x_{p}') for p in pts]
        model.Add(sum(x) == args.rank)
        for p in fixed:
            model.Add(x[idx[p]] == 1)
        rank1_vars = [x[idx[p]] for p in pts if matrix_rank_of_mask(p) == 1]
        if args.min_rank1_count is not None:
            model.Add(sum(rank1_vars) >= args.min_rank1_count)
        if args.max_rank1_count is not None:
            model.Add(sum(rank1_vars) <= args.max_rank1_count)
        if args.exact_rank1_count is not None:
            model.Add(sum(rank1_vars) == args.exact_rank1_count)
        added: set[int] = set()
        records: list[dict] = []
        init_meta = add_initial_rows(model, x, idx, fixed_set, lut, added, records, include_dims,
                                     through_dims, through_points, seed_dims, seed_keys, args.rank)
        r1stats = {}
        if not args.no_rank1_projection:
            r1stats = add_rank1_projection(model, x, idx, args.rank1_cache, args.lut, args.rank, fixed_set)
        else:
            r1stats = {'rank1_projection_rows_added': 0, 'rank1_projection_skipped_vacuous': 0, 'rank1_projection_empty': 0}
        build_elapsed = time.time() - t0
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = args.solver_time
        solver.parameters.num_search_workers = args.workers
        solver.parameters.random_seed = args.random_seed + outer
        ts = time.time()
        st = solver.Solve(model)
        solve_elapsed = time.time() - ts
        name = solver.StatusName(st)
        entry = {'iteration': outer, 'solver_status': name, 'cut_count': len(added),
                 'seed_key_count': len(seed_keys), 'build_elapsed_sec': build_elapsed,
                 'solve_elapsed_sec': solve_elapsed, 'solver_walltime': float(solver.WallTime()),
                 'conflicts': int(solver.NumConflicts()), 'branches': int(solver.NumBranches()),
                 **init_meta, **r1stats}
        print(f'iter {outer}: {name}; seed_keys={len(seed_keys):,}; cuts={len(added):,}; build={build_elapsed:.1f}s; solve={solve_elapsed:.1f}s', flush=True)
        if name in ('INFEASIBLE', 'MODEL_INVALID'):
            final_status = name
            all_history.append(entry)
            final_cuts_summary = (added, records, r1stats, init_meta)
            break
        if name not in ('OPTIMAL', 'FEASIBLE'):
            final_status = name
            all_history.append(entry)
            final_cuts_summary = (added, records, r1stats, init_meta)
            break
        sol = [p for p in pts if solver.Value(x[idx[p]])]
        entry['support'] = sol
        entry['support_size'] = len(sol)
        entry['support_rank_hist'] = dict(sorted(Counter(matrix_rank_of_mask(p) for p in sol).items()))
        entry['support_rank1_count'] = sum(1 for p in sol if matrix_rank_of_mask(p) == 1)
        violations, stats = full_lut_violations(lut, sol, args.rank, args.max_add_per_iter)
        entry['full_lut_check'] = stats
        entry['violations_head'] = violations[:args.max_report]
        print(f'  support ranks={entry["support_rank_hist"]}; full violations={stats["violation_count"]:,}; selected={stats["selected_violation_count"]}; max_excess={stats["max_excess"]}; check={stats["elapsed_sec"]:.1f}s', flush=True)
        if stats['violation_count'] == 0:
            final_status = 'CAPACITY_FEASIBLE_FULL_LUT'
            final_solution = sol
            all_history.append(entry)
            final_cuts_summary = (added, records, r1stats, init_meta)
            break
        before = len(seed_keys)
        seed_keys.update(int(v['key']) for v in violations if (int(v['key']) & 0xF) in seed_dims)
        entry['lazy_seed_keys_added_for_rebuild'] = len(seed_keys) - before
        all_history.append(entry)
        if len(seed_keys) == before:
            final_status = 'STALLED_NO_NEW_CUTS'
            final_solution = sol
            final_cuts_summary = (added, records, r1stats, init_meta)
            break
    if final_cuts_summary is None:
        final_cuts_summary = (set(), [], {}, {})
    added, records, r1stats, init_meta = final_cuts_summary
    result = {
        'problem': 'seeded lazy fixed-E11 branch with complete-LUT support checks',
        'field': 'F2',
        'rank_s': args.rank,
        'fixed_points': fixed,
        'fixed_extra': fixed_extra,
        'through_points': through_points,
        'exclude_second_orbits_before': args.exclude_second_orbits_before,
        'include_dims': sorted(include_dims),
        'through_dims': sorted(through_dims),
        'seed_dims': sorted(seed_dims),
        'final_seed_key_count': len(seed_keys),
        'cut_count': len(added),
        'cuts_by_dim': dict(sorted(Counter(r['dim'] for r in records).items())),
        'cuts_by_lb': dict(sorted(Counter(r['lb'] for r in records).items())),
        'vacuous_cut_records': sum(1 for r in records if r.get('vacuous_in_branch')),
        'variable_point_count': len(pts),
        'variable_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in pts).items())),
        'excluded_point_count': len(excluded),
        'excluded_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in excluded).items())),
        **r1stats,
        'min_rank1_count': args.min_rank1_count,
        'max_rank1_count': args.max_rank1_count,
        'exact_rank1_count': args.exact_rank1_count,
        'max_iters': args.max_iters,
        'solver_time_per_iter': args.solver_time,
        'max_add_per_iter': args.max_add_per_iter,
        'final_status': final_status,
        'final_solution': final_solution,
        'iterations': all_history,
        'cut_records_head': records[:args.max_report],
        'cut_records_tail': records[-args.max_report:],
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'total_elapsed_sec': time.time() - t_all,
        'meaning': 'If final_status is CAPACITY_FEASIBLE_FULL_LUT, the branch has an A-side support satisfying the complete Wang table; if INFEASIBLE, theorem use still needs proof-producing replay.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: result[k] for k in ['final_status','fixed_points','through_points','final_seed_key_count','cut_count','cuts_by_dim','rank1_projection_rows_added','total_elapsed_sec']}, indent=2, sort_keys=True))
    print('saved', args.out)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', required=True)
    ap.add_argument('--exclude-second-orbits-before', action='store_true')
    ap.add_argument('--through-points', default=str(E11))
    ap.add_argument('--include-dims', default='1,2,3')
    ap.add_argument('--through-dims', default='4-8')
    ap.add_argument('--seed-json', type=Path, action='append', default=[])
    ap.add_argument('--seed-dims', default='4-8')
    ap.add_argument('--no-rank1-projection', action='store_true')
    ap.add_argument('--rank1-cache', type=Path, default=Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl'))
    ap.add_argument('--min-rank1-count', type=int, default=1)
    ap.add_argument('--max-rank1-count', type=int, default=17)
    ap.add_argument('--exact-rank1-count', type=int, default=None)
    ap.add_argument('--max-iters', type=int, default=5)
    ap.add_argument('--solver-time', type=float, default=300.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--max-add-per-iter', type=int, default=500)
    ap.add_argument('--max-report', type=int, default=80)
    ap.add_argument('--random-seed', type=int, default=21000)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    lut, lmeta = load_lut(args.lut)
    print(f'loaded LUT {len(lut):,} coverage={lmeta.get("coverage_ok")} conflicts={lmeta.get("conflict_count")}', flush=True)
    solve(lut, lmeta, args)


if __name__ == '__main__':
    main()
