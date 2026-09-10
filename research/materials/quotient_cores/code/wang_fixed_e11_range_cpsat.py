#!/usr/bin/env python3
"""CP-SAT probes for fixed-E11 Wang supports with a rank-1-count range.

The variable set is the projective A-side over F2.  The script fixes E11,
optionally fixes a second Stab(E11)-orbit representative and removes earlier
single-orbit points, constrains the number of rank-1 selected points to a range,
and combines three sound families of Wang occupation inequalities:

  1. full rows in selected low dimensions, usually 1,2,3;
  2. high-dimensional rows that contain a fixed prefix, usually E11 alone or
     E11 plus a fixed second point;
  3. the full compressed projection of all Wang rows onto rank-1 points.

SAT output is only an A-support candidate and should be scanned against the full
Wang table.  INFEASIBLE is useful execution evidence; theorem use requires a
CNF/DRAT replay or another independently verifiable proof object.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Sequence, Set

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_capacity_profile import load_or_build as load_or_build_rank1_projection  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11, collect_violation_keys, parse_dims, stab_e11_orbits  # noqa: E402
from wang_capacity_lazy import in_rowspace, matrix_rank_of_mask, unpack_basis, subspace_points_from_basis  # noqa: E402


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


def add_rank1_projection(model, x, idx: dict[int, int], rank1_cache: Path, lut_path: Path, rank_s: int,
                         max_intersection_size: int | None, include_groups: set[tuple[int, int]] | None):
    pts_r1, cons, cmeta, lmeta = load_or_build_rank1_projection(rank1_cache, lut_path, rank_s, False)
    rows_added = 0; skipped = 0; empty = 0
    row_hist = Counter(); cap_hist = Counter(); row_var_hist = Counter(); group_selected = Counter()
    for mask0, cap0, key in cons:
        mask = int(mask0); cap = int(cap0); size = mask.bit_count()
        if include_groups is not None and (size, cap) not in include_groups:
            continue
        if include_groups is None and max_intersection_size is not None and size > max_intersection_size:
            continue
        vars_in = []
        y = mask
        while y:
            lb = y & -y
            i = lb.bit_length() - 1
            y ^= lb
            p = int(pts_r1[i])
            if p in idx:
                vars_in.append(x[idx[p]])
        row_hist[(size, cap)] += 1; cap_hist[cap] += 1; row_var_hist[len(vars_in)] += 1; group_selected[(size, cap)] += 1
        if cap < 0:
            model.AddBoolOr([]); rows_added += 1; empty += 1
        elif len(vars_in) <= cap:
            skipped += 1
        else:
            model.Add(sum(vars_in) <= cap); rows_added += 1
    return {
        'rank1_projection_rows_added': rows_added,
        'rank1_projection_skipped_vacuous': skipped,
        'rank1_projection_empty': empty,
        'rank1_projection_hist': {f'{a},{b}': c for (a, b), c in sorted(row_hist.items())},
        'rank1_projection_cap_hist': dict(sorted(cap_hist.items())),
        'rank1_projection_row_var_hist': dict(sorted(row_var_hist.items())),
        'rank1_projection_filter': {
            'max_intersection_size': max_intersection_size,
            'include_groups': None if include_groups is None else sorted([list(g) for g in include_groups]),
        },
        'rank1_projection_cache_meta_brief': {
            'compressed_intersections': cmeta.get('compressed_intersections'),
            'nonvacuous_constraints': cmeta.get('nonvacuous_constraints'),
            'lut_coverage_ok': lmeta.get('coverage_ok'),
            'lut_conflict_count': lmeta.get('conflict_count'),
        },
    }


def parse_groups(spec: str) -> set[tuple[int, int]] | None:
    spec = spec.strip()
    if not spec:
        return None
    out: set[tuple[int, int]] = set()
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


def solve(lut: Dict[int, int], lut_meta: dict, *, lut_path: Path, rank_s: int, fixed_extra: Sequence[int],
          exclude_second_orbits_before: bool, min_rank1_count: int | None, max_rank1_count: int | None,
          exact_rank1_count: int | None, include_dims: Set[int], through_fixed_dims: Set[int],
          seed_keys: Set[int], seed_dims: Set[int], rank1_cache: Path,
          rank1_max_intersection_size: int | None, rank1_include_groups: set[tuple[int, int]] | None,
          time_limit: float, workers: int, out: Path):
    from ortools.sat.python import cp_model

    t0 = time.time()
    fixed, excluded, pts, idx = branch_points(fixed_extra, exclude_second_orbits_before)
    fixed_set = set(fixed)
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x_{p}') for p in pts]
    model.Add(sum(x) == rank_s)
    for p in fixed:
        model.Add(x[idx[p]] == 1)
    rank1_vars = [x[idx[p]] for p in pts if matrix_rank_of_mask(p) == 1]
    if exact_rank1_count is not None:
        model.Add(sum(rank1_vars) == exact_rank1_count)
    if min_rank1_count is not None:
        model.Add(sum(rank1_vars) >= min_rank1_count)
    if max_rank1_count is not None:
        model.Add(sum(rank1_vars) <= max_rank1_count)

    rows_added = 0; skipped = 0; empty = 0
    rows_by_dim = Counter(); rows_by_lb = Counter(); source_by_dim = Counter(); row_var_hist = Counter(); cap_hist = Counter(); fixed_in_hist = Counter()
    for i, (key, lb0) in enumerate(lut.items(), 1):
        d = int(key) & 0xF
        basis = None
        source = None
        if d in include_dims:
            source = 'include_dim'
        elif d in through_fixed_dims:
            basis = unpack_basis(key)
            if row_contains_all(fixed, basis):
                source = 'through_fixed'
        if source is None and key in seed_keys and d in seed_dims:
            source = 'seed'
        if source is None:
            continue
        if basis is None:
            basis = unpack_basis(key)
        pts_in = subspace_points_from_basis(basis)
        cap = rank_s - int(lb0)
        fixed_in = sum(1 for p in fixed if p in pts_in)
        cap_rem = cap - fixed_in
        vars_in = [x[idx[p]] for p in pts_in if p in idx and p not in fixed_set]
        rows_by_dim[d] += 1; rows_by_lb[int(lb0)] += 1; source_by_dim[(source, d)] += 1; row_var_hist[len(vars_in)] += 1; cap_hist[cap_rem] += 1; fixed_in_hist[fixed_in] += 1
        if cap_rem < 0:
            model.AddBoolOr([]); rows_added += 1; empty += 1
        elif len(vars_in) <= cap_rem:
            skipped += 1
        else:
            model.Add(sum(vars_in) <= cap_rem); rows_added += 1
        if i % 1_000_000 == 0:
            print(f'scanned {i:,}/{len(lut):,}; wang_added={rows_added:,}; elapsed={time.time()-t0:.1f}s', flush=True)

    r1_stats = add_rank1_projection(model, x, idx, rank1_cache, lut_path, rank_s, rank1_max_intersection_size, rank1_include_groups)
    build_elapsed = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = workers
    t1 = time.time(); st = solver.Solve(model); solve_elapsed = time.time() - t1
    names = {cp_model.OPTIMAL: 'OPTIMAL', cp_model.FEASIBLE: 'FEASIBLE', cp_model.INFEASIBLE: 'INFEASIBLE', cp_model.UNKNOWN: 'UNKNOWN', cp_model.MODEL_INVALID: 'MODEL_INVALID'}
    sol = None
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = [p for p in pts if solver.Value(x[idx[p]])]
    orbit_info = stab_e11_orbits()
    payload = {
        'problem': 'fixed-E11 Wang support CP-SAT with rank-1-count range',
        'field': 'F2',
        'rank_s': rank_s,
        'fixed_points': fixed,
        'fixed_extra': list(fixed_extra),
        'exclude_second_orbits_before': exclude_second_orbits_before,
        'second_orbit_reps': [int(o['rep']) for o in orbit_info],
        'min_rank1_count': min_rank1_count,
        'max_rank1_count': max_rank1_count,
        'exact_rank1_count': exact_rank1_count,
        'include_dims': sorted(include_dims),
        'through_fixed_dims': sorted(through_fixed_dims),
        'seed_dims': sorted(seed_dims),
        'seed_key_count': len(seed_keys),
        'variable_point_count': len(pts),
        'variable_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in pts).items())),
        'excluded_point_count': len(excluded),
        'excluded_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in excluded).items())),
        'wang_rows_added': rows_added,
        'wang_rows_by_dim': dict(sorted(rows_by_dim.items())),
        'wang_rows_by_lb': dict(sorted(rows_by_lb.items())),
        'wang_source_by_dim': {f'{s},{d}': c for (s, d), c in sorted(source_by_dim.items())},
        'wang_row_var_hist': dict(sorted(row_var_hist.items())),
        'wang_residual_cap_hist': dict(sorted(cap_hist.items())),
        'wang_fixed_in_row_hist': dict(sorted(fixed_in_hist.items())),
        'wang_skipped_vacuous': skipped,
        'wang_empty': empty,
        **r1_stats,
        'solver_status': names.get(st, str(st)),
        'solver_status_code': int(st),
        'solver_walltime': float(solver.WallTime()),
        'solver_num_conflicts': int(solver.NumConflicts()),
        'solver_num_branches': int(solver.NumBranches()),
        'build_elapsed_sec': build_elapsed,
        'solve_elapsed_sec': solve_elapsed,
        'support': sol,
        'support_size': None if sol is None else len(sol),
        'support_rank_hist': None if sol is None else dict(sorted(Counter(matrix_rank_of_mask(p) for p in sol).items())),
        'support_rank1_count': None if sol is None else sum(1 for p in sol if matrix_rank_of_mask(p) == 1),
        'lut_meta_brief': {'coverage_ok': lut_meta.get('coverage_ok'), 'conflict_count': lut_meta.get('conflict_count'), 'subspace_count': lut_meta.get('subspace_count')},
        'meaning': 'CP-SAT range probe using a sound subset of Wang occupation rows plus the rank-1 projection. SAT needs a complete-LUT scan; INFEASIBLE needs a proof replay before theorem use.',
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: payload[k] for k in ['solver_status', 'support_size', 'support_rank_hist', 'support_rank1_count', 'fixed_points', 'wang_rows_added', 'rank1_projection_rows_added', 'build_elapsed_sec', 'solve_elapsed_sec']}, indent=2, sort_keys=True))
    print('saved', out)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', default='', help='comma-separated extra fixed projective masks after E11')
    ap.add_argument('--exclude-second-orbits-before', action='store_true')
    ap.add_argument('--min-rank1-count', type=int, default=None)
    ap.add_argument('--max-rank1-count', type=int, default=None)
    ap.add_argument('--exact-rank1-count', type=int, default=None)
    ap.add_argument('--include-dims', default='1,2,3')
    ap.add_argument('--through-fixed-dims', default='4-8')
    ap.add_argument('--seed-json', type=Path, action='append', default=[])
    ap.add_argument('--seed-dims', default='4-8')
    ap.add_argument('--rank1-cache', type=Path, default=Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl'))
    ap.add_argument('--rank1-max-intersection-size', type=int, default=None)
    ap.add_argument('--rank1-include-groups', default='')
    ap.add_argument('--time-limit', type=float, default=300)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    fixed_extra = parse_ints(args.fixed_extra)
    if args.exclude_second_orbits_before and len(fixed_extra) != 1:
        raise SystemExit('--exclude-second-orbits-before requires exactly one --fixed-extra mask')
    seed_keys: Set[int] = set()
    for path in args.seed_json:
        got = collect_violation_keys(path)
        print(f'seed {path}: {len(got)} keys', flush=True)
        seed_keys.update(got)
    lut, meta = load_lut(args.lut)
    print(f'loaded LUT {len(lut):,} coverage={meta.get("coverage_ok")} conflicts={meta.get("conflict_count")}', flush=True)
    solve(
        lut, meta, lut_path=args.lut, rank_s=args.rank, fixed_extra=fixed_extra,
        exclude_second_orbits_before=args.exclude_second_orbits_before,
        min_rank1_count=args.min_rank1_count, max_rank1_count=args.max_rank1_count,
        exact_rank1_count=args.exact_rank1_count, include_dims=parse_dims(args.include_dims),
        through_fixed_dims=parse_dims(args.through_fixed_dims), seed_keys=seed_keys,
        seed_dims=parse_dims(args.seed_dims), rank1_cache=args.rank1_cache,
        rank1_max_intersection_size=args.rank1_max_intersection_size,
        rank1_include_groups=parse_groups(args.rank1_include_groups),
        time_limit=args.time_limit, workers=args.workers, out=args.out,
    )


if __name__ == '__main__':
    main()
