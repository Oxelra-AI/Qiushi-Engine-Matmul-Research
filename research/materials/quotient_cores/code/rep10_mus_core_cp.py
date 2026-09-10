#!/usr/bin/env python3
"""Shrink the fixed-E11/rep10 Wang CP-SAT infeasibility to a row core.

This is an execution instrument for the research_record finite-field lower-bound route.
It works at the level of Wang occupation rows, not CNF clauses.  For a selected
row family (default: dim 1 plus through-fixed dims 4 and 6 for fixed points
E11 and rep10), it constructs the CP-SAT support model with one assumption
literal per non-vacuous row.  OR-Tools can then return a sufficient infeasible
assumption set.  The script iteratively rebuilds the model using only that set
and/or performs deletion passes to shrink the row family before proof-producing
CNF encoding.

The output is not a theorem by itself; it is a compact row-core candidate and a
semantic explanation of which Wang rows cause the rep10 branch to die.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_cnf_e11_fixed import E11, parse_dims, stab_e11_orbits  # noqa: E402
from wang_capacity_lazy import (  # noqa: E402
    in_rowspace,
    matrix_rank_of_mask,
    subspace_points_from_basis,
    transform_mask,
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
            if orb['rep'] == second:
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
    """Return selected rows with residual support variables/capacities.

    Rows with len(vars)<=cap_rem are marked vacuous and not returned as active
    constraints.  They are still counted by the caller from the metadata fields.
    """
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
    return rows, {'selected_rows_total': selected, 'active_rows': len(rows), 'skipped_vacuous': skipped,
                  'row_signature_hist': {str(k): v for k, v in sorted(hist.items())},
                  'source_by_dim': {f'{s},{d}': c for (s, d), c in sorted(src_hist.items())}}


def solve_with_assumptions(rows: Sequence[dict], *, pts: Sequence[int], idx: dict[int, int], fixed: Sequence[int],
                           rank_s: int, time_limit: float, workers: int, use_assumptions: bool):
    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x_{p}') for p in pts]
    model.Add(sum(x) == rank_s)
    for p in fixed:
        model.Add(x[idx[p]] == 1)
    assumptions = []
    amap = {}
    for j, r in enumerate(rows):
        vars_in = [x[idx[p]] for p in r['vars']]
        if r['cap_rem'] < 0:
            if use_assumptions:
                a = model.NewBoolVar(f'a_row_{j}')
                model.AddBoolOr([]).OnlyEnforceIf(a)
                assumptions.append(a)
                amap[a.Index()] = j
            else:
                model.AddBoolOr([])
        else:
            if use_assumptions:
                a = model.NewBoolVar(f'a_row_{j}')
                model.Add(sum(vars_in) <= int(r['cap_rem'])).OnlyEnforceIf(a)
                assumptions.append(a)
                amap[a.Index()] = j
            else:
                model.Add(sum(vars_in) <= int(r['cap_rem']))
    if use_assumptions:
        model.AddAssumptions(assumptions)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = workers
    t0 = time.time()
    st = solver.Solve(model)
    elapsed = time.time() - t0
    status_name = solver.StatusName(st)
    core_indices: list[int] | None = None
    if use_assumptions and st == cp_model.INFEASIBLE:
        raw = list(solver.SufficientAssumptionsForInfeasibility())
        core_indices = sorted({amap[i] for i in raw if i in amap})
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
    }


def shrink_by_solver_core(rows: list[dict], *, pts, idx, fixed, rank_s, time_limit, workers, rounds: int):
    history = []
    cur = list(rows)
    for r in range(rounds):
        res = solve_with_assumptions(cur, pts=pts, idx=idx, fixed=fixed, rank_s=rank_s,
                                     time_limit=time_limit, workers=workers, use_assumptions=True)
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


def deletion_pass(rows: list[dict], *, pts, idx, fixed, rank_s, time_limit, workers,
                  block_size: int, max_tests: int | None):
    """Greedy row deletion; removing a block permanently if UNSAT persists."""
    cur = list(rows)
    history = []
    pos = 0
    tests = 0
    while pos < len(cur):
        if max_tests is not None and tests >= max_tests:
            break
        block = list(range(pos, min(pos + block_size, len(cur))))
        trial = cur[:pos] + cur[pos + len(block):]
        res = solve_with_assumptions(trial, pts=pts, idx=idx, fixed=fixed, rank_s=rank_s,
                                     time_limit=time_limit, workers=workers, use_assumptions=False)
        tests += 1
        ent = {'test': tests, 'start': pos, 'block_size': len(block), 'input_rows': len(cur),
               'trial_rows': len(trial), 'status': res['status'], 'elapsed_sec': res['elapsed_sec'],
               'conflicts': res['conflicts'], 'branches': res['branches']}
        if res['status'] == 'INFEASIBLE':
            # The removed block was not needed.  Stay at same position because
            # the next old block shifted left.
            cur = trial
            ent['removed'] = len(block)
        else:
            pos += len(block)
            ent['removed'] = 0
        history.append(ent)
    return cur, history


def subgroup_stabilizing(points: Sequence[int]):
    target = set(int(p) for p in points)
    out = []
    # stab_e11_orbits imports all actions via wang_capacity_lazy; regenerate here
    from wang_capacity_lazy import make_actions
    for img in make_actions():
        if all(transform_mask(p, img) == p for p in target):
            out.append(img)
    return out


def orbit_close_keys(seed_keys: Iterable[int], rows_by_key: dict[int, dict], fixed: Sequence[int]):
    from wang_capacity_lazy import transform_key
    actions = subgroup_stabilizing(fixed)
    keys = set(int(k) for k in seed_keys)
    closed = set(keys)
    missing = set()
    for key in list(keys):
        basis = unpack_basis(key)
        for img in actions:
            k2 = transform_key(basis, img)
            if k2 in rows_by_key:
                closed.add(int(k2))
            else:
                missing.add(int(k2))
    return closed, {'stab_size': len(actions), 'seed_key_count': len(keys), 'closed_key_count': len(closed), 'missing_selected_images': len(missing)}


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
        out.append({k: (list(v) if isinstance(v, tuple) else v) for k, v in r.items() if k in ['key','dim','lb','raw_cap','fixed_in','cap_rem','var_count','basis','source']})
    return out


def write_core(rows: Sequence[dict], path: Path, meta: dict, preview_limit: int):
    payload = dict(meta)
    payload['core_summary'] = row_summary(rows)
    payload['core_keys'] = [int(r['key']) for r in rows]
    payload['core_rows_preview'] = representative_rows(rows, preview_limit)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', default='10')
    ap.add_argument('--exclude-second-orbits-before', action='store_true')
    ap.add_argument('--include-dims', default='1')
    ap.add_argument('--through-fixed-dims', default='4,6')
    ap.add_argument('--time-limit', type=float, default=120.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--core-rounds', type=int, default=4)
    ap.add_argument('--deletion-passes', type=int, default=0)
    ap.add_argument('--deletion-block-size', type=int, default=1)
    ap.add_argument('--max-deletion-tests', type=int, default=None)
    ap.add_argument('--orbit-close', action='store_true')
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
    original_rows = rows
    core, core_hist = shrink_by_solver_core(rows, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                            time_limit=args.time_limit, workers=args.workers,
                                            rounds=args.core_rounds)
    orbit_meta = None
    if args.orbit_close:
        by_key = {int(r['key']): r for r in original_rows}
        closed_keys, orbit_meta = orbit_close_keys([r['key'] for r in core], by_key, fixed)
        core = [by_key[k] for k in sorted(closed_keys)]
        # Confirm the orbit-closed set remains infeasible and possibly shrink again.
        core2, hist2 = shrink_by_solver_core(core, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                             time_limit=args.time_limit, workers=args.workers,
                                             rounds=max(1, args.core_rounds))
        core_hist.append({'orbit_close_confirm_input_rows': len(core), 'orbit_meta': orbit_meta})
        core_hist.extend(hist2)
        core = core2
    deletion_history = []
    for p in range(args.deletion_passes):
        core, hist = deletion_pass(core, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                   time_limit=args.time_limit, workers=args.workers,
                                   block_size=args.deletion_block_size,
                                   max_tests=args.max_deletion_tests)
        deletion_history.append({'pass': p + 1, 'block_size': args.deletion_block_size, 'history': hist,
                                 'rows_after': len(core)})
        # Re-ask the solver for a sufficient core after the deletion pass.
        core, hist2 = shrink_by_solver_core(core, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                            time_limit=args.time_limit, workers=args.workers,
                                            rounds=1)
        deletion_history[-1]['post_core_history'] = hist2
        deletion_history[-1]['rows_after_post_core'] = len(core)
    final_check = solve_with_assumptions(core, pts=pts, idx=idx, fixed=fixed, rank_s=args.rank,
                                         time_limit=args.time_limit, workers=args.workers,
                                         use_assumptions=False)
    meta = {
        'problem': 'rep10 fixed-E11 row-level CP-SAT infeasible-core shrink',
        'field': 'F2',
        'rank_s': args.rank,
        'fixed_points': fixed,
        'fixed_extra': fixed_extra,
        'exclude_second_orbits_before': args.exclude_second_orbits_before,
        'include_dims': sorted(parse_dims(args.include_dims)),
        'through_fixed_dims': sorted(parse_dims(args.through_fixed_dims)),
        'variable_point_count': len(pts),
        'variable_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in pts).items())),
        'excluded_point_count': len(excluded),
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'initial_row_summary': row_summary(original_rows),
        'collect_meta': collect_meta,
        'core_solver_history': core_hist,
        'orbit_close_meta': orbit_meta,
        'deletion_history': deletion_history,
        'final_check': {k: final_check[k] for k in ['status','elapsed_sec','solver_walltime','conflicts','branches']},
        'total_elapsed_sec': time.time() - t0,
        'meaning': 'A compact row set whose CP-SAT support model is infeasible. It must be encoded in CNF and DRAT-verified before use as a formal proof leaf.',
    }
    write_core(core, args.out, meta, args.preview_limit)
    print(json.dumps({
        'initial_rows': len(original_rows),
        'core_rows': len(core),
        'core_summary': row_summary(core),
        'core_history': core_hist,
        'deletion_passes': len(deletion_history),
        'final_status': final_check['status'],
        'final_elapsed_sec': final_check['elapsed_sec'],
        'out': str(args.out),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
