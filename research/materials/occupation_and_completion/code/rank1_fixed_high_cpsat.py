#!/usr/bin/env python3
"""CP-SAT probes for exact rank-1 skeletons with fixed higher-rank prefixes.

This is the fast, non-proof counterpart to rank1_fixed_high_cnf.py.  It fixes
some rank-1 A-points (usually E11 and a second rank-1 orbit representative) and
some higher-rank A-points, then solves for exactly K rank-1 points satisfying
the full Wang occupation table after subtracting the fixed higher-rank
occupancy.  SAT outputs are skeleton candidates; INFEASIBLE is execution
evidence that must be replayed as CNF/DRAT before theorem use.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import matrix_rank_of_mask, unpack_basis, subspace_points_from_basis  # noqa: E402


def parse_ints(spec: str) -> List[int]:
    if not spec.strip():
        return []
    return [int(x) for x in spec.replace(';', ',').split(',') if x.strip()]


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def rank1_points() -> List[int]:
    pts = [p for p in range(1, 512) if matrix_rank_of_mask(p) == 1]
    if len(pts) != 49:
        raise RuntimeError(f'expected 49 rank-1 points, got {len(pts)}')
    return pts


def solve_one(lut: Dict[int, int], lut_meta: dict, fixed_rank1: Sequence[int], fixed_high: Sequence[int],
              exact_rank1_count: int, rank_s: int, time_limit: float, workers: int):
    from ortools.sat.python import cp_model
    t0 = time.time()
    r1_pts = rank1_points(); r1_index = {p: i for i, p in enumerate(r1_pts)}; fixed_high_set = set(int(p) for p in fixed_high)
    model = cp_model.CpModel(); x = [model.NewBoolVar(f'x_{p}') for p in r1_pts]
    model.Add(sum(x) == exact_rank1_count)
    for p in fixed_rank1:
        if p not in r1_index:
            model.AddBoolOr([])
        else:
            model.Add(x[r1_index[p]] == 1)
    # Compress by rank-1 intersection mask and keep the tightest residual cap.
    tight: Dict[int, int] = {}; witness: Dict[int, dict] = {}
    raw_by_dim = Counter(); raw_by_lb = Counter(); fixed_high_in_hist = Counter(); raw_residual_cap_hist = Counter()
    for idx, (key, lb0) in enumerate(lut.items(), 1):
        basis = unpack_basis(key)
        rmask = 0; high_in = 0
        for p in subspace_points_from_basis(basis):
            j = r1_index.get(p)
            if j is not None:
                rmask |= 1 << j
            if p in fixed_high_set:
                high_in += 1
        cap = rank_s - int(lb0) - high_in
        old = tight.get(rmask)
        if old is None or cap < old:
            tight[rmask] = cap
            witness[rmask] = {'key': int(key), 'dim': int(key) & 0xF, 'lb': int(lb0), 'raw_cap': rank_s - int(lb0), 'fixed_high_in_row': high_in, 'residual_cap': cap, 'basis': list(basis)}
        raw_by_dim[int(key) & 0xF] += 1; raw_by_lb[int(lb0)] += 1; fixed_high_in_hist[high_in] += 1; raw_residual_cap_hist[cap] += 1
        if idx % 1_000_000 == 0:
            print(f'compressed {idx:,}/{len(lut):,}; distinct={len(tight):,}; elapsed={time.time()-t0:.1f}s', flush=True)
    cons = [(mask, cap, witness[mask]) for mask, cap in tight.items() if mask.bit_count() > cap]
    cons.sort(key=lambda t: (t[0].bit_count(), t[1], t[0]))
    row_hist = Counter(); row_var_hist = Counter(); cap_hist = Counter(); added = 0; skipped = 0; empty = 0; witness_head = []
    for mask, cap, wit in cons:
        inds = [i for i in range(len(r1_pts)) if (mask >> i) & 1]
        row_hist[(len(inds), int(cap))] += 1; row_var_hist[len(inds)] += 1; cap_hist[int(cap)] += 1
        if cap < 0:
            model.AddBoolOr([]); added += 1; empty += 1
        elif len(inds) <= cap:
            skipped += 1
        else:
            model.Add(sum(x[i] for i in inds) <= int(cap)); added += 1
        if len(witness_head) < 50:
            w = dict(wit); w['intersection_size'] = len(inds); w['cap'] = int(cap); witness_head.append(w)
    build_elapsed = time.time() - t0
    solver = cp_model.CpSolver(); solver.parameters.max_time_in_seconds = time_limit; solver.parameters.num_search_workers = workers
    t1 = time.time(); st = solver.Solve(model); solve_elapsed = time.time() - t1
    names = {cp_model.OPTIMAL:'OPTIMAL', cp_model.FEASIBLE:'FEASIBLE', cp_model.INFEASIBLE:'INFEASIBLE', cp_model.UNKNOWN:'UNKNOWN', cp_model.MODEL_INVALID:'MODEL_INVALID'}
    sol = None
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = [r1_pts[i] for i in range(len(r1_pts)) if solver.Value(x[i])]
    return {
        'problem': 'CP-SAT exact rank-1 skeleton with fixed higher-rank A-prefix',
        'field': 'F2', 'rank_s_for_capacities': rank_s, 'exact_rank1_count': exact_rank1_count,
        'fixed_rank1_points': list(fixed_rank1), 'fixed_high_points': list(fixed_high),
        'fixed_high_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in fixed_high).items())),
        'rank1_points': r1_pts,
        'compression': {'compressed_intersections': len(tight), 'nonvacuous_constraints': len(cons), 'constraint_size_cap_hist': {f'{a},{b}': c for (a,b),c in sorted(row_hist.items())}, 'raw_by_dim': dict(sorted(raw_by_dim.items())), 'raw_by_lb': dict(sorted(raw_by_lb.items())), 'fixed_high_in_row_hist': dict(sorted(fixed_high_in_hist.items())), 'raw_residual_cap_hist': dict(sorted(raw_residual_cap_hist.items()))},
        'rows_added': added, 'skipped_vacuous': skipped, 'empty_rows': empty, 'row_var_hist': dict(sorted(row_var_hist.items())), 'cap_hist': dict(sorted(cap_hist.items())), 'witness_head': witness_head,
        'solver_status': names.get(st, str(st)), 'solver_status_code': int(st), 'solver_walltime': float(solver.WallTime()), 'solver_num_conflicts': int(solver.NumConflicts()), 'solver_num_branches': int(solver.NumBranches()),
        'build_elapsed_sec': build_elapsed, 'solve_elapsed_sec': solve_elapsed,
        'support_rank1': sol, 'support_rank1_size': None if sol is None else len(sol),
        'support_all_fixed_prefix': None if sol is None else sorted(list(sol) + list(fixed_high)),
        'support_all_size_with_fixed_high': None if sol is None else len(sol) + len(fixed_high),
        'lut_meta_brief': {'coverage_ok': lut_meta.get('coverage_ok'), 'conflict_count': lut_meta.get('conflict_count'), 'subspace_count': lut_meta.get('subspace_count')},
        'meaning': 'SAT/OPTIMAL is a rank-1 skeleton candidate under the fixed high prefix. INFEASIBLE should be converted to CNF/DRAT before theorem use.'
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank-s', type=int, default=20)
    ap.add_argument('--exact-rank1-count', type=int, default=18)
    ap.add_argument('--fixed-rank1', default='1')
    ap.add_argument('--fixed-high', required=True)
    ap.add_argument('--time-limit', type=float, default=120)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    fixed_rank1 = parse_ints(args.fixed_rank1); fixed_high = parse_ints(args.fixed_high)
    lut, meta = load_lut(args.lut)
    print(f'loaded LUT {len(lut):,} coverage={meta.get("coverage_ok")} conflicts={meta.get("conflict_count")} fixed_rank1={fixed_rank1} fixed_high={fixed_high}', flush=True)
    res = solve_one(lut, meta, fixed_rank1, fixed_high, args.exact_rank1_count, args.rank_s, args.time_limit, args.workers)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(res, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: res[k] for k in ['solver_status','support_rank1_size','support_all_size_with_fixed_high','fixed_rank1_points','fixed_high_points','rows_added','build_elapsed_sec','solve_elapsed_sec']}, indent=2, sort_keys=True))
    print('saved', args.out)


if __name__ == '__main__':
    main()
