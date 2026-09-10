#!/usr/bin/env python3
"""Lazy full-Wang-LUT solver for the nonadjacent rank-1 matching branch.

This is the analysis global-cover branch where, after fixing E11 as one rank-1
A-factor, all selected rank-1 A-factors are required to form a matching in the
7x7 Segre grid.  The script starts from a chosen row family, solves CP-SAT,
then scans every support candidate against the full expanded Wang LUT and adds
violated rows.  It is a search/evidence instrument, not a proof checker.
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

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from precompute_skeleton_system import pack_bases_numpy, vectorized_multi_membership  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11, parse_dims  # noqa: E402
from wang_capacity_lazy import in_rowspace, matrix_rank_of_mask, subspace_points_from_basis, unpack_basis  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def outer_mask(u: int, v: int) -> int:
    mask = 0
    for i in range(3):
        if (u >> i) & 1:
            mask |= int(v) << (3 * i)
    return mask


def rank1_uv_map() -> dict[int, tuple[int, int]]:
    out = {outer_mask(u, v): (u, v) for u in range(1, 8) for v in range(1, 8)}
    rank1 = [p for p in range(1, 512) if matrix_rank_of_mask(p) == 1]
    if set(out) != set(rank1) or len(out) != 49:
        raise RuntimeError('rank1 uv map mismatch')
    return out


def support_matching_ok(support: Sequence[int], uv: dict[int, tuple[int, int]]) -> bool:
    used_u = set(); used_v = set()
    for p in support:
        if int(p) not in uv:
            continue
        u, v = uv[int(p)]
        if u in used_u or v in used_v:
            return False
        used_u.add(u); used_v.add(v)
    return True


def add_row_cut(model, x: dict[int, object], key: int, lb: int, rank_s: int, added_keys: set[int], reason: str, records: list[dict]) -> bool:
    if int(key) in added_keys:
        return False
    pts = subspace_points_from_basis(unpack_basis(int(key)))
    cap = int(rank_s) - int(lb)
    if cap < 0:
        model.AddBoolOr([])
        mode = 'empty'
    elif len(pts) <= cap:
        mode = 'vacuous'
    else:
        model.Add(sum(x[p] for p in pts) <= cap)
        mode = 'atmost'
    added_keys.add(int(key))
    records.append({'key': int(key), 'dim': int(key) & 0xF, 'lb': int(lb), 'cap': int(cap), 'point_count': len(pts), 'reason': reason, 'mode': mode})
    return mode != 'vacuous'


def initial_rows(lut: dict[int, int], include_dims: Set[int], through_e11_dims: Set[int]) -> list[tuple[int, int, str]]:
    rows = []
    for key, lb in lut.items():
        d = int(key) & 0xF
        if d in include_dims:
            rows.append((int(key), int(lb), f'include_dim_{d}'))
        elif d in through_e11_dims:
            basis = unpack_basis(int(key))
            if in_rowspace(E11, basis, n=9):
                rows.append((int(key), int(lb), f'through_E11_dim_{d}'))
    return rows


def full_lut_violations_vectorized(support: Sequence[int], keys: list[int], lbs: np.ndarray, bases: np.ndarray, rank_s: int,
                                   max_store: int) -> tuple[list[dict], dict]:
    t0 = time.time()
    occ = vectorized_multi_membership(bases, [int(p) for p in support]).astype(np.int16)
    caps = int(rank_s) - lbs.astype(np.int16)
    bad_idx = np.nonzero(occ > caps)[0]
    # Sort by excess, lb, occupancy, and lower dimension preference roughly matching older scanners.
    order = sorted((int(i) for i in bad_idx), key=lambda i: (int(occ[i] - caps[i]), int(lbs[i]), int(occ[i]), -(int(keys[i]) & 0xF)), reverse=True)
    violations = []
    by_dim = Counter(); by_dim_lb = Counter(); by_excess = Counter()
    max_excess = 0
    for i in order:
        key = int(keys[i]); lb = int(lbs[i]); cap = int(caps[i]); o = int(occ[i]); excess = o - cap
        d = key & 0xF
        by_dim[d] += 1; by_dim_lb[(d, lb)] += 1; by_excess[excess] += 1; max_excess = max(max_excess, excess)
        if len(violations) < max_store:
            violations.append({'key': key, 'dim': d, 'lb': lb, 'cap': cap, 'occupancy': o, 'excess': excess, 'basis': list(unpack_basis(key))})
    stats = {
        'checked_keys': len(keys),
        'violation_count': int(len(bad_idx)),
        'max_excess': int(max_excess),
        'violations_by_dim': dict(sorted(by_dim.items())),
        'violations_by_dim_lb': {f'{d},{lb}': c for (d, lb), c in sorted(by_dim_lb.items())},
        'violations_by_excess': dict(sorted(by_excess.items())),
        'elapsed_sec': time.time() - t0,
    }
    return violations, stats


def main() -> None:
    from ortools.sat.python import cp_model
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--include-dims', default='1')
    ap.add_argument('--through-e11-dims', default='4,6')
    ap.add_argument('--max-iters', type=int, default=8)
    ap.add_argument('--solver-time', type=float, default=120.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--add-cuts-per-iter', type=int, default=1000)
    ap.add_argument('--store-violations-per-iter', type=int, default=5000)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--candidate-out', type=Path, default=None)
    args = ap.parse_args()
    if args.k < 1 or args.k > 7:
        raise ValueError('matching branch requires 1 <= k <= 7')

    t_all = time.time()
    lut, lmeta = load_lut(args.lut)
    keys = list(lut.keys())
    print(f'loaded LUT {len(lut):,}; packing bases...', flush=True)
    bases, dims, lbs = pack_bases_numpy(lut)
    uv = rank1_uv_map()
    rank1_pts = sorted(uv)
    pts = list(range(1, 512))

    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f'x_{p}') for p in pts}
    model.Add(sum(x.values()) == args.rank)
    model.Add(x[E11] == 1)
    model.Add(sum(x[p] for p in rank1_pts) == args.k)
    for u in range(1, 8):
        model.Add(sum(x[outer_mask(u, v)] for v in range(1, 8)) <= 1)
    for v in range(1, 8):
        model.Add(sum(x[outer_mask(u, v)] for u in range(1, 8)) <= 1)

    added_keys: set[int] = set()
    cut_records: list[dict] = []
    init = initial_rows(lut, parse_dims(args.include_dims), parse_dims(args.through_e11_dims))
    init_added_effective = 0
    for key, lb, reason in init:
        if add_row_cut(model, x, key, lb, args.rank, added_keys, reason, cut_records):
            init_added_effective += 1
    print(f'initial rows requested={len(init):,} effective={init_added_effective:,}', flush=True)

    history = []
    final_status = None
    final_support = None
    for it in range(1, args.max_iters + 1):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = args.solver_time
        solver.parameters.num_search_workers = args.workers
        solver.parameters.random_seed = 27000 + it
        t0 = time.time(); st = solver.Solve(model); solve_sec = time.time() - t0
        status = {cp_model.OPTIMAL: 'OPTIMAL', cp_model.FEASIBLE: 'FEASIBLE', cp_model.INFEASIBLE: 'INFEASIBLE', cp_model.UNKNOWN: 'UNKNOWN', cp_model.MODEL_INVALID: 'MODEL_INVALID'}.get(st, str(st))
        entry = {
            'iteration': it,
            'solver_status': status,
            'solver_walltime': float(solver.WallTime()),
            'solver_num_conflicts': int(solver.NumConflicts()),
            'solver_num_branches': int(solver.NumBranches()),
            'solve_elapsed_sec': solve_sec,
            'cut_count_total': len(added_keys),
        }
        print(f'iter {it}: {status}, cuts={len(added_keys):,}, solve={solve_sec:.1f}s', flush=True)
        if st == cp_model.INFEASIBLE:
            final_status = 'INFEASIBLE'
            history.append(entry)
            break
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            final_status = status
            history.append(entry)
            break
        support = [p for p in pts if solver.Value(x[p])]
        entry['support'] = support
        entry['support_rank_hist'] = dict(sorted(Counter(matrix_rank_of_mask(p) for p in support).items()))
        entry['support_rank1_uv'] = [{'point': p, 'u': uv[p][0], 'v': uv[p][1]} for p in support if p in uv]
        entry['support_matching_ok'] = support_matching_ok(support, uv)
        violations, stats = full_lut_violations_vectorized(support, keys, lbs, bases, args.rank, args.store_violations_per_iter)
        entry['full_lut_scan'] = stats
        entry['violations_head'] = violations[:80]
        print(f'  full LUT violations={stats["violation_count"]:,}, max_excess={stats["max_excess"]}, scan={stats["elapsed_sec"]:.1f}s', flush=True)
        if stats['violation_count'] == 0:
            final_status = 'FULL_LUT_FEASIBLE_SUPPORT'
            final_support = support
            if args.candidate_out is not None:
                cand = {
                    'problem': 'matching-branch full-Wang-LUT A-support candidate',
                    'field': 'F2',
                    'rank_s': args.rank,
                    'exact_rank1_count': args.k,
                    'support': support,
                    'support_rank_hist': entry['support_rank_hist'],
                    'support_rank1_uv': entry['support_rank1_uv'],
                    'meaning': 'Satisfies all expanded Wang occupation inequalities as scanned here; still only an A-support necessary-condition object, not a tensor decomposition.',
                }
                args.candidate_out.parent.mkdir(parents=True, exist_ok=True)
                args.candidate_out.write_text(json.dumps(cand, indent=2, sort_keys=True) + '\n')
            history.append(entry)
            break
        added = 0
        for v in violations[:args.add_cuts_per_iter]:
            if add_row_cut(model, x, int(v['key']), int(v['lb']), args.rank, added_keys, f'lazy_iter_{it}', cut_records):
                added += 1
        entry['lazy_cuts_added'] = added
        entry['lazy_cut_keys_head'] = [int(v['key']) for v in violations[:min(len(violations), args.add_cuts_per_iter, 50)]]
        history.append(entry)
        if added == 0:
            final_status = 'STALLED_NO_NEW_CUTS'
            final_support = support
            break

    payload = {
        'problem': 'lazy full-Wang-LUT matching-branch CP-SAT',
        'field': 'F2',
        'rank_s': args.rank,
        'fixed_rank1_anchor': E11,
        'exact_rank1_count': args.k,
        'initial_include_dims': sorted(parse_dims(args.include_dims)),
        'initial_through_e11_dims': sorted(parse_dims(args.through_e11_dims)),
        'initial_row_count_requested': len(init),
        'initial_row_count_effective': init_added_effective,
        'final_status': final_status,
        'final_support': final_support,
        'iteration_count': len(history),
        'history': history,
        'cut_count_total': len(added_keys),
        'cuts_by_reason': dict(sorted(Counter(r['reason'] for r in cut_records).items())),
        'cuts_by_dim_lb': {f'{d},{lb}': c for (d, lb), c in sorted(Counter((r['dim'], r['lb']) for r in cut_records).items())},
        'cut_records_head': cut_records[:120],
        'cut_records_tail': cut_records[-120:],
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'elapsed_sec': time.time() - t_all,
        'proof_status': 'CP-SAT/lazy evidence only; INFEASIBLE or cut-derived conclusions require independent proof replay before lower-bound use.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True, default=str) + '\n')
    print(json.dumps({
        'k': args.k,
        'final_status': final_status,
        'iteration_count': len(history),
        'cut_count_total': len(added_keys),
        'elapsed_sec': payload['elapsed_sec'],
        'out': str(args.out),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
