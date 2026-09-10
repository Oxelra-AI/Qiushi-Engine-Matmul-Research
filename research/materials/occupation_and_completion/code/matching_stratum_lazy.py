#!/usr/bin/env python3
"""Lazy full-LUT solver for one fixed anchored matching stratum.

A rank-1 matching M is fixed exactly (including E11).  The variables are only
higher-rank projective A-points, and the solver selects exactly 20-|M| of them.
After each CP-SAT candidate, the complete expanded Wang LUT is scanned; violated
rows are added with residual capacity 20-L(Phi)-|M cap Phi|.

This differs from matching_lazy_full_lut.py by conditioning on the whole
rank-1 matching geometry, not merely the count and matching constraints.
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
    if set(out) != set(rank1) or len(out) != 49 or out.get(E11) != (1, 1):
        raise RuntimeError('rank1 uv map mismatch')
    return out


def parse_matching(spec: str) -> list[int]:
    return sorted(int(x) for x in spec.replace(';', ',').split(',') if x.strip())


def matching_ok(points: Sequence[int], uv: dict[int, tuple[int, int]]) -> bool:
    us: set[int] = set(); vs: set[int] = set()
    for p in points:
        if int(p) not in uv:
            return False
        u, v = uv[int(p)]
        if u in us or v in vs:
            return False
        us.add(u); vs.add(v)
    return True


def collect_keys_from_json(path: Path) -> set[int]:
    data = json.loads(path.read_text())
    out: set[int] = set()
    def visit(obj):
        if isinstance(obj, dict):
            if 'key' in obj and ('lb' in obj or 'dim' in obj or 'occupancy' in obj or 'cap' in obj):
                try:
                    out.add(int(obj['key']))
                except Exception:
                    pass
            for v in obj.values():
                visit(v)
        elif isinstance(obj, list):
            for v in obj:
                visit(v)
    visit(data)
    return out


def initial_rows(lut: dict[int, int], include_dims: set[int], through_e11_dims: set[int], seed_keys: set[int]) -> list[tuple[int, int, str]]:
    rows = []
    for key0, lb0 in lut.items():
        key = int(key0); lb = int(lb0); d = key & 0xF
        source = None
        if d in include_dims:
            source = f'include_dim_{d}'
        elif d in through_e11_dims:
            basis = unpack_basis(key)
            if in_rowspace(E11, basis, n=9):
                source = f'through_E11_dim_{d}'
        if source is None and key in seed_keys:
            source = 'seed'
        if source is not None:
            rows.append((key, lb, source))
    return rows


def add_row_cut(model, y: dict[int, object], matching: Sequence[int], key: int, lb: int, rank_s: int,
                added_keys: set[int], reason: str, records: list[dict]) -> str | None:
    key = int(key)
    if key in added_keys:
        return None
    basis = unpack_basis(key)
    pts = subspace_points_from_basis(basis)
    selected_r1_occ = sum(1 for p in matching if p in pts)
    residual_cap = int(rank_s) - int(lb) - selected_r1_occ
    vars_in = [y[p] for p in pts if p in y]
    if residual_cap < 0:
        model.AddBoolOr([])
        mode = 'empty'
    elif len(vars_in) <= residual_cap:
        mode = 'vacuous'
    else:
        model.Add(sum(vars_in) <= residual_cap)
        mode = 'atmost'
    added_keys.add(key)
    records.append({
        'key': key, 'dim': key & 0xF, 'lb': int(lb), 'cap_before_rank1': int(rank_s) - int(lb),
        'selected_rank1_in_row': int(selected_r1_occ), 'residual_cap': int(residual_cap),
        'hr_vars_in_row': len(vars_in), 'reason': reason, 'mode': mode,
    })
    return mode


def scan_support(support: Sequence[int], key_list: list[int], lbs: np.ndarray, bases: np.ndarray, rank_s: int,
                 max_store: int) -> tuple[list[dict], dict]:
    t0 = time.time()
    occ = vectorized_multi_membership(bases, [int(p) for p in support]).astype(np.int16)
    caps = int(rank_s) - lbs.astype(np.int16)
    bad_idx = np.nonzero(occ > caps)[0]
    order = sorted((int(i) for i in bad_idx), key=lambda i: (int(occ[i] - caps[i]), int(lbs[i]), int(occ[i]), -(key_list[i] & 0xF)), reverse=True)
    violations = []
    by_dim = Counter(); by_dim_lb = Counter(); by_excess = Counter(); max_excess = 0
    for i in order:
        key = int(key_list[i]); lb = int(lbs[i]); cap = int(caps[i]); o = int(occ[i]); ex = int(o - cap); d = key & 0xF
        by_dim[d] += 1; by_dim_lb[(d, lb)] += 1; by_excess[ex] += 1; max_excess = max(max_excess, ex)
        if len(violations) < max_store:
            violations.append({'key': key, 'dim': d, 'lb': lb, 'cap': cap, 'occupancy': o, 'excess': ex, 'basis': list(unpack_basis(key))})
    stats = {
        'checked_keys': len(key_list),
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
    ap.add_argument('--matching', required=True, help='comma-separated fixed rank-1 points, including E11')
    ap.add_argument('--include-dims', default='1')
    ap.add_argument('--through-e11-dims', default='')
    ap.add_argument('--seed-json', type=Path, action='append', default=[])
    ap.add_argument('--max-iters', type=int, default=8)
    ap.add_argument('--solver-time', type=float, default=30.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--add-cuts-per-iter', type=int, default=2000)
    ap.add_argument('--store-violations-per-iter', type=int, default=5000)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--candidate-out', type=Path, default=None)
    args = ap.parse_args()

    t_all = time.time()
    uv = rank1_uv_map()
    matching = parse_matching(args.matching)
    if E11 not in matching or not matching_ok(matching, uv):
        raise ValueError(f'bad anchored matching {matching}')
    rank1_all = set(uv)
    hr_pts = [p for p in range(1, 512) if p not in rank1_all]
    target_hr = int(args.rank) - len(matching)
    if target_hr < 0 or target_hr > len(hr_pts):
        raise ValueError('bad target_hr')

    seed_keys: set[int] = set()
    for sp in args.seed_json:
        got = collect_keys_from_json(sp)
        print(f'seed {sp}: {len(got)} keys', flush=True)
        seed_keys.update(got)
    lut, lmeta = load_lut(args.lut)
    key_list = [int(k) for k in lut.keys()]
    print(f'loaded LUT {len(lut):,}; packing bases...', flush=True)
    bases, _, lbs_u8 = pack_bases_numpy(lut)
    lbs = np.array([int(v) for v in lut.values()], dtype=np.int16)

    model = cp_model.CpModel()
    y = {p: model.NewBoolVar(f'y_{p}') for p in hr_pts}
    model.Add(sum(y.values()) == target_hr)

    added_keys: set[int] = set()
    cut_records: list[dict] = []
    requested = initial_rows(lut, parse_dims(args.include_dims), parse_dims(args.through_e11_dims), seed_keys)
    effective = 0; vacuous = 0; empty = 0
    for key, lb, reason in requested:
        mode = add_row_cut(model, y, matching, key, lb, args.rank, added_keys, reason, cut_records)
        if mode == 'vacuous':
            vacuous += 1
        elif mode == 'empty':
            effective += 1; empty += 1
        elif mode == 'atmost':
            effective += 1
    print(f'initial rows requested={len(requested):,} effective={effective:,} vacuous={vacuous:,} empty={empty}', flush=True)

    history = []
    final_status = None
    final_support = None
    for it in range(1, args.max_iters + 1):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(args.solver_time)
        solver.parameters.num_search_workers = int(args.workers)
        solver.parameters.random_seed = 28000 + it
        t0 = time.time(); st = solver.Solve(model); solve_sec = time.time() - t0
        status = solver.StatusName(st)
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
        high = [p for p in hr_pts if solver.Value(y[p])]
        support = sorted(matching + high)
        entry['support'] = support
        entry['support_rank_hist'] = dict(sorted(Counter(matrix_rank_of_mask(p) for p in support).items()))
        entry['selected_high_head'] = high[:80]
        entry['fixed_rank1_matching_uv'] = [{'point': p, 'u': uv[p][0], 'v': uv[p][1]} for p in matching]
        violations, stats = scan_support(support, key_list, lbs, bases, args.rank, args.store_violations_per_iter)
        entry['full_lut_scan'] = stats
        entry['violations_head'] = violations[:100]
        print(f'  full LUT violations={stats["violation_count"]:,}, max_excess={stats["max_excess"]}, scan={stats["elapsed_sec"]:.1f}s', flush=True)
        if stats['violation_count'] == 0:
            final_status = 'FULL_LUT_FEASIBLE_SUPPORT'
            final_support = support
            if args.candidate_out is not None:
                args.candidate_out.parent.mkdir(parents=True, exist_ok=True)
                args.candidate_out.write_text(json.dumps({
                    'problem': 'fixed matching stratum full-Wang-LUT A-support candidate',
                    'field': 'F2', 'rank_s': args.rank, 'fixed_rank1_matching': matching,
                    'support': support, 'support_rank_hist': entry['support_rank_hist'],
                    'meaning': 'A-side Wang necessary-condition object only, not a tensor decomposition.',
                }, indent=2, sort_keys=True) + '\n')
            history.append(entry)
            break
        added = 0; added_modes = Counter()
        for v in violations[:args.add_cuts_per_iter]:
            mode = add_row_cut(model, y, matching, int(v['key']), int(v['lb']), args.rank, added_keys, f'lazy_iter_{it}', cut_records)
            if mode is not None:
                added_modes[mode] += 1
                if mode != 'vacuous':
                    added += 1
        entry['lazy_cuts_effective_added'] = added
        entry['lazy_cut_modes'] = dict(sorted(added_modes.items()))
        entry['lazy_cut_keys_head'] = [int(v['key']) for v in violations[:min(len(violations), args.add_cuts_per_iter, 80)]]
        history.append(entry)
        if added == 0:
            final_status = 'STALLED_NO_EFFECTIVE_NEW_CUTS'
            final_support = support
            break

    payload = {
        'problem': 'lazy full-Wang-LUT fixed matching stratum higher-rank completion',
        'field': 'F2',
        'rank_s': int(args.rank),
        'fixed_rank1_matching': matching,
        'fixed_rank1_matching_uv': [{'point': p, 'u': uv[p][0], 'v': uv[p][1]} for p in matching],
        'total_rank1_k': len(matching),
        'target_higher_rank_count': target_hr,
        'initial_include_dims': sorted(parse_dims(args.include_dims)),
        'initial_through_e11_dims': sorted(parse_dims(args.through_e11_dims)),
        'seed_key_count': len(seed_keys),
        'initial_rows_requested': len(requested),
        'initial_rows_effective': effective,
        'initial_rows_vacuous': vacuous,
        'initial_rows_empty': empty,
        'final_status': final_status,
        'final_support': final_support,
        'iteration_count': len(history),
        'history': history,
        'cut_count_total': len(added_keys),
        'core_keys_all': sorted(int(k) for k in added_keys),
        'core_keys_effective': sorted(int(r['key']) for r in cut_records if r.get('mode') != 'vacuous'),
        'cuts_by_reason': dict(sorted(Counter(r['reason'] for r in cut_records).items())),
        'cuts_by_mode': dict(sorted(Counter(r['mode'] for r in cut_records).items())),
        'cuts_by_dim_lb': {f'{d},{lb}': c for (d, lb), c in sorted(Counter((r['dim'], r['lb']) for r in cut_records).items())},
        'cut_records_head': cut_records[:120],
        'cut_records_tail': cut_records[-120:],
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'elapsed_sec': time.time() - t_all,
        'proof_status': 'CP-SAT/lazy evidence only; not a checked lower-bound proof.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'matching': matching,
        'k': len(matching),
        'target_hr': target_hr,
        'final_status': final_status,
        'iteration_count': len(history),
        'cut_count_total': len(added_keys),
        'cuts_by_mode': payload['cuts_by_mode'],
        'elapsed_sec': payload['elapsed_sec'],
        'out': str(args.out),
    }, indent=2, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
