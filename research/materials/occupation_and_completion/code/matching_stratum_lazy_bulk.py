#!/usr/bin/env python3
"""Bulk lazy full-LUT probes for fixed anchored matching strata.

Loads the expanded Wang LUT and packed bases once, then runs the fixed-rank1
matching-stratum lazy completion loop for many representative matchings.  This
is designed to test whether the analysis stratum conditioning scales beyond k=7.
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

from precompute_skeleton_system import pack_bases_numpy  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11, parse_dims  # noqa: E402
from wang_capacity_lazy import in_rowspace, matrix_rank_of_mask, unpack_basis  # noqa: E402
from matching_stratum_lazy import (  # noqa: E402
    add_row_cut,
    collect_keys_from_json,
    matching_ok,
    rank1_uv_map,
    scan_support,
)


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def all_representatives(classification: dict) -> list[dict]:
    out = []
    for k_s, arr in classification['representatives_by_k'].items():
        for rec in arr:
            r = dict(rec)
            r['k'] = int(k_s)
            out.append(r)
    out.sort(key=lambda r: (r['k'], tuple(r['canonical'])))
    return out


def initial_rows_once(lut: dict[int, int], include_dims: set[int], through_e11_dims: set[int], seed_keys: set[int]) -> list[tuple[int, int, str]]:
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


def run_one(matching: Sequence[int], *, lut_meta: dict, key_list: list[int], lbs: np.ndarray, bases: np.ndarray,
            requested_rows: list[tuple[int, int, str]], rank_s: int, max_iters: int, solver_time: float,
            workers: int, add_cuts_per_iter: int, store_violations_per_iter: int, out: Path) -> dict:
    from ortools.sat.python import cp_model
    t_all = time.time()
    uv = rank1_uv_map()
    matching = sorted(int(p) for p in matching)
    if E11 not in matching or not matching_ok(matching, uv):
        raise ValueError(f'bad anchored matching {matching}')
    rank1_all = set(uv)
    hr_pts = [p for p in range(1, 512) if p not in rank1_all]
    target_hr = int(rank_s) - len(matching)

    model = cp_model.CpModel()
    y = {p: model.NewBoolVar(f'y_{p}') for p in hr_pts}
    model.Add(sum(y.values()) == target_hr)
    added_keys: set[int] = set()
    cut_records: list[dict] = []
    effective = vacuous = empty = 0
    for key, lb, reason in requested_rows:
        mode = add_row_cut(model, y, matching, key, lb, rank_s, added_keys, reason, cut_records)
        if mode == 'vacuous':
            vacuous += 1
        elif mode == 'empty':
            effective += 1; empty += 1
        elif mode == 'atmost':
            effective += 1

    history = []
    final_status = None
    final_support = None
    for it in range(1, max_iters + 1):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(solver_time)
        solver.parameters.num_search_workers = int(workers)
        solver.parameters.random_seed = 28100 + 17 * len(matching) + it
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
        violations, stats = scan_support(support, key_list, lbs, bases, rank_s, store_violations_per_iter)
        entry['full_lut_scan'] = stats
        entry['violations_head'] = violations[:80]
        if stats['violation_count'] == 0:
            final_status = 'FULL_LUT_FEASIBLE_SUPPORT'
            final_support = support
            history.append(entry)
            break
        added = 0; added_modes = Counter()
        for v in violations[:add_cuts_per_iter]:
            mode = add_row_cut(model, y, matching, int(v['key']), int(v['lb']), rank_s, added_keys, f'lazy_iter_{it}', cut_records)
            if mode is not None:
                added_modes[mode] += 1
                if mode != 'vacuous':
                    added += 1
        entry['lazy_cuts_effective_added'] = added
        entry['lazy_cut_modes'] = dict(sorted(added_modes.items()))
        entry['lazy_cut_keys_head'] = [int(v['key']) for v in violations[:min(len(violations), add_cuts_per_iter, 80)]]
        history.append(entry)
        if added == 0:
            final_status = 'STALLED_NO_EFFECTIVE_NEW_CUTS'
            final_support = support
            break
    payload = {
        'problem': 'bulk lazy full-Wang-LUT fixed matching stratum higher-rank completion',
        'field': 'F2',
        'rank_s': int(rank_s),
        'fixed_rank1_matching': matching,
        'fixed_rank1_matching_uv': [{'point': p, 'u': uv[p][0], 'v': uv[p][1]} for p in matching],
        'total_rank1_k': len(matching),
        'target_higher_rank_count': target_hr,
        'initial_rows_requested': len(requested_rows),
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
        'cut_records_head': cut_records[:100],
        'cut_records_tail': cut_records[-100:],
        'lut_meta_brief': {'coverage_ok': lut_meta.get('coverage_ok'), 'conflict_count': lut_meta.get('conflict_count'), 'subspace_count': lut_meta.get('subspace_count')},
        'elapsed_sec': time.time() - t_all,
        'proof_status': 'CP-SAT/lazy evidence only; not a checked lower-bound proof.',
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    return payload


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--classification', type=Path, default=Path('data/matching_strata/anchored_matching_strata.json'))
    ap.add_argument('--profile', type=Path, default=Path('data/matching_strata/matching_stratum_residual_profile.json'))
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--k', type=int, action='append', default=None)
    ap.add_argument('--only-profile-ok', action='store_true')
    ap.add_argument('--max-strata', type=int, default=0)
    ap.add_argument('--include-dims', default='1')
    ap.add_argument('--through-e11-dims', default='')
    ap.add_argument('--seed-json', type=Path, action='append', default=[])
    ap.add_argument('--max-iters', type=int, default=4)
    ap.add_argument('--solver-time', type=float, default=20.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--add-cuts-per-iter', type=int, default=1500)
    ap.add_argument('--store-violations-per-iter', type=int, default=3000)
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--summary', type=Path, required=True)
    args = ap.parse_args()

    t0 = time.time()
    classification = json.loads(args.classification.read_text())
    reps = all_representatives(classification)
    if args.k is not None:
        use_k = set(int(k) for k in args.k)
        reps = [r for r in reps if int(r['k']) in use_k]
    if args.only_profile_ok:
        profile = json.loads(args.profile.read_text())
        ok_set = {tuple(int(p) for p in r['canonical']) for r in profile['records'] if r.get('rank1_only_status') == 'OK'}
        reps = [r for r in reps if tuple(int(p) for p in r['canonical']) in ok_set]
    reps.sort(key=lambda r: (int(r['k']), -int(r.get('enumerated_members', 0)), tuple(r['canonical'])))
    if args.max_strata > 0:
        reps = reps[:args.max_strata]

    seed_keys: set[int] = set()
    for sp in args.seed_json:
        got = collect_keys_from_json(sp)
        print(f'seed {sp}: {len(got)} keys', flush=True)
        seed_keys.update(got)
    lut, lmeta = load_lut(args.lut)
    key_list = [int(k) for k in lut.keys()]
    lbs = np.array([int(v) for v in lut.values()], dtype=np.int16)
    print(f'loaded LUT {len(lut):,}; packing bases once...', flush=True)
    bases, _, _ = pack_bases_numpy(lut)
    requested_rows = initial_rows_once(lut, parse_dims(args.include_dims), parse_dims(args.through_e11_dims), seed_keys)
    print(f'will probe {len(reps)} strata; initial rows={len(requested_rows):,}; seed_keys={len(seed_keys)}', flush=True)

    args.outdir.mkdir(parents=True, exist_ok=True)
    records = []
    for idx, rec in enumerate(reps):
        matching = [int(p) for p in rec['canonical']]
        out = args.outdir / f'lazy_k{len(matching):02d}_idx{idx:03d}_can_{"_".join(map(str, matching))}.json'
        q = run_one(matching, lut_meta=lmeta, key_list=key_list, lbs=lbs, bases=bases, requested_rows=requested_rows,
                    rank_s=args.rank, max_iters=args.max_iters, solver_time=args.solver_time, workers=args.workers,
                    add_cuts_per_iter=args.add_cuts_per_iter, store_violations_per_iter=args.store_violations_per_iter,
                    out=out)
        record = {
            'idx': idx,
            'k': len(matching),
            'canonical': matching,
            'enumerated_members': int(rec.get('enumerated_members', 0)),
            'path': str(out),
            'final_status': q['final_status'],
            'iteration_count': q['iteration_count'],
            'cut_count_total': q['cut_count_total'],
            'target_higher_rank_count': q['target_higher_rank_count'],
            'candidate_violation_counts': [it.get('full_lut_scan', {}).get('violation_count') for it in q['history'] if 'full_lut_scan' in it],
            'candidate_max_excess': [it.get('full_lut_scan', {}).get('max_excess') for it in q['history'] if 'full_lut_scan' in it],
            'elapsed_sec': q['elapsed_sec'],
        }
        records.append(record)
        summary = {
            'problem': 'bulk fixed matching stratum lazy probe summary',
            'field': 'F2',
            'classification_path': str(args.classification),
            'profile_path': str(args.profile),
            'k_filter': None if args.k is None else sorted(int(k) for k in args.k),
            'only_profile_ok': bool(args.only_profile_ok),
            'include_dims': sorted(parse_dims(args.include_dims)),
            'through_e11_dims': sorted(parse_dims(args.through_e11_dims)),
            'seed_key_count': len(seed_keys),
            'max_iters': args.max_iters,
            'solver_time': args.solver_time,
            'add_cuts_per_iter': args.add_cuts_per_iter,
            'records': records,
            'status_hist_so_far': dict(sorted(Counter(r['final_status'] for r in records).items())),
            'elapsed_sec': time.time() - t0,
        }
        args.summary.parent.mkdir(parents=True, exist_ok=True)
        args.summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
        print(json.dumps(record, sort_keys=True), flush=True)
    print(json.dumps(summary, indent=2, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
