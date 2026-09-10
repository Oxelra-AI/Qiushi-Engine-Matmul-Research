#!/usr/bin/env python3
"""Deletion shrink for fixed-matching row cores.

Unlike assumption-core extraction, this repeatedly solves ordinary unguarded
CP-SAT subformulas.  If removing a chunk of Wang row keys preserves
infeasibility, the chunk is permanently removed.  The output is still only a
CP-SAT-shrunk row-core target; independent CNF/DRAT replay is required.
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

from fixed_matching_rowcore_cnf import matching_ok, rank1_points  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11  # noqa: E402
from wang_capacity_lazy import matrix_rank_of_mask, subspace_points_from_basis, unpack_basis  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def extract_keys(payload: dict) -> list[int]:
    if payload.get('core_keys_effective'):
        return sorted({int(k) for k in payload['core_keys_effective']})
    if payload.get('core_keys_all'):
        return sorted({int(k) for k in payload['core_keys_all']})
    keys = [int(r['key']) for r in payload.get('cut_records', []) if r.get('mode') != 'vacuous']
    out = sorted(set(keys))
    if not out:
        raise ValueError('no keys; rerun lazy with core_keys_effective')
    return out


def solve_keys(lut: dict[int, int], matching: Sequence[int], keys: Sequence[int], *, rank_s: int, time_limit: float, workers: int) -> dict:
    from ortools.sat.python import cp_model
    t0 = time.time()
    matching = sorted(int(p) for p in matching)
    if E11 not in matching or not matching_ok(matching):
        raise ValueError(f'bad matching {matching}')
    r1 = rank1_points()
    hr_pts = [p for p in range(1, 512) if p not in r1]
    target_hr = rank_s - len(matching)
    model = cp_model.CpModel()
    y = {p: model.NewBoolVar(f'y_{p}') for p in hr_pts}
    model.Add(sum(y.values()) == target_hr)
    added = skipped = empty = 0
    row_hist = Counter(); row_var_hist = Counter(); cap_hist = Counter(); fixed_occ_hist = Counter()
    for key0 in keys:
        key = int(key0)
        lb = int(lut[key])
        basis = unpack_basis(key)
        pts = subspace_points_from_basis(basis)
        fixed_occ = sum(1 for p in matching if p in pts)
        cap = rank_s - lb - fixed_occ
        vars_in = [y[p] for p in pts if p in y]
        row_hist[(key & 0xF, lb)] += 1; row_var_hist[len(vars_in)] += 1; cap_hist[cap] += 1; fixed_occ_hist[fixed_occ] += 1
        if cap < 0:
            model.AddBoolOr([]); added += 1; empty += 1
        elif len(vars_in) <= cap:
            skipped += 1
        else:
            model.Add(sum(vars_in) <= cap); added += 1
    build_sec = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = 283000 + len(keys)
    t1 = time.time(); st = solver.Solve(model); solve_sec = time.time() - t1
    status = solver.StatusName(st)
    return {
        'status': status,
        'status_code': int(st),
        'build_sec': build_sec,
        'solve_sec': solve_sec,
        'solver_walltime': float(solver.WallTime()),
        'solver_conflicts': int(solver.NumConflicts()),
        'solver_branches': int(solver.NumBranches()),
        'rows_effective': added,
        'rows_skipped_vacuous': skipped,
        'rows_empty': empty,
        'row_hist': {f'{d},{lb}': c for (d, lb), c in sorted(row_hist.items())},
        'row_var_hist': dict(sorted(row_var_hist.items())),
        'residual_cap_hist': dict(sorted(cap_hist.items())),
        'fixed_occ_hist': dict(sorted(fixed_occ_hist.items())),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--lazy-json', type=Path, required=True)
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--time-limit', type=float, default=10.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--passes', type=int, default=3)
    ap.add_argument('--initial-chunks', default='500,250,100,50,25,10,5,1')
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    t0 = time.time()
    payload_in = json.loads(args.lazy_json.read_text())
    matching = sorted(int(p) for p in payload_in['fixed_rank1_matching'])
    keys = extract_keys(payload_in)
    lut, lmeta = load_lut(args.lut)
    history = []
    base = solve_keys(lut, matching, keys, rank_s=args.rank, time_limit=args.time_limit, workers=args.workers)
    history.append({'event': 'initial', 'key_count': len(keys), **base})
    if base['status'] != 'INFEASIBLE':
        out = {
            'problem': 'deletion shrink fixed matching row core',
            'source_lazy_json': str(args.lazy_json),
            'fixed_rank1_matching': matching,
            'rank_s': args.rank,
            'initial_core_key_count': len(keys),
            'final_core_key_count': len(keys),
            'core_keys_effective': keys,
            'history': history,
            'stopped_reason': 'initial_not_infeasible',
            'elapsed_sec': time.time() - t0,
        }
        args.out.parent.mkdir(parents=True, exist_ok=True); args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
        print(json.dumps({'stopped_reason': out['stopped_reason'], 'initial_status': base['status'], 'out': str(args.out)}, indent=2))
        return
    chunks = [int(x) for x in args.initial_chunks.replace(';', ',').split(',') if x.strip()]
    current = list(keys)
    for pno in range(1, args.passes + 1):
        changed_pass = False
        for chunk in chunks:
            i = 0
            while i < len(current):
                trial = current[:i] + current[i+chunk:]
                if len(trial) == len(current):
                    i += chunk
                    continue
                res = solve_keys(lut, matching, trial, rank_s=args.rank, time_limit=args.time_limit, workers=args.workers)
                rec = {'event': 'try_remove', 'pass': pno, 'chunk': chunk, 'start': i, 'old_count': len(current), 'trial_count': len(trial), **res}
                history.append(rec)
                if res['status'] == 'INFEASIBLE':
                    current = trial
                    changed_pass = True
                    print(f'pass {pno} chunk {chunk}: removed at {i}, new count {len(current)}', flush=True)
                    # Keep same i after deletion.
                else:
                    i += chunk
        if not changed_pass:
            break
    final = solve_keys(lut, matching, current, rank_s=args.rank, time_limit=max(args.time_limit, 30.0), workers=args.workers)
    history.append({'event': 'final_check', 'key_count': len(current), **final})
    out = {
        'problem': 'deletion shrink fixed matching row core',
        'field': 'F2',
        'source_lazy_json': str(args.lazy_json),
        'rank_s': int(args.rank),
        'fixed_rank1_matching': matching,
        'target_higher_rank_count': int(args.rank) - len(matching),
        'initial_core_key_count': len(keys),
        'final_core_key_count': len(current),
        'core_keys_effective': sorted(int(k) for k in current),
        'core_keys_all': sorted(int(k) for k in current),
        'final_check': final,
        'history': history,
        'history_length': len(history),
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'elapsed_sec': time.time() - t0,
        'proof_status': 'CP-SAT-shrunk row-core target only; independent CNF/DRAT replay required.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'initial_core_key_count': len(keys),
        'final_core_key_count': len(current),
        'final_status': final['status'],
        'history_length': len(history),
        'out': str(args.out),
        'elapsed_sec': out['elapsed_sec'],
    }, indent=2, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
