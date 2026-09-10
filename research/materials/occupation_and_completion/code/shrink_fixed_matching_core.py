#!/usr/bin/env python3
"""Shrink a fixed-matching lazy row core using CP-SAT assumptions.

This is a proof-engineering aid, not a certificate.  It reads a fixed matching
stratum record containing core_keys_effective/core_keys_all, builds the same
higher-rank completion problem, guards each Wang row by an assumption literal,
and asks CP-SAT for a sufficient infeasible subset.  The output is a smaller
row-core JSON consumable by fixed_matching_rowcore_cnf.py.
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

from wang_capacity_cnf_e11_fixed import E11  # noqa: E402
from wang_capacity_lazy import matrix_rank_of_mask, subspace_points_from_basis, unpack_basis  # noqa: E402
from fixed_matching_rowcore_cnf import matching_ok, rank1_points  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def extract_keys(payload: dict, use_all: bool) -> list[int]:
    if use_all and payload.get('core_keys_all'):
        keys = payload['core_keys_all']
    elif payload.get('core_keys_effective'):
        keys = payload['core_keys_effective']
    elif payload.get('core_keys_all'):
        keys = payload['core_keys_all']
    else:
        keys = [r['key'] for r in payload.get('cut_records', []) if r.get('mode') != 'vacuous']
    out = sorted({int(k) for k in keys})
    if not out:
        raise ValueError('no core keys available')
    return out


def build_and_solve(lut: dict[int, int], matching: Sequence[int], core_keys: Sequence[int], *, rank_s: int,
                    time_limit: float, workers: int, log_progress: bool) -> dict:
    from ortools.sat.python import cp_model
    t0 = time.time()
    matching = sorted(int(p) for p in matching)
    if E11 not in matching or not matching_ok(matching):
        raise ValueError(f'bad fixed matching {matching}')
    r1 = rank1_points()
    hr_pts = [p for p in range(1, 512) if p not in r1]
    target_hr = int(rank_s) - len(matching)
    model = cp_model.CpModel()
    y = {p: model.NewBoolVar(f'y_{p}') for p in hr_pts}
    model.Add(sum(y.values()) == target_hr)
    assumps = []
    lit_to_key: dict[int, int] = {}
    row_hist = Counter(); row_var_hist = Counter(); cap_hist = Counter(); fixed_occ_hist = Counter(); skipped = 0; empty = 0
    preview = []
    for idx, key0 in enumerate(core_keys):
        key = int(key0)
        if key not in lut:
            raise ValueError(f'key not in LUT: {key}')
        lb = int(lut[key])
        basis = unpack_basis(key)
        pts = subspace_points_from_basis(basis)
        fixed_occ = sum(1 for p in matching if p in pts)
        cap = rank_s - lb - fixed_occ
        lits = [y[p] for p in pts if p in y]
        row_hist[(key & 0xF, lb)] += 1; row_var_hist[len(lits)] += 1; cap_hist[cap] += 1; fixed_occ_hist[fixed_occ] += 1
        if len(lits) <= cap and cap >= 0:
            skipped += 1
            continue
        a = model.NewBoolVar(f'a_{idx}_{key}')
        assumps.append(a)
        lit_to_key[a.Index()] = key
        lit_to_key[-a.Index()] = key
        if cap < 0:
            model.AddBoolOr([]).OnlyEnforceIf(a)
            empty += 1
        else:
            model.Add(sum(lits) <= cap).OnlyEnforceIf(a)
        if len(preview) < 80:
            preview.append({'key': key, 'dim': key & 0xF, 'lb': lb, 'fixed_rank1_occ': fixed_occ, 'residual_cap': cap, 'hr_var_count': len(lits), 'basis': list(basis)})
    model.AddAssumptions(assumps)
    build_sec = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = 282828
    solver.parameters.log_search_progress = bool(log_progress)
    t1 = time.time(); st = solver.Solve(model); solve_sec = time.time() - t1
    status = solver.StatusName(st)
    raw_core = []
    core_keys_out = []
    if status == 'INFEASIBLE':
        raw_core = list(solver.SufficientAssumptionsForInfeasibility())
        core_keys_out = sorted({int(lit_to_key[int(l)]) for l in raw_core if int(l) in lit_to_key})
    return {
        'solver_status': status,
        'solver_status_code': int(st),
        'solver_walltime': float(solver.WallTime()),
        'solver_num_conflicts': int(solver.NumConflicts()),
        'solver_num_branches': int(solver.NumBranches()),
        'build_sec': build_sec,
        'solve_sec': solve_sec,
        'input_core_key_count': len(core_keys),
        'assumption_count': len(assumps),
        'skipped_vacuous_rows': skipped,
        'empty_guarded_rows': empty,
        'sufficient_assumption_literal_count': len(raw_core),
        'core_keys_effective': core_keys_out,
        'row_hist': {f'{d},{lb}': c for (d, lb), c in sorted(row_hist.items())},
        'row_var_hist': dict(sorted(row_var_hist.items())),
        'residual_cap_hist': dict(sorted(cap_hist.items())),
        'fixed_rank1_occ_hist': dict(sorted(fixed_occ_hist.items())),
        'preview': preview,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--lazy-json', type=Path, required=True)
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--use-all-keys', action='store_true')
    ap.add_argument('--time-limit', type=float, default=120.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--log-progress', action='store_true')
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    t0 = time.time()
    payload_in = json.loads(args.lazy_json.read_text())
    matching = [int(p) for p in payload_in['fixed_rank1_matching']]
    keys = extract_keys(payload_in, use_all=args.use_all_keys)
    lut, lmeta = load_lut(args.lut)
    res = build_and_solve(lut, matching, keys, rank_s=args.rank, time_limit=args.time_limit, workers=args.workers, log_progress=args.log_progress)
    out = {
        'problem': 'CP-SAT assumption shrink of fixed matching stratum row core',
        'field': 'F2',
        'source_lazy_json': str(args.lazy_json),
        'rank_s': int(args.rank),
        'fixed_rank1_matching': matching,
        'target_higher_rank_count': int(args.rank) - len(matching),
        'source_lazy_final_status': payload_in.get('final_status'),
        'source_lazy_iteration_count': payload_in.get('iteration_count'),
        **res,
        'core_keys_all': sorted({int(k) for k in keys}),
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'elapsed_sec': time.time() - t0,
        'proof_status': 'Not a proof. Use this output only as a smaller row-core input for independent CNF/DRAT replay.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'solver_status': out['solver_status'],
        'input_core_key_count': out['input_core_key_count'],
        'assumption_count': out['assumption_count'],
        'sufficient_assumption_literal_count': out['sufficient_assumption_literal_count'],
        'shrunk_core_key_count': len(out['core_keys_effective']),
        'out': str(args.out),
        'elapsed_sec': out['elapsed_sec'],
    }, indent=2, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
