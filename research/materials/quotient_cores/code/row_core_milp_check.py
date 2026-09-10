#!/usr/bin/env python3
"""LP/MILP check for a saved Wang row core.

This tests whether a row-core infeasibility is already visible to linear
programming, or only to 0/1 integrality.  It uses SciPy/HiGHS as an execution
instrument, not as a proof certificate.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import lil_matrix, vstack

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import matrix_rank_of_mask, subspace_points_from_basis, unpack_basis  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def parse_ints(spec: str):
    return [int(x) for x in spec.replace(';', ',').split(',') if x.strip()]


def row_summary(keys, lut):
    return {
        'row_count': len(keys),
        'by_dim': dict(sorted(Counter(int(k)&15 for k in keys).items())),
        'by_lb': dict(sorted(Counter(int(lut[int(k)]) for k in keys).items())),
    }


def build_matrices(keys, lut, fixed, rank):
    n = 511
    A = lil_matrix((len(keys), n), dtype=float)
    ub = np.empty(len(keys), dtype=float)
    for i, k in enumerate(keys):
        pts = subspace_points_from_basis(unpack_basis(int(k)))
        for p in pts:
            A[i, p-1] = 1.0
        ub[i] = rank - int(lut[int(k)])
    A = A.tocsr()
    Aeq = lil_matrix((1 + len(fixed), n), dtype=float)
    beq = np.empty(1 + len(fixed), dtype=float)
    Aeq[0, :] = 1.0
    beq[0] = rank
    for j, p in enumerate(fixed, start=1):
        Aeq[j, p-1] = 1.0
        beq[j] = 1.0
    return A, ub, Aeq.tocsr(), beq


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--core', type=Path, required=True)
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--fixed', default='1,10')
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--lp', action='store_true')
    ap.add_argument('--milp', action='store_true')
    ap.add_argument('--time-limit', type=float, default=300.0)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    t0 = time.time()
    lut, lmeta = load_lut(args.lut)
    data = json.loads(args.core.read_text())
    keys = [int(k) for k in data['core_keys']]
    fixed = parse_ints(args.fixed)
    A, ub, Aeq, beq = build_matrices(keys, lut, fixed, args.rank)
    bounds_obj = Bounds(np.zeros(511), np.ones(511))
    linprog_bounds = [(0.0, 1.0)] * 511
    c = np.zeros(511)
    payload = {
        'problem': 'LP/MILP feasibility check for Wang row core',
        'field': 'F2 support polytope/integer support model',
        'rank_s': args.rank,
        'fixed_points': fixed,
        'core_path': str(args.core),
        'row_summary': row_summary(keys, lut),
        'matrix_shape': [int(A.shape[0]), int(A.shape[1])],
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
    }
    if args.lp:
        t = time.time()
        lp = linprog(c, A_ub=A, b_ub=ub, A_eq=Aeq, b_eq=beq, bounds=linprog_bounds, method='highs', options={'time_limit': args.time_limit})
        payload['lp'] = {'status': int(lp.status), 'success': bool(lp.success), 'message': str(lp.message), 'fun': None if lp.fun is None else float(lp.fun), 'elapsed_sec': time.time()-t}
        if lp.x is not None:
            payload['lp']['support_fraction_hist'] = {
                'near0': int(np.sum(lp.x < 1e-8)),
                'near1': int(np.sum(lp.x > 1-1e-8)),
                'fractional': int(np.sum((lp.x >= 1e-8) & (lp.x <= 1-1e-8))),
                'sum': float(np.sum(lp.x)),
                'fixed_values': {str(p): float(lp.x[p-1]) for p in fixed},
            }
    if args.milp:
        t = time.time()
        constraints = [LinearConstraint(A, -np.inf*np.ones(len(keys)), ub), LinearConstraint(Aeq, beq, beq)]
        mi = milp(c=c, integrality=np.ones(511), bounds=bounds_obj, constraints=constraints, options={'time_limit': args.time_limit, 'mip_rel_gap': 0.0})
        payload['milp'] = {'status': int(mi.status), 'success': bool(mi.success), 'message': str(mi.message), 'fun': None if mi.fun is None else float(mi.fun), 'elapsed_sec': time.time()-t}
        if mi.x is not None:
            supp = [i+1 for i,v in enumerate(mi.x) if v > 0.5]
            payload['milp']['support'] = supp
            payload['milp']['support_rank_hist'] = dict(sorted(Counter(matrix_rank_of_mask(p) for p in supp).items()))
            payload['milp']['support_rank1_count'] = sum(1 for p in supp if matrix_rank_of_mask(p)==1)
    payload['total_elapsed_sec'] = time.time()-t0
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps(payload, indent=2, sort_keys=True)[:4000])
    print('saved', args.out)


if __name__ == '__main__':
    main()
