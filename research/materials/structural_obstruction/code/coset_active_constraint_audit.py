#!/usr/bin/env python3
"""Independent LP/MILP audit of active CEGAR constraints for the surviving coset ansatz.

The CEGAR loop in surviving_coset_ansatz.py adds violated full-Wang rows to a
0/1 model over the remaining rank-one A directions.  This script reconstructs
those active rows from a saved cegar_result.json, builds an independent SciPy
linear/integer program, and reports whether the active system is already LP- or
MILP-infeasible.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import coo_matrix, vstack

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))

from surviving_coset_ansatz import (  # type: ignore
    analyze_H,
    canonical_coset_points,
    iter_wang_rows,
    load_lut,
    rank_one_uv_map,
)


def reconstruct_active_rows(cegar: Dict, allowed: Sequence[int], binary: Path) -> Tuple[List[Dict], Dict]:
    H = [int(x) for x in cegar['H']]
    H_mask = sum(1 << h for h in H)
    allowed = [int(x) for x in allowed]
    rows = []
    raw = 0
    for rd in cegar['rounds']:
        if 'support' not in rd:
            continue
        support_mask = sum(1 << int(x) for x in rd['support'])
        add_limit = int(cegar['parameters']['add_per_round'])
        added = 0
        for idx, cap, dim, rowmask in iter_wang_rows(binary):
            occ = (rowmask & (H_mask | support_mask)).bit_count()
            if occ > cap:
                raw += 1
                rhs = int(cap) - (rowmask & H_mask).bit_count()
                pts = [j for j, x in enumerate(allowed) if (rowmask >> x) & 1]
                rows.append({'idx': int(idx), 'cap': int(cap), 'dim': int(dim), 'rhs': int(rhs), 'vars': pts, 'support_size': len(pts), 'rowmask': int(rowmask)})
                added += 1
                if added >= add_limit:
                    break
    # Deduplicate by row index; full binary has unique row indices.
    by_idx = {}
    for r in rows:
        if r['idx'] not in by_idx:
            by_idx[r['idx']] = r
    unique = [by_idx[k] for k in sorted(by_idx)]
    meta = {
        'raw_reconstructed_rows': raw,
        'unique_reconstructed_rows': len(unique),
        'dim_hist': dict(Counter(r['dim'] for r in unique)),
        'rhs_hist': dict(Counter(r['rhs'] for r in unique)),
        'support_size_hist': dict(Counter(r['support_size'] for r in unique)),
        'negative_rhs_rows': sum(1 for r in unique if r['rhs'] < 0),
    }
    return unique, meta


def build_sparse_constraints(n: int, active_rows: Sequence[Dict], allowed: Sequence[int]) -> Tuple[LinearConstraint, Dict]:
    rows_i = []
    cols_j = []
    data = []
    lb = []
    ub = []
    row_names = []

    # Sum exactly 16.
    rr = len(lb)
    for j in range(n):
        rows_i.append(rr); cols_j.append(j); data.append(1.0)
    lb.append(16.0); ub.append(16.0); row_names.append('sum16')

    # Per-left and per-right caps <=5.
    uv = rank_one_uv_map()
    allowed = [int(x) for x in allowed]
    for side in ['left', 'right']:
        for val in range(1, 8):
            rr = len(lb)
            cnt = 0
            for j, x in enumerate(allowed):
                u, v = uv[x]
                if (u if side == 'left' else v) == val:
                    rows_i.append(rr); cols_j.append(j); data.append(1.0); cnt += 1
            if cnt:
                lb.append(-np.inf); ub.append(5.0); row_names.append(f'{side}_{val}')

    active_added = 0
    taut = 0
    impossible = 0
    for r in active_rows:
        rhs = int(r['rhs'])
        pts = list(r['vars'])
        if rhs < 0:
            # Add 0 <= -1 impossible row.
            rr = len(lb)
            lb.append(0.0); ub.append(-1.0); row_names.append(f'wang_{r["idx"]}_neg')
            impossible += 1
        elif rhs >= len(pts):
            taut += 1
            continue
        else:
            rr = len(lb)
            for j in pts:
                rows_i.append(rr); cols_j.append(j); data.append(1.0)
            lb.append(-np.inf); ub.append(float(rhs)); row_names.append(f'wang_{r["idx"]}')
            active_added += 1
    A = coo_matrix((data, (rows_i, cols_j)), shape=(len(lb), n)).tocsr()
    meta = {'rows_total': len(lb), 'active_rows_added': active_added, 'taut_active_rows': taut, 'impossible_active_rows': impossible, 'nnz': int(A.nnz)}
    return LinearConstraint(A, np.array(lb), np.array(ub)), meta


def audit_one(cegar_path: Path, lut_path: Path, binary: Path, milp_time: float) -> Dict:
    t0 = time.time()
    cegar = json.loads(cegar_path.read_text())
    lut = load_lut(lut_path)
    hrec = analyze_H(lut, cegar['H'], canonical_coset_points()[0])
    allowed = [int(x) for x in hrec['allowed_rank_one']]
    active_rows, active_meta = reconstruct_active_rows(cegar, allowed, binary)
    lc, lc_meta = build_sparse_constraints(len(allowed), active_rows, allowed)
    bounds = Bounds(np.zeros(len(allowed)), np.ones(len(allowed)))
    c = np.zeros(len(allowed))

    lp_t0 = time.time()
    lp = linprog(c, A_ub=lc.A[lc.lb == -np.inf], b_ub=lc.ub[lc.lb == -np.inf],
                 A_eq=lc.A[lc.lb == lc.ub], b_eq=lc.ub[lc.lb == lc.ub],
                 bounds=[(0, 1)] * len(allowed), method='highs')
    lp_elapsed = time.time() - lp_t0

    milp_rec = None
    if lp.status == 0:
        milp_t0 = time.time()
        res = milp(c=c, integrality=np.ones(len(allowed)), bounds=bounds, constraints=lc,
                   options={'time_limit': float(milp_time), 'mip_rel_gap': 0.0, 'presolve': True})
        milp_rec = {
            'status': int(res.status),
            'message': str(res.message),
            'success': bool(res.success),
            'fun': None if res.fun is None else float(res.fun),
            'elapsed_sec': time.time() - milp_t0,
        }
        if res.x is not None:
            x = np.rint(res.x).astype(int)
            milp_rec['solution_weight'] = int(x.sum())
            milp_rec['selected'] = [allowed[i] for i, z in enumerate(x) if z]

    return {
        'schema': 'coset_active_constraint_audit_v1',
        'cegar_path': str(cegar_path),
        'H': cegar['H'],
        'H_firstrows': cegar.get('H_firstrows'),
        'allowed_count': len(allowed),
        'cegar_final_status': cegar.get('final_status'),
        'active_reconstruction': active_meta,
        'linear_constraint_meta': lc_meta,
        'lp': {
            'status': int(lp.status),
            'message': str(lp.message),
            'success': bool(lp.success),
            'elapsed_sec': lp_elapsed,
            'fun': None if lp.fun is None else float(lp.fun),
        },
        'milp': milp_rec,
        'elapsed_sec': time.time() - t0,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cegar', type=Path, required=True)
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--binary', type=Path, default=Path('data/wang_native/full_tensor/full_wang512_cap19_len20_all_dim9_allbinding.bin'))
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--milp-time', type=float, default=120.0)
    args = ap.parse_args()
    rec = audit_one(args.cegar, args.lut, args.binary, args.milp_time)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(rec, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(args.out),
        'H': rec['H'],
        'cegar_status': rec['cegar_final_status'],
        'active_rows': rec['active_reconstruction']['unique_reconstructed_rows'],
        'lp_status': rec['lp']['status'],
        'lp_message': rec['lp']['message'],
        'milp': rec['milp'],
        'elapsed_sec': rec['elapsed_sec'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
