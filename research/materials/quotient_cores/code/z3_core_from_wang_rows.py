#!/usr/bin/env python3
"""Z3 unsat-core extraction for a saved Wang row set.

This is a complementary row-level shrinking instrument for the fixed-E11/rep10
support problem.  It takes a JSON file with `core_keys`, asserts the support-size
and fixed-point constraints, tracks every selected Wang row, and asks Z3 for an
unsat core.  Z3's core is not a final proof object; selected rows still need a
CNF/DRAT replay, but a small core can make that replay much cheaper.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path

import z3

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import in_rowspace, matrix_rank_of_mask, subspace_points_from_basis, unpack_basis  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def parse_ints(spec: str):
    return [int(x) for x in spec.replace(';', ',').split(',') if x.strip()]


def row_summary(keys, lut):
    rows = []
    for k in keys:
        basis = unpack_basis(int(k)); lb = int(lut[int(k)]); pts = subspace_points_from_basis(basis)
        rows.append({'key': int(k), 'dim': int(k)&15, 'lb': lb, 'cap': 20-lb, 'point_count': len(pts), 'basis': list(basis)})
    return {
        'row_count': len(rows),
        'by_dim': dict(sorted(Counter(r['dim'] for r in rows).items())),
        'by_lb': dict(sorted(Counter(r['lb'] for r in rows).items())),
        'by_cap': dict(sorted(Counter(r['cap'] for r in rows).items())),
        'by_point_count': dict(sorted(Counter(r['point_count'] for r in rows).items())),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--in-core', type=Path, required=True)
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed', default='1,10')
    ap.add_argument('--timeout-ms', type=int, default=600000)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    t0 = time.time()
    lut, lmeta = load_lut(args.lut)
    seed = json.loads(args.in_core.read_text())
    keys = [int(k) for k in seed['core_keys']]
    fixed = parse_ints(args.fixed)

    x = {p: z3.Bool(f'x{p}') for p in range(1, 512)}
    s = z3.Solver()
    s.set('timeout', args.timeout_ms)
    labels = {}
    l_total = z3.Bool('track_total_support')
    s.assert_and_track(z3.PbEq([(x[p], 1) for p in range(1, 512)], args.rank), l_total)
    labels[str(l_total)] = {'kind': 'total', 'rank': args.rank}
    for p in fixed:
        lab = z3.Bool(f'track_fixed_{p}')
        s.assert_and_track(x[p], lab)
        labels[str(lab)] = {'kind': 'fixed', 'point': p}
    for i, k in enumerate(keys):
        lb = int(lut[int(k)]); cap = args.rank - lb; pts = subspace_points_from_basis(unpack_basis(int(k)))
        lab = z3.Bool(f'row_{i}')
        s.assert_and_track(z3.PbLe([(x[p], 1) for p in pts], cap), lab)
        labels[str(lab)] = {'kind': 'wang_row', 'key': int(k), 'dim': int(k)&15, 'lb': lb, 'cap': cap, 'point_count': len(pts), 'basis': list(unpack_basis(int(k)))}
    build_elapsed = time.time() - t0
    ts = time.time(); res = s.check(); solve_elapsed = time.time() - ts
    core_labels = []
    core_rows = []
    core_fixed = []
    total_in_core = False
    if res == z3.unsat:
        core_labels = [str(c) for c in s.unsat_core()]
        for cl in core_labels:
            rec = labels.get(cl)
            if not rec: continue
            if rec['kind'] == 'wang_row': core_rows.append(rec)
            elif rec['kind'] == 'fixed': core_fixed.append(rec['point'])
            elif rec['kind'] == 'total': total_in_core = True
    model_support = None
    if res == z3.sat:
        m = s.model(); model_support = [p for p in range(1,512) if z3.is_true(m[x[p]])]
    payload = {
        'problem': 'Z3 core for saved Wang row set',
        'input_core': str(args.in_core),
        'field': 'F2',
        'rank_s': args.rank,
        'fixed_points': fixed,
        'input_row_summary': row_summary(keys, lut),
        'status': str(res),
        'build_elapsed_sec': build_elapsed,
        'solve_elapsed_sec': solve_elapsed,
        'timeout_ms': args.timeout_ms,
        'core_label_count': len(core_labels),
        'total_constraint_in_core': total_in_core,
        'fixed_points_in_core': sorted(core_fixed),
        'core_row_count': len(core_rows),
        'core_summary': row_summary([r['key'] for r in core_rows], lut) if core_rows else None,
        'core_keys': [int(r['key']) for r in core_rows],
        'core_rows_preview': core_rows[:80],
        'model_support': model_support,
        'model_rank_hist': None if model_support is None else dict(sorted(Counter(matrix_rank_of_mask(p) for p in model_support).items())),
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'total_elapsed_sec': time.time() - t0,
        'meaning': 'Z3 UNSAT core is a row-core candidate, not an independently checkable proof. Replay selected rows in CNF/DRAT before theorem use.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'status': payload['status'],
        'input_rows': len(keys),
        'core_label_count': len(core_labels),
        'core_row_count': len(core_rows),
        'core_summary': payload['core_summary'],
        'total_in_core': total_in_core,
        'fixed_in_core': sorted(core_fixed),
        'build_elapsed_sec': build_elapsed,
        'solve_elapsed_sec': solve_elapsed,
        'out': str(args.out),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
