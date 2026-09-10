#!/usr/bin/env python3
"""Check analysis support witnesses against the intended analysis row subset.

This does not use SAT auxiliary variables. It directly evaluates Wang occupation
inequalities for dim-1 rows plus rows of dimensions 4 and 6 containing the fixed
prefix [E11, rep].  These are the mathematical constraints analysis intended to
encode for reps 2/10/16.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import in_rowspace, unpack_basis, subspace_points_from_basis  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def check(support_path: Path, rep: int, lut_path: Path, rank_s: int = 20) -> dict:
    data = json.loads(support_path.read_text())
    support = [int(p) for p in data['support']]
    fixed = [1, int(rep)]
    support_set = set(support)
    if len(support) != rank_s:
        raise ValueError(f'support size {len(support)} != {rank_s}')
    if any(p not in support_set for p in fixed):
        raise ValueError(f'fixed prefix {fixed} not contained in support')
    lut, meta = load_lut(lut_path)
    rows_seen = 0
    violations = []
    rows_by_dim = Counter()
    rows_by_lb = Counter()
    occ_hist = Counter()
    slack_hist = Counter()
    for key, lb0 in lut.items():
        d = int(key) & 0xF
        basis = None
        include = d == 1
        if not include and d in (4, 6):
            basis = unpack_basis(key)
            include = all(in_rowspace(p, basis, n=9) for p in fixed)
        if not include:
            continue
        if basis is None:
            basis = unpack_basis(key)
        pts = subspace_points_from_basis(basis)
        occ = sum(1 for p in support if p in pts)
        cap = rank_s - int(lb0)
        rows_seen += 1
        rows_by_dim[d] += 1
        rows_by_lb[int(lb0)] += 1
        occ_hist[occ] += 1
        slack_hist[cap - occ] += 1
        if occ > cap:
            violations.append({'key': int(key), 'dim': d, 'lb': int(lb0), 'cap': cap, 'occ': occ, 'excess': occ - cap, 'basis': list(basis)})
    return {
        'support_path': str(support_path),
        'rep': int(rep),
        'fixed': fixed,
        'support': support,
        'rank_s': rank_s,
        'row_subset': 'dim1 plus through-fixed dim4,6',
        'rows_seen': rows_seen,
        'rows_by_dim': dict(sorted(rows_by_dim.items())),
        'rows_by_lb': dict(sorted(rows_by_lb.items())),
        'violation_count': len(violations),
        'max_excess': max([v['excess'] for v in violations], default=0),
        'violation_head': violations[:20],
        'occ_hist': dict(sorted(occ_hist.items())),
        'slack_hist': dict(sorted(slack_hist.items())),
        'lut_meta_brief': {'coverage_ok': meta.get('coverage_ok'), 'conflict_count': meta.get('conflict_count'), 'subspace_count': meta.get('subspace_count')},
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--case', action='append', nargs=3, metavar=('REP', 'SUPPORT_JSON', 'OUT_JSON'))
    args = ap.parse_args()
    if not args.case:
        raise SystemExit('provide at least one --case REP SUPPORT_JSON OUT_JSON')
    for rep_s, src_s, out_s in args.case:
        res = check(Path(src_s), int(rep_s), args.lut)
        out = Path(out_s)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(res, indent=2, sort_keys=True) + '\n')
        print(json.dumps({k: res[k] for k in ['rep', 'rows_seen', 'rows_by_dim', 'violation_count', 'max_excess', 'support_path']}, indent=2, sort_keys=True))
        print(f'saved {out}')


if __name__ == '__main__':
    main()
