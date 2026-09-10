#!/usr/bin/env python3
"""Filtered proof-producing CNF for fixed-high exact rank-1 skeletons.

This wraps rank1_fixed_high_cnf.py but keeps only selected compressed row groups,
usually found by rank1_fixed_high_ablation.py.  It is used to turn fast CP-SAT
infeasibility for fixed high prefixes into smaller CaDiCaL/DRAT proof objects.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Set, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_fixed_high_cnf import (  # noqa: E402
    compress_for_fixed_high,
    load_lut,
    parse_ints,
    rank1_points,
    run_solver,
    write_cnf,
)
from wang_capacity_lazy import matrix_rank_of_mask  # noqa: E402


def parse_groups(spec: str) -> Set[Tuple[int, int]] | None:
    spec = spec.strip()
    if not spec:
        return None
    out: Set[Tuple[int, int]] = set()
    for part in spec.replace(';', ',').split(','):
        part = part.strip()
        if not part:
            continue
        if ':' in part:
            a, b = part.split(':', 1)
        elif '/' in part:
            a, b = part.split('/', 1)
        else:
            raise ValueError(f'bad group {part!r}')
        out.add((int(a), int(b)))
    return out


def filter_cons(cons, max_intersection_size: int | None, groups: Set[Tuple[int, int]] | None, min_gap: int | None):
    out = []
    for mask, cap, wit in cons:
        size = int(mask).bit_count(); cap = int(cap)
        if size <= cap:
            continue
        if groups is not None and (size, cap) not in groups:
            continue
        if groups is None and max_intersection_size is not None and size > max_intersection_size:
            continue
        if min_gap is not None and size - cap < min_gap:
            continue
        out.append((int(mask), cap, wit))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank-s', type=int, default=20)
    ap.add_argument('--exact-rank1-count', type=int, default=18)
    ap.add_argument('--fixed-rank1', default='1')
    ap.add_argument('--fixed-high', required=True)
    ap.add_argument('--max-intersection-size', type=int, default=None)
    ap.add_argument('--include-groups', default='')
    ap.add_argument('--min-gap', type=int, default=None)
    ap.add_argument('--cnf', type=Path, required=True)
    ap.add_argument('--meta', type=Path, required=True)
    ap.add_argument('--direct-comb-limit', type=int, default=2000)
    ap.add_argument('--solve', action='store_true')
    ap.add_argument('--solver-time', type=int, default=0)
    args = ap.parse_args()
    fixed_rank1 = parse_ints(args.fixed_rank1); fixed_high = parse_ints(args.fixed_high)
    for p in fixed_rank1:
        if matrix_rank_of_mask(p) != 1:
            raise SystemExit(f'fixed-rank1 point {p} does not have rank 1')
    for p in fixed_high:
        if matrix_rank_of_mask(p) <= 1:
            raise SystemExit(f'fixed-high point {p} does not have rank 2/3')
    lut, lmeta = load_lut(args.lut)
    r1_pts = rank1_points()
    print(f'loaded LUT {len(lut):,} coverage={lmeta.get("coverage_ok")} conflicts={lmeta.get("conflict_count")} fixed_high={fixed_high}')
    cons, cmeta = compress_for_fixed_high(lut, args.rank_s, fixed_high, r1_pts)
    groups = parse_groups(args.include_groups)
    fcons = filter_cons(cons, args.max_intersection_size, groups, args.min_gap)
    cmeta = dict(cmeta)
    cmeta['filter'] = {'max_intersection_size': args.max_intersection_size, 'include_groups': None if groups is None else sorted([list(g) for g in groups]), 'min_gap': args.min_gap, 'filtered_nonvacuous_constraints': len(fcons)}
    write_cnf(r1_pts, fcons, args.exact_rank1_count, fixed_rank1, args.cnf, args.meta, args.rank_s, fixed_high, cmeta, lmeta, args.direct_comb_limit)
    if args.solve:
        run_solver(args.cnf, args.solver_time)


if __name__ == '__main__':
    main()
