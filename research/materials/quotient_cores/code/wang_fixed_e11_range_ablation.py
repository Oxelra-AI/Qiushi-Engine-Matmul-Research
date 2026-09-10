#!/usr/bin/env python3
"""Ablate row families for fixed-E11 rank-1-count range CP-SAT probes.

This helps find compact proof-producing targets for k=1..17 branches.  It runs
several variants of wang_fixed_e11_range_cpsat.solve after loading the Wang LUT
once.  Results remain CP-SAT probes; UNSAT/INFEASIBLE needs CNF/DRAT replay.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_cnf_e11_fixed import collect_violation_keys, parse_dims  # noqa: E402
from wang_fixed_e11_range_cpsat import load_lut, parse_groups, parse_ints, solve  # noqa: E402


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', required=True)
    ap.add_argument('--exclude-second-orbits-before', action='store_true')
    ap.add_argument('--min-rank1-count', type=int, default=1)
    ap.add_argument('--max-rank1-count', type=int, default=17)
    ap.add_argument('--exact-rank1-count', type=int, default=None)
    ap.add_argument('--include-dims', default='1,2,3')
    ap.add_argument('--through-fixed-dims-list', default=',4,5,6,7,8,4-5,6-8,4-8', help='semicolon-separated dimension specs; empty spec allowed')
    ap.add_argument('--rank1-cache', type=Path, default=Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl'))
    ap.add_argument('--rank1-max-intersection-size', type=int, default=None)
    ap.add_argument('--rank1-include-groups', default='')
    ap.add_argument('--seed-json', type=Path, action='append', default=[])
    ap.add_argument('--seed-dims', default='4-8')
    ap.add_argument('--time-limit', type=float, default=120)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--summary', type=Path, required=True)
    args = ap.parse_args()

    seed_keys = set()
    for p in args.seed_json:
        got = collect_violation_keys(p)
        print(f'seed {p}: {len(got)} keys', flush=True)
        seed_keys.update(got)
    lut, meta = load_lut(args.lut)
    fixed_extra = parse_ints(args.fixed_extra)
    include_dims = parse_dims(args.include_dims)
    rank1_groups = parse_groups(args.rank1_include_groups)
    specs = [x.strip() for x in args.through_fixed_dims_list.split(';')]
    args.outdir.mkdir(parents=True, exist_ok=True)
    args.summary.parent.mkdir(parents=True, exist_ok=True)

    records = []
    t0 = time.time()
    for spec in specs:
        safe = spec.replace(',', '_').replace('-', 'to') if spec else 'none'
        out = args.outdir / f'through_{safe}.json'
        print(f'RUN through_fixed_dims={spec!r} -> {out}', flush=True)
        solve(
            lut, meta, lut_path=args.lut, rank_s=args.rank, fixed_extra=fixed_extra,
            exclude_second_orbits_before=args.exclude_second_orbits_before,
            min_rank1_count=args.min_rank1_count, max_rank1_count=args.max_rank1_count,
            exact_rank1_count=args.exact_rank1_count,
            include_dims=include_dims,
            through_fixed_dims=parse_dims(spec),
            seed_keys=seed_keys,
            seed_dims=parse_dims(args.seed_dims),
            rank1_cache=args.rank1_cache,
            rank1_max_intersection_size=args.rank1_max_intersection_size,
            rank1_include_groups=rank1_groups,
            time_limit=args.time_limit,
            workers=args.workers,
            out=out,
        )
        d = json.loads(out.read_text())
        records.append({
            'through_fixed_dims_spec': spec,
            'out': str(out),
            'solver_status': d.get('solver_status'),
            'support_rank1_count': d.get('support_rank1_count'),
            'support_rank_hist': d.get('support_rank_hist'),
            'support_size': d.get('support_size'),
            'wang_rows_added': d.get('wang_rows_added'),
            'rank1_projection_rows_added': d.get('rank1_projection_rows_added'),
            'solve_elapsed_sec': d.get('solve_elapsed_sec'),
            'build_elapsed_sec': d.get('build_elapsed_sec'),
        })
        summary = {
            'problem': 'row-family ablation for fixed-E11 rank-1-count range CP-SAT',
            'field': 'F2',
            'fixed_extra': fixed_extra,
            'rank_s': args.rank,
            'min_rank1_count': args.min_rank1_count,
            'max_rank1_count': args.max_rank1_count,
            'exact_rank1_count': args.exact_rank1_count,
            'include_dims': sorted(include_dims),
            'rank1_filter': {'max_intersection_size': args.rank1_max_intersection_size, 'include_groups': None if rank1_groups is None else sorted([list(g) for g in rank1_groups])},
            'seed_key_count': len(seed_keys),
            'completed_count': len(records),
            'records': records,
            'status_hist': dict(sorted(Counter(r['solver_status'] for r in records).items())),
            'elapsed_sec': time.time() - t0,
            'meaning': 'CP-SAT probe only; identifies row families suitable for later CNF/DRAT replay.',
        }
        args.summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
