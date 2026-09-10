#!/usr/bin/env python3
"""Direct CP-SAT scan of rep10 exact-k original branch row family.

This keeps all original branch variables for fixed (E11, rep10), excludes only
earlier second-orbit points, and uses a sound Wang row family.  It is meant to
compare the singleton/pair hierarchy with the un-reduced exact-k branch formula.
No result here is proof-level without CNF/DRAT or another independent certificate.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_cnf_e11_fixed import parse_dims  # noqa: E402
from wang_fixed_e11_range_cpsat import load_lut, parse_groups, solve  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--out-dir', type=Path, required=True)
    ap.add_argument('--summary', type=Path, required=True)
    ap.add_argument('--k-list', default='1-17')
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', default='10')
    ap.add_argument('--include-dims', default='1')
    ap.add_argument('--through-fixed-dims', default='4,6')
    ap.add_argument('--time-limit', type=float, default=300)
    ap.add_argument('--workers', type=int, default=8)
    args = ap.parse_args()

    def parse_ks(spec: str):
        out = []
        for part in spec.replace(';', ',').split(','):
            part = part.strip()
            if not part:
                continue
            if '-' in part:
                a, b = part.split('-', 1)
                out.extend(range(int(a), int(b) + 1))
            else:
                out.append(int(part))
        return sorted(set(out))

    args.out_dir.mkdir(parents=True, exist_ok=True)
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    lut, meta = load_lut(args.lut)
    records = []
    t_all = time.time()
    for k in parse_ks(args.k_list):
        out = args.out_dir / f'rep10_exact_k{k:02d}_dim1_through46_no_rank1proj.json'
        print(f'=== exact k={k} -> {out} ===', flush=True)
        t0 = time.time()
        solve(
            lut, meta, lut_path=args.lut, rank_s=args.rank, fixed_extra=[10],
            exclude_second_orbits_before=True, min_rank1_count=None,
            max_rank1_count=None, exact_rank1_count=k,
            include_dims=parse_dims(args.include_dims),
            through_fixed_dims=parse_dims(args.through_fixed_dims),
            seed_keys=set(), seed_dims=parse_dims('4-8'),
            rank1_cache=Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl'),
            rank1_max_intersection_size=None,
            rank1_include_groups=parse_groups('0:0'),
            time_limit=args.time_limit, workers=args.workers, out=out,
        )
        d = json.loads(out.read_text())
        rec = {
            'k': k,
            'out': str(out),
            'solver_status': d.get('solver_status'),
            'build_elapsed_sec': d.get('build_elapsed_sec'),
            'solve_elapsed_sec': d.get('solve_elapsed_sec'),
            'solver_conflicts': d.get('solver_num_conflicts'),
            'solver_branches': d.get('solver_num_branches'),
            'support_size': d.get('support_size'),
            'support_rank1_count': d.get('support_rank1_count'),
            'support_rank_hist': d.get('support_rank_hist'),
            'elapsed_loop_sec': time.time() - t0,
        }
        records.append(rec)
        summary = {
            'problem': 'rep10 direct exact-k CP-SAT scan with original branch variables',
            'field': 'F2',
            'rank_s': args.rank,
            'fixed_points': [1, 10],
            'k_list': parse_ks(args.k_list),
            'include_dims': sorted(parse_dims(args.include_dims)),
            'through_fixed_dims': sorted(parse_dims(args.through_fixed_dims)),
            'rank1_projection': 'disabled by empty include group 0:0',
            'records': records,
            'status_hist': {s: sum(1 for r in records if r['solver_status'] == s) for s in sorted(set(r['solver_status'] for r in records))},
            'elapsed_sec': time.time() - t_all,
            'meaning': 'CP-SAT evidence only.  INFEASIBLE exact-k files are direct original-branch proof targets; SAT/FEASIBLE supports still require full LUT and bilinear-coupling analysis.',
        }
        args.summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'summary': str(args.summary), 'records': records, 'elapsed_sec': time.time() - t_all}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
