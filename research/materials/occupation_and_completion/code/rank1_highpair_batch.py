#!/usr/bin/env python3
"""Batch CP-SAT over Stab(E11)-orbits of two higher-rank points.

analysis proved that length-20 Wang-admissible supports have at most 18 rank-1
A-points.  In the exact-18 case, after fixing E11 the remaining two A-points
are higher-rank.  This script enumerates unordered high-point pair orbits under
Stab(E11), optionally filters them by the Stab(E11) single orbit of each high
point, and for each representative solves the full projected rank-1 skeleton
problem with those two high points fixed.

A SAT/OPTIMAL result is already a full Wang-admissible A-support candidate
(18 rank-1 points plus the two fixed high points) and should be sent to fixed-A
B/C solving.  INFEASIBLE is computational evidence; use rank1_fixed_high_cnf.py
to produce DRAT proof objects for theorem components.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence, Set, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_fixed_high_cpsat import load_lut, solve_one  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11, stab_e11_orbits  # noqa: E402
from wang_capacity_lazy import make_actions, matrix_rank_of_mask, transform_mask  # noqa: E402


def parse_intset(spec: str) -> Set[int] | None:
    spec = spec.strip()
    if not spec:
        return None
    return {int(x) for x in spec.replace(';', ',').split(',') if x.strip()}


def single_orbit_map() -> Dict[int, int]:
    mp: Dict[int, int] = {}
    for orb in stab_e11_orbits():
        for p in orb['members']:
            mp[int(p)] = int(orb['rep'])
    return mp


def high_pair_orbits(allowed_single_reps: Set[int] | None = None):
    actions = [img for img in make_actions() if transform_mask(E11, img) == E11]
    single = single_orbit_map()
    high = [p for p in range(1, 512) if matrix_rank_of_mask(p) > 1]
    if allowed_single_reps is not None:
        high = [p for p in high if single[p] in allowed_single_reps]
    unseen = set()
    for i, p in enumerate(high):
        for q in high[i + 1:]:
            unseen.add((p, q) if p < q else (q, p))
    out = []
    while unseen:
        pair = min(unseen)
        imgs = {tuple(sorted((transform_mask(pair[0], img), transform_mask(pair[1], img)))) for img in actions}
        imgs = {x for x in imgs if x[0] != x[1] and x[0] in single and x[1] in single and matrix_rank_of_mask(x[0]) > 1 and matrix_rank_of_mask(x[1]) > 1 and (allowed_single_reps is None or (single[x[0]] in allowed_single_reps and single[x[1]] in allowed_single_reps))}
        sorb = Counter(tuple(sorted((single[a], single[b]))) for a, b in imgs)
        rh = Counter(tuple(sorted((matrix_rank_of_mask(a), matrix_rank_of_mask(b)))) for a, b in imgs)
        out.append({'pair': list(pair), 'orbit_size': len(imgs), 'single_orbit_pair_hist': {str(k): v for k, v in sorted(sorb.items())}, 'rank_pair_hist': {str(k): v for k, v in sorted(rh.items())}})
        unseen -= imgs
    out.sort(key=lambda e: tuple(e['pair']))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--allowed-single-reps', default='17,20,160', help='comma-separated Stab(E11) single high orbits to keep; empty keeps all high points')
    ap.add_argument('--fixed-rank1', default='1')
    ap.add_argument('--exact-rank1-count', type=int, default=18)
    ap.add_argument('--rank-s', type=int, default=20)
    ap.add_argument('--time-limit', type=float, default=60)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--max-pairs', type=int, default=0)
    ap.add_argument('--start-index', type=int, default=0)
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--summary', type=Path, required=True)
    args = ap.parse_args()
    fixed_rank1 = [int(x) for x in args.fixed_rank1.replace(';', ',').split(',') if x.strip()]
    allowed = parse_intset(args.allowed_single_reps)
    orbits = high_pair_orbits(allowed)
    selected = orbits[args.start_index:]
    if args.max_pairs:
        selected = selected[:args.max_pairs]
    args.outdir.mkdir(parents=True, exist_ok=True); args.summary.parent.mkdir(parents=True, exist_ok=True)
    lut, meta = load_lut(args.lut)
    print(f'loaded LUT {len(lut):,}; pair_orbits_total={len(orbits)} selected={len(selected)} allowed_single_reps={sorted(allowed) if allowed else None}', flush=True)
    records = []
    t0 = time.time()
    for local_i, orb in enumerate(selected, 1):
        pair = orb['pair']; global_i = args.start_index + local_i - 1
        print(f'PAIR {local_i}/{len(selected)} global={global_i} pair={pair} orbit_size={orb["orbit_size"]}', flush=True)
        r = solve_one(lut, meta, fixed_rank1, pair, args.exact_rank1_count, args.rank_s, args.time_limit, args.workers)
        r['pair_orbit'] = orb; r['pair_orbit_global_index'] = global_i
        f = args.outdir / f'pair_{global_i:03d}_{pair[0]}_{pair[1]}.json'
        f.write_text(json.dumps(r, indent=2, sort_keys=True) + '\n')
        records.append({'path': str(f), 'pair_orbit_global_index': global_i, 'pair': pair, 'orbit_size': orb['orbit_size'], 'solver_status': r['solver_status'], 'support_all_size_with_fixed_high': r.get('support_all_size_with_fixed_high'), 'support_all_fixed_prefix': r.get('support_all_fixed_prefix'), 'build_elapsed_sec': r.get('build_elapsed_sec'), 'solve_elapsed_sec': r.get('solve_elapsed_sec')})
        # Update summary after every pair for safe interruption.
        summary = {'problem':'exact-18 rank1 plus high-pair orbit CP-SAT batch','field':'F2','rank_s':args.rank_s,'exact_rank1_count':args.exact_rank1_count,'fixed_rank1':fixed_rank1,'allowed_single_reps':None if allowed is None else sorted(allowed),'pair_orbit_total_count':len(orbits),'start_index':args.start_index,'selected_count':len(selected),'completed_count':len(records),'status_hist':dict(sorted(Counter(e['solver_status'] for e in records).items())),'sat_candidate_count':sum(1 for e in records if e['solver_status'] in ('OPTIMAL','FEASIBLE')),'records':records,'elapsed_sec':time.time()-t0,'meaning':'SAT entries are full Wang-admissible A-support candidates if the encoding semantics are trusted; INFEASIBLE needs DRAT replay before theorem use.'}
        args.summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(json.dumps(summary, indent=2, sort_keys=True))
    print('saved', args.summary)


if __name__ == '__main__':
    main()
