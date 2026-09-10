#!/usr/bin/env python3
"""Batch-create filtered CNF/DRAT leaves for exact-18 high-pair orbits.

For each Stab(E11) pair representative among the exact-18 remaining higher-rank
pairs, compress the full Wang LUT once, then try increasing rank-1-intersection
filters (for example 7,9,11,13,17,33,49).  A leaf is recorded as closed only when
CaDiCaL returns UNSAT and drat-trim verifies the DRAT trace.  SAT at a smaller
filter simply means that row family is too weak; the batch then tries the next
filter.
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

from rank1_fixed_high_cnf import compress_for_fixed_high, load_lut, rank1_points, run_solver, write_cnf  # noqa: E402
from rank1_fixed_high_filtered_cnf import filter_cons  # noqa: E402
from rank1_highpair_batch import high_pair_orbits, parse_intset  # noqa: E402


def parse_sizes(spec: str) -> list[int]:
    return [int(x) for x in spec.replace(';', ',').split(',') if x.strip()]


def is_verified_unsat_status(path: Path) -> bool:
    if not path.exists():
        return False
    try:
        data = json.loads(path.read_text())
    except Exception:
        return False
    return bool(data.get('cadical_log_parse', {}).get('unsat')) and bool(data.get('drat_trim_log_parse', {}).get('verified'))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--allowed-single-reps', default='17,20,160')
    ap.add_argument('--start-index', type=int, default=0)
    ap.add_argument('--max-pairs', type=int, default=0)
    ap.add_argument('--max-sizes', default='7,9,11,13,17,33,49')
    ap.add_argument('--rank-s', type=int, default=20)
    ap.add_argument('--exact-rank1-count', type=int, default=18)
    ap.add_argument('--fixed-rank1', default='1')
    ap.add_argument('--direct-comb-limit', type=int, default=2000)
    ap.add_argument('--solver-time', type=int, default=600)
    ap.add_argument('--out-root', type=Path, required=True)
    ap.add_argument('--summary', type=Path, required=True)
    args = ap.parse_args()

    allowed = parse_intset(args.allowed_single_reps)
    pairs = high_pair_orbits(allowed)
    selected = pairs[args.start_index:]
    if args.max_pairs:
        selected = selected[:args.max_pairs]
    sizes = parse_sizes(args.max_sizes)
    fixed_rank1 = [int(x) for x in args.fixed_rank1.replace(';', ',').split(',') if x.strip()]
    args.out_root.mkdir(parents=True, exist_ok=True)
    args.summary.parent.mkdir(parents=True, exist_ok=True)

    lut, lmeta = load_lut(args.lut)
    r1_pts = rank1_points()
    records = []
    t0 = time.time()
    for local_i, pair_orb in enumerate(selected, 1):
        idx = args.start_index + local_i - 1
        pair = [int(x) for x in pair_orb['pair']]
        print(f'PAIR {local_i}/{len(selected)} global={idx} pair={pair}', flush=True)
        cons, cmeta = compress_for_fixed_high(lut, args.rank_s, pair, r1_pts)
        pair_record = {
            'pair_orbit_global_index': idx,
            'pair': pair,
            'pair_orbit': pair_orb,
            'compression_nonvacuous_constraints': cmeta.get('nonvacuous_constraints'),
            'compression_constraint_size_cap_hist': cmeta.get('constraint_size_cap_hist'),
            'attempts': [],
            'closed_by_verified_unsat': False,
            'closed_filter': None,
        }
        for max_size in sizes:
            leaf = args.out_root / f'pair_{idx:03d}_{pair[0]}_{pair[1]}_exact18_max{max_size}'
            stem = f'e11_highpair_{pair[0]}_{pair[1]}_exact18_max{max_size}'
            cnf = leaf / f'{stem}.cnf'
            meta = leaf / f'{stem}.meta.json'
            status = leaf / f'{stem}.status.json'
            if is_verified_unsat_status(status):
                st_data = json.loads(status.read_text())
                pair_record['attempts'].append({'max_intersection_size': max_size, 'status_path': str(status), 'already_verified': True, 'cadical_exit': st_data.get('cadical_exit'), 'verified': True, 'hashes': st_data.get('hashes', {})})
                pair_record['closed_by_verified_unsat'] = True
                pair_record['closed_filter'] = max_size
                break
            fcons = filter_cons(cons, max_size, None, None)
            print(f'  max{max_size}: selected={len(fcons)} -> {leaf}', flush=True)
            write_cnf(r1_pts, fcons, args.exact_rank1_count, fixed_rank1, cnf, meta, args.rank_s, pair, {**cmeta, 'filter': {'max_intersection_size': max_size}}, lmeta, args.direct_comb_limit)
            st = run_solver(cnf, args.solver_time)
            attempt = {
                'max_intersection_size': max_size,
                'selected_constraint_count': len(fcons),
                'status_path': str(status),
                'cadical_exit': st.get('cadical_exit'),
                'cadical_elapsed_sec': st.get('cadical_elapsed_sec'),
                'drat_trim_exit': st.get('drat_trim_exit'),
                'drat_trim_elapsed_sec': st.get('drat_trim_elapsed_sec'),
                'unsat': bool(st.get('cadical_log_parse', {}).get('unsat')),
                'sat': bool(st.get('cadical_log_parse', {}).get('sat')),
                'verified': bool(st.get('drat_trim_log_parse', {}).get('verified')),
                'hashes': st.get('hashes', {}),
            }
            pair_record['attempts'].append(attempt)
            if attempt['unsat'] and attempt['verified']:
                pair_record['closed_by_verified_unsat'] = True
                pair_record['closed_filter'] = max_size
                break
        records.append(pair_record)
        summary = {
            'problem': 'exact-18 high-pair filtered proof batch',
            'field': 'F2',
            'rank_s': args.rank_s,
            'exact_rank1_count': args.exact_rank1_count,
            'fixed_rank1': fixed_rank1,
            'allowed_single_reps': None if allowed is None else sorted(allowed),
            'pair_orbit_total_count': len(pairs),
            'start_index': args.start_index,
            'selected_count': len(selected),
            'completed_count': len(records),
            'closed_count': sum(1 for r in records if r['closed_by_verified_unsat']),
            'closed_indices': [r['pair_orbit_global_index'] for r in records if r['closed_by_verified_unsat']],
            'open_indices_in_batch': [r['pair_orbit_global_index'] for r in records if not r['closed_by_verified_unsat']],
            'closed_filter_hist': dict(sorted(Counter(r['closed_filter'] for r in records if r['closed_filter'] is not None).items())),
            'records': records,
            'elapsed_sec': time.time() - t0,
            'meaning': 'Only leaves with closed_by_verified_unsat true are proof components; SAT or timeout at a smaller filter only guides the next filter.',
        }
        args.summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'summary': str(args.summary),
        'completed_count': len(records),
        'closed_count': sum(1 for r in records if r['closed_by_verified_unsat']),
        'closed_filter_hist': dict(sorted(Counter(r['closed_filter'] for r in records if r['closed_filter'] is not None).items())),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
