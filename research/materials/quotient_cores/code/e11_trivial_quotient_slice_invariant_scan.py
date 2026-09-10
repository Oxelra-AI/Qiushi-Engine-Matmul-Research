#!/usr/bin/env python3
"""Slice-rank invariant scan for coordinate quotient CPDs on prefix-span orbits."""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

SCRIPTS = Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import e11_quotient_lift_general_sat as glift  # noqa: E402
import e11_lift_slice_rank_invariants as slicer  # noqa: E402


def coordinate_scheme(Q: np.ndarray) -> np.ndarray:
    terms = []
    for a, b, c in np.argwhere(Q.astype(np.uint8) & 1):
        terms.extend([1 << int(a), 1 << int(b), 1 << int(c)])
    return np.array(terms, dtype=np.uint16)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--invariants', type=Path, default=Path('data/prefix_span_orbits/prefix_span_orbit_invariants_top1000.json'))
    ap.add_argument('--max-q', type=int, default=15)
    ap.add_argument('--out', type=Path, default=Path('data/lift_slice_rank_invariants/coordinate_q_le15_all36_slice_rank.json'))
    args = ap.parse_args()
    t0 = time.time()
    inv = json.loads(args.invariants.read_text())
    reps = [r for r in inv['directly_testable_by_trivial_quotient_rank_le15_head'] if int(r['quotient_nnz']) <= args.max_q]
    core = glift.build_e11_core()
    records = []
    for i, r in enumerate(reps):
        prefix = [int(x) for x in r['basis']]
        ann = glift.annihilator_basis(prefix, 8)
        Q = glift.quotient_core(core, ann)
        scheme = coordinate_scheme(Q)
        q = len(scheme) // 3
        s = 19 - q
        rec = slicer.analyze_scheme(core, prefix, scheme, s, hist=False)
        rec.update({
            'orbit_id': int(r['orbit_id']),
            'prefix_basis': prefix,
            'Wang_L': int(r['Wang_L']),
            'Wang_cap_at_rank19': int(r['Wang_cap_at_rank19']),
            'orbit_size': int(r['orbit_size']),
            'coordinate_quotient_rank': int(q),
            'residual_rank_budget': int(s),
            'quotient_flattening_ranks': r['flattening_ranks'],
            'quotient_nnz': int(r['quotient_nnz']),
        })
        records.append(rec)
        print(f"{i+1}/{len(reps)} orbit {r['orbit_id']} q={q} s={s} sum_m={rec.get('sum_m_phi')} eight_s={8*s} cover={rec.get('cover_condition',{}).get('cover_feasible')}")
    by_q = Counter(int(r['coordinate_quotient_rank']) for r in records)
    by_pair = Counter((int(r['coordinate_quotient_rank']), bool(r.get('cover_condition', {}).get('cover_feasible'))) for r in records)
    by_sum = Counter((int(r['coordinate_quotient_rank']), int(r.get('sum_m_phi', -1)), int(r.get('eight_s_bound', -1))) for r in records)
    result = {
        'purpose': 'exact contraction-coset necessary obstruction for all low-q coordinate quotient schemes on 4D E11 prefix-span orbits',
        'field': 'F2',
        'source_invariants': str(args.invariants),
        'max_coordinate_q': int(args.max_q),
        'representatives_analyzed': len(records),
        'coordinate_q_distribution': dict(sorted((str(k), int(v)) for k, v in by_q.items())),
        'q_cover_feasible_distribution': {f'{k[0]},{k[1]}': int(v) for k, v in sorted(by_pair.items())},
        'q_sum_m_eight_s_distribution': {f'{k[0]},{k[1]},{k[2]}': int(v) for k, v in sorted(by_sum.items())},
        'all_cover_infeasible': all(not bool(r.get('cover_condition', {}).get('cover_feasible')) for r in records),
        'meaning': 'For each coordinate quotient CPD, cover infeasibility proves no lift within total E11 rank 19 for that fixed coordinate quotient scheme. It does not exclude other quotient CPDs of the same quotient tensor.',
        'elapsed_sec': time.time() - t0,
        'records': records,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True, default=int) + '\n')
    print(json.dumps({k: result[k] for k in ['representatives_analyzed','coordinate_q_distribution','q_cover_feasible_distribution','all_cover_infeasible','elapsed_sec']}, indent=2, sort_keys=True))
    print('wrote', args.out)


if __name__ == '__main__':
    main()
