#!/usr/bin/env python3
"""Make positive regression inputs for the general quotient-lift SAT.

Starting from a known E11 CPD, choose a 4D A-subspace V, project all terms to
A/V, and save the induced quotient CPD.  The omitted terms inside V give a known
residual budget, so the general lift SAT should be SAT and decode back to the
known E11 tensor (possibly with an equivalent decomposition).
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
from collections import Counter
from pathlib import Path

import numpy as np

SCRIPTS = Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import e11_quotient_lift_general_sat as g  # noqa: E402


def project_mask(u: int, ann: list[int]) -> int:
    q = 0
    for i, l in enumerate(ann):
        if (int(u) & int(l)).bit_count() & 1:
            q |= 1 << i
    return q


def choose_span(us: list[int], target_inside: int | None = 4) -> tuple[list[int], list[int]]:
    uniq = sorted(set(int(u) for u in us if int(u)))
    best = None
    best_inside = None
    # Prefer independent bases whose span contains target_inside terms; otherwise closest above target.
    for combo in itertools.combinations(uniq, 4):
        if g.gf2_rank_int(list(combo)) != 4:
            continue
        pts = set()
        for code in range(1, 16):
            v = 0
            for i, b in enumerate(combo):
                if (code >> i) & 1:
                    v ^= b
            pts.add(v)
        inside = [i for i, u in enumerate(us) if int(u) in pts]
        k = len(inside)
        if target_inside is not None and k == target_inside:
            return list(combo), inside
        score = (abs(k - (target_inside or 4)), k, combo)
        if best is None or score < best:
            best = score
            best_inside = (list(combo), inside)
    if best_inside is None:
        raise RuntimeError('no independent 4D span found')
    return best_inside


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--pool', type=Path, default=Path('data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy'))
    ap.add_argument('--row', type=int, default=0)
    ap.add_argument('--target-inside', type=int, default=4)
    ap.add_argument('--prefix', default='', help='optional explicit 4-mask basis')
    ap.add_argument('--outdir', type=Path, default=Path('data/general_lift_positive_regression'))
    ap.add_argument('--name', default='known_rank21_regression')
    args = ap.parse_args()
    pool = np.load(args.pool)
    scheme = pool[args.row]
    r = len(scheme) // 3
    us = [int(scheme[3*j]) for j in range(r)]
    vs = [int(scheme[3*j+1]) for j in range(r)]
    ws = [int(scheme[3*j+2]) for j in range(r)]
    if args.prefix.strip():
        prefix = [int(x) for x in args.prefix.split(',') if x.strip()]
        if len(prefix) != 4 or g.gf2_rank_int(prefix) != 4:
            raise ValueError('explicit prefix must be independent length 4')
        pts = set()
        for code in range(1, 16):
            v = 0
            for i, b in enumerate(prefix):
                if (code >> i) & 1:
                    v ^= b
            pts.add(v)
        inside = [i for i, u in enumerate(us) if int(u) in pts]
    else:
        prefix, inside = choose_span(us, target_inside=args.target_inside)
    ann = g.annihilator_basis(prefix, 8)
    qterms = []
    outside = []
    qmask_counter = Counter()
    for j, u in enumerate(us):
        q = project_mask(u, ann)
        if q == 0:
            if j not in inside:
                inside.append(j)
            continue
        outside.append(j)
        qmask_counter[q] += 1
        qterms.extend([q, vs[j], ws[j]])
    qrank = len(qterms) // 3
    rank_res = len(inside)
    args.outdir.mkdir(parents=True, exist_ok=True)
    qpool_path = args.outdir / f'{args.name}_q{qrank}_res{rank_res}.npy'
    np.save(qpool_path, np.array([qterms], dtype=np.uint16))
    # Verify induced quotient with the general-lift utilities.
    core = g.build_e11_core()
    meta, _, _, _, _, _ = g.scheme_to_residual(core, prefix, np.array(qterms, dtype=np.uint16))
    rec = {
        'purpose': 'positive regression input for exact general quotient-lift SAT',
        'source_pool': str(args.pool),
        'source_row': int(args.row),
        'source_rank': r,
        'prefix_basis': prefix,
        'annihilator_basis': ann,
        'inside_term_indices': sorted(set(int(x) for x in inside)),
        'inside_term_count': rank_res,
        'outside_term_indices': outside,
        'quotient_rank_from_source_terms': qrank,
        'rank_residual_budget_for_source_lift': rank_res,
        'total_rank_budget': qrank + rank_res,
        'quotient_mask_multiplicities': dict(sorted((int(k), int(v)) for k, v in qmask_counter.items())),
        'qpool_path': str(qpool_path),
        'quotient_verification_meta': meta,
        'source_u_masks': us,
        'source_v_masks': vs,
        'source_w_masks': ws,
    }
    out_json = args.outdir / f'{args.name}_meta.json'
    out_json.write_text(json.dumps(rec, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'prefix_basis': prefix,
        'inside_term_count': rank_res,
        'quotient_rank_from_source_terms': qrank,
        'total_rank_budget': qrank + rank_res,
        'qpool_path': str(qpool_path),
        'quotient_diff': meta['quotient_diff'],
        'residual_reconstruction_diff': meta['residual_reconstruction_diff'],
        'annihilator_residual_nnz': meta['annihilator_residual_nnz'],
        'out_json': str(out_json),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
