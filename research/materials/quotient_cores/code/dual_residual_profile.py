#!/usr/bin/env python3
"""analysis: profile which E11-core Wang rows add information beyond contraction ranks.

Using the exact annihilator reformulation, a row U with D=U^perp, k=dim D,
L=L(U), and linked contraction weights w(q) is

    sum_{q in D\0} w(q) >= 2^(k-1) L.

If the individual contraction lower bounds w(q) >= rank L(q) imply this row,
i.e. if sum_{q in D\0} rank L(q) >= 2^(k-1)L, then the row is redundant in a
model that already includes all contraction lower bounds.  Rows with positive
residual demand are the genuinely joint occupation/contraction requirements in
this representation.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Sequence

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints  # noqa: E402
from quotient_rank_cuts import build_contractions  # noqa: E402
from wang_capacity_lazy import pack_basis, rref_basis, unpack_basis  # noqa: E402

OUTDIR = ROOT / "workspace/data/hybrid_annihilator"


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}, payload.get('meta', {})


def parity_dot(q: int, p: int) -> int:
    return (int(q) & int(p)).bit_count() & 1


def annihilator_points(basis: Sequence[int], n: int = 8):
    bs = [int(b) for b in basis]
    return [q for q in range(1, 1 << n) if all(parity_dot(q, u) == 0 for u in bs)]


def D_key(D: Sequence[int]) -> int:
    return pack_basis(rref_basis(D, n=8))


def support_weights(A: Sequence[int]) -> dict[int, int]:
    return {q: sum(1 for p in A if parity_dot(q, p)) for q in range(1, 256)}


def load_support(path: Path | None, index: int = 0):
    if path is None:
        return None
    d = json.loads(path.read_text())
    if 'A_cols' in d:
        return [int(x) for x in d['A_cols']]
    if d.get('solutions'):
        return [int(x) for x in d['solutions'][index]['A_cols']]
    if d.get('rounds'):
        r = d['rounds'][index]
        return [int(x) for x in (r.get('support') or r.get('A_cols'))]
    raise ValueError(f'no support in {path}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--threshold-L', type=int, default=0)
    ap.add_argument('--support-json', type=Path, default=ROOT / 'workspace/data/distinct_line_cover/threshold_L15_300s.json')
    ap.add_argument('--support-index', type=int, default=0)
    ap.add_argument('--store-positive', type=int, default=200)
    ap.add_argument('--out', type=Path, default=OUTDIR / 'dual_residual_profile.json')
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    lut,_ = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    core = CoreQuotient(1)
    records, meta = build_core_constraints(core, lut)
    T = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    contractions = build_contractions(T)
    rank = {q: int(c['rank']) for q, c in contractions.items()}
    A = load_support(args.support_json, args.support_index)
    weights = support_weights(A) if A is not None else None

    by_dim_L = Counter()
    by_dim_L_resid = Counter()
    by_k_L_resid = Counter()
    by_k_rank_pattern_resid = Counter()
    redundant_by_dim_L = Counter()
    positive_by_dim_L = Counter()
    positive_rows = []
    support_violating_positive = []
    support_violating_redundant = []
    exact_clb_rows = []

    for rec in records:
        L = int(rec['L'])
        if L < args.threshold_L:
            continue
        d = int(rec['dim8'])
        k = 8 - d
        by_dim_L[(d, L)] += 1
        if k <= 0:
            continue
        D = annihilator_points(unpack_basis(int(rec['key8'])), 8)
        req = (1 << (k - 1)) * L
        rks = [rank[q] for q in D]
        rank_sum = sum(rks)
        residual = req - rank_sum
        patt = tuple(sorted(Counter(rks).items()))
        by_dim_L_resid[(d, L, residual)] += 1
        by_k_L_resid[(k, L, residual)] += 1
        by_k_rank_pattern_resid[(k, patt, residual)] += 1
        if residual <= 0:
            redundant_by_dim_L[(d, L)] += 1
        else:
            positive_by_dim_L[(d, L)] += 1
            if len(positive_rows) < args.store_positive:
                positive_rows.append({
                    'key8': int(rec['key8']),
                    'basis8': list(unpack_basis(int(rec['key8']))),
                    'dim8': d,
                    'codim_dual_k': k,
                    'key9': int(rec['key9']),
                    'L': L,
                    'D_key': int(D_key(D)),
                    'D_basis': list(unpack_basis(D_key(D))),
                    'D_nonzero': D,
                    'rank_pattern': {str(rr): int(cc) for rr, cc in sorted(Counter(rks).items())},
                    'rank_sum': int(rank_sum),
                    'requirement': int(req),
                    'residual_over_individual_contraction_bounds': int(residual),
                })
        if weights is not None:
            wsum = sum(weights[q] for q in D)
            violated = wsum < req
            item = None
            if violated:
                item = {
                    'key8': int(rec['key8']), 'dim8': d, 'L': L,
                    'codim_dual_k': k,
                    'D_key': int(D_key(D)),
                    'D_nonzero': D,
                    'weights': [weights[q] for q in D],
                    'rank_pattern': {str(rr): int(cc) for rr, cc in sorted(Counter(rks).items())},
                    'rank_sum': int(rank_sum), 'weight_sum': int(wsum),
                    'requirement': int(req),
                    'annihilator_deficit': int(req - wsum),
                    'residual_over_clb': int(residual),
                }
                if residual > 0:
                    support_violating_positive.append(item)
                else:
                    support_violating_redundant.append(item)
            if k == 1 and L == rank_sum and len(exact_clb_rows) < 20:
                exact_clb_rows.append({'q': D[0], 'L': L, 'rank': rank_sum})

    def tuple_counter_to_dict(c: Counter, limit: int | None = None):
        items = c.items()
        if limit is not None:
            items = sorted(items, key=lambda kv: (-kv[1], str(kv[0])))[:limit]
        else:
            items = sorted(items, key=lambda kv: str(kv[0]))
        return {str(k): int(v) for k, v in items}

    out = {
        'schema': 'dual_residual_profile_v1',
        'field': 'F2', 'core': 'E11', 'rank_s': 19,
        'threshold_L': int(args.threshold_L),
        'complete_core_table_meta': meta,
        'support_json': None if args.support_json is None else str(args.support_json),
        'support': A,
        'row_count_considered': int(sum(by_dim_L.values())),
        'by_dim_L': tuple_counter_to_dict(by_dim_L),
        'redundant_by_individual_contraction_bounds_by_dim_L': tuple_counter_to_dict(redundant_by_dim_L),
        'positive_residual_by_dim_L': tuple_counter_to_dict(positive_by_dim_L),
        'by_dim_L_residual_head': tuple_counter_to_dict(by_dim_L_resid, limit=120),
        'by_k_L_residual_head': tuple_counter_to_dict(by_k_L_resid, limit=120),
        'by_k_rank_pattern_residual_head': tuple_counter_to_dict(by_k_rank_pattern_resid, limit=160),
        'positive_rows_stored': positive_rows,
        'support_violating_positive_count': len(support_violating_positive),
        'support_violating_positive_rows': support_violating_positive[:80],
        'support_violating_redundant_count': len(support_violating_redundant),
        'support_violating_redundant_rows': support_violating_redundant[:20],
        'exact_dim7_contraction_rows_sample': exact_clb_rows,
        'interpretation': 'Rows with residual<=0 are implied by linked contraction lower bounds in the annihilator-weight representation. Positive residual rows are joint requirements across a dual subspace D and are the part not explained by individual contractions.',
        'elapsed_sec': round(time.time()-t0, 3),
    }
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(args.out),
        'rows': out['row_count_considered'],
        'positive_residual_rows': int(sum(positive_by_dim_L.values())),
        'support_violating_positive_count': len(support_violating_positive),
        'support_violating_redundant_count': len(support_violating_redundant),
        'elapsed_sec': out['elapsed_sec'],
    }, sort_keys=True))


if __name__ == '__main__':
    main()
