#!/usr/bin/env python3
"""Rank distributions of matrix subspaces S and residual affine cosets."""
from __future__ import annotations
import argparse, json, sys, time
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np

SCRIPTS = Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import e11_s_coset_rank_sat as scoset  # noqa: E402


def rank_dist_for_coset(base: int, basis: tuple[int, ...]) -> Counter:
    cur = int(base)
    hist = Counter({scoset.gf2_rank_rows(scoset.rows_from_mask81(cur)): 1})
    n = len(basis)
    for step in range(1, 1 << n):
        j = (step & -step).bit_length() - 1
        cur ^= basis[j]
        hist[scoset.gf2_rank_rows(scoset.rows_from_mask81(cur))] += 1
    return hist


def matrix_mask_from_np(M: np.ndarray) -> int:
    out = 0
    for b in range(9):
        row = 0
        for c in range(9):
            if int(M[b, c]) & 1:
                row |= 1 << c
        out |= row << (9 * b)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--prefix', required=True)
    ap.add_argument('--pool', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--max-S', type=int, default=0)
    args = ap.parse_args()
    t0 = time.time()
    prefix = [int(x) for x in args.prefix.split(',') if x.strip()]
    pool = np.load(args.pool)
    basis_to_scheme = {}
    for i, scheme in enumerate(pool):
        S = scoset.scheme_s_basis(scheme)
        basis_to_scheme.setdefault(S, i)
    S_list = sorted(basis_to_scheme.keys())
    if args.max_S:
        S_list = S_list[:args.max_S]
    _, _, _, Rcoords = scoset.quotient_base_residual(prefix)
    R_phi_masks = {}
    for phi in range(1, 16):
        M = np.zeros((9, 9), dtype=np.uint8)
        for k in range(4):
            if (phi >> k) & 1:
                M ^= Rcoords[k]
        R_phi_masks[phi] = matrix_mask_from_np(M)
    records = []
    subspace_dist_counter = Counter()
    coset_profile_counter = Counter()
    for si, S in enumerate(S_list):
        subhist = rank_dist_for_coset(0, S)
        subkey = tuple(subhist.get(r, 0) for r in range(10))
        subspace_dist_counter[subkey] += 1
        cosets = {}
        for phi in range(1, 16):
            h = rank_dist_for_coset(R_phi_masks[phi], S)
            cosets[phi] = {str(r): int(h.get(r, 0)) for r in range(10) if h.get(r, 0)}
        coskey = tuple(tuple(int(cosets[phi].get(str(r), 0)) for r in range(10)) for phi in range(1, 16))
        coset_profile_counter[coskey] += 1
        if si < 20:
            records.append({
                'S_index': si,
                'S_hash': scoset.basis_hash(S),
                'scheme_index': basis_to_scheme[S],
                'S_rank_distribution': {str(r): int(subhist.get(r, 0)) for r in range(10) if subhist.get(r, 0)},
                'coset_rank_distributions': cosets,
            })
        if si < 5 or si % 100 == 0:
            print(f'S {si}/{len(S_list)} Sdist={dict(subhist)}')
    result = {
        'purpose': 'rank distributions of sampled S subspaces and residual contraction cosets',
        'field': 'F2',
        'prefix': prefix,
        'pool': str(args.pool),
        'distinct_S_analyzed': len(S_list),
        'S_rank_distribution_type_count': len(subspace_dist_counter),
        'S_rank_distribution_types': [
            {'rank_histogram': {str(r): int(v) for r, v in enumerate(k) if v}, 'count': int(c)}
            for k, c in subspace_dist_counter.most_common(20)
        ],
        'coset_rank_profile_type_count': len(coset_profile_counter),
        'coset_rank_profile_counts_head': [int(c) for _, c in coset_profile_counter.most_common(20)],
        'records_head': records,
        'elapsed_sec': time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: result[k] for k in ['distinct_S_analyzed','S_rank_distribution_type_count','coset_rank_profile_type_count','coset_rank_profile_counts_head','elapsed_sec']}, indent=2, sort_keys=True))
    print('wrote', args.out)

if __name__ == '__main__':
    main()
