#!/usr/bin/env python3
"""Orbit and quotient invariants for 4D E11 A-prefix spans over F2.

Uses the verified 576-element quotient action and the complete Wang cache/orbit
surface to summarize all 4-dimensional subspace orbits.  These are the natural
prefix-span classes for quotient-lift experiments.
"""
from __future__ import annotations

import argparse
import json
import pickle
import time
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np


def parity(x: int) -> int:
    return int(x).bit_count() & 1


def gf2_basis(vectors: list[int]) -> list[int]:
    basis: dict[int, int] = {}
    for v in vectors:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                break
    return sorted(basis.values(), reverse=True)


def gf2_rank_int(vectors: list[int]) -> int:
    return len(gf2_basis(vectors))


def points_from_mask(mask: int) -> list[int]:
    pts = []
    m = int(mask)
    p = 1
    while m:
        if m & 1:
            pts.append(p)
        m >>= 1
        p += 1
    return pts


def span_mask(basis: list[int]) -> int:
    pts = set()
    d = len(basis)
    for code in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis):
            if (code >> i) & 1:
                v ^= int(b)
        pts.add(v)
    m = 0
    for p in pts:
        m |= 1 << (p - 1)
    return m


def choose_basis(points: list[int], d: int) -> list[int]:
    basis: list[int] = []
    for p in points:
        if gf2_rank_int(basis + [p]) > len(basis):
            basis.append(p)
            if len(basis) == d:
                return basis
    raise RuntimeError('no basis')


def annihilator_basis(prefix: list[int], n: int = 8) -> list[int]:
    d = gf2_rank_int(prefix)
    out: list[int] = []
    for l in range(1, 1 << n):
        if all(parity(l & v) == 0 for v in prefix):
            if gf2_rank_int(out + [l]) > len(out):
                out.append(l)
                if len(out) == n - d:
                    return out
    raise RuntimeError('no ann')


def gf2_rank_mat(M: np.ndarray) -> int:
    M = M.copy().astype(np.uint8)
    m, n = M.shape
    r = 0
    for col in range(n):
        piv = None
        for row in range(r, m):
            if M[row, col] & 1:
                piv = row
                break
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        for row in range(m):
            if row != r and (M[row, col] & 1):
                M[row] ^= M[r]
        r += 1
    return r


def build_e11_core() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1
    return T[1:, :, :]


def quotient_core(core: np.ndarray, ann: list[int]) -> np.ndarray:
    q = np.zeros((len(ann), core.shape[1], core.shape[2]), dtype=np.uint8)
    for i, l in enumerate(ann):
        for a in range(core.shape[0]):
            if (int(l) >> a) & 1:
                q[i] ^= core[a]
    return q


def quotient_invariants(core: np.ndarray, basis: list[int]) -> dict:
    ann = annihilator_basis(basis, 8)
    Q = quotient_core(core, ann)
    Af = Q.reshape(Q.shape[0], -1)
    Bf = np.transpose(Q, (1, 0, 2)).reshape(Q.shape[1], -1)
    Cf = np.transpose(Q, (2, 0, 1)).reshape(Q.shape[2], -1)
    return {
        'annihilator_basis': ann,
        'quotient_shape': list(Q.shape),
        'quotient_nnz': int(Q.sum()),
        'flattening_ranks': {
            'A': gf2_rank_mat(Af),
            'B': gf2_rank_mat(Bf),
            'C': gf2_rank_mat(Cf),
        },
        'flattening_lower_bound': max(gf2_rank_mat(Af), gf2_rank_mat(Bf), gf2_rank_mat(Cf)),
        'trivial_coordinate_rank_upper_bound': int(Q.sum()),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--cache', type=Path, default=Path('data/e11_capacity_sat/e11_capacity_cache.pkl'))
    ap.add_argument('--orbits', type=Path, default=Path('data/e11_subspace_orbits/e11_subspace_orbits.npz'))
    ap.add_argument('--out', type=Path, default=Path('data/prefix_span_orbits/prefix_span_orbit_invariants.json'))
    ap.add_argument('--top', type=int, default=40)
    args = ap.parse_args()
    t0 = time.time()
    cache = pickle.load(args.cache.open('rb'))
    masks = [int(x) for x in cache['masks']]
    dims = [int(x) for x in cache['dims']]
    Ls = [int(x) for x in cache['Ls']]
    caps = [int(x) for x in cache['caps']]
    orbit_data = np.load(args.orbits)
    orbit_id = orbit_data['orbit_id']
    offsets = orbit_data['offsets']
    rep_indices = orbit_data['rep_indices']
    core = build_e11_core()
    mask_to_idx = {m: i for i, m in enumerate(masks)}

    dim4_records = []
    for oid, idx in enumerate(rep_indices.tolist()):
        idx = int(idx)
        if dims[idx] != 4:
            continue
        pts = points_from_mask(masks[idx])
        bas = choose_basis(pts, 4)
        inv = quotient_invariants(core, bas)
        dim4_records.append({
            'orbit_id': int(oid),
            'orbit_size': int(offsets[oid + 1] - offsets[oid]),
            'cache_index': idx,
            'Wang_L': Ls[idx],
            'Wang_cap_at_rank19': caps[idx],
            'subspace_points': pts,
            'basis': bas,
            **inv,
        })

    by_qnnz = Counter(r['quotient_nnz'] for r in dim4_records)
    by_lb = Counter(r['flattening_lower_bound'] for r in dim4_records)
    by_cap = Counter(r['Wang_cap_at_rank19'] for r in dim4_records)
    by_qnnz_lb = Counter((r['quotient_nnz'], r['flattening_lower_bound']) for r in dim4_records)

    def locate(prefix: list[int]) -> dict:
        m = span_mask(prefix)
        idx = mask_to_idx.get(m)
        if idx is None:
            return {'prefix': prefix, 'span_mask_found': False}
        oid = int(orbit_id[idx])
        rec = next((r for r in dim4_records if r['orbit_id'] == oid), None)
        return {
            'prefix': prefix,
            'span_mask_found': True,
            'cache_index': int(idx),
            'orbit_id': oid,
            'orbit_size': int(offsets[oid + 1] - offsets[oid]),
            'representative_basis': None if rec is None else rec['basis'],
            'representative_quotient_nnz': None if rec is None else rec['quotient_nnz'],
            'representative_flattening_ranks': None if rec is None else rec['flattening_ranks'],
            'representative_Wang_cap': None if rec is None else rec['Wang_cap_at_rank19'],
        }

    # representative choices useful for next tests
    sorted_low = sorted(dim4_records, key=lambda r: (r['quotient_nnz'], r['flattening_lower_bound'], r['Wang_cap_at_rank19'], -r['orbit_size'], r['orbit_id']))
    sorted_high_cap_low = sorted(dim4_records, key=lambda r: (-r['Wang_cap_at_rank19'], r['quotient_nnz'], r['flattening_lower_bound'], r['orbit_id']))
    # q <= 15 are directly testable with rank_res >= 4 by trivial coordinate quotient schemes.
    directly_rank19_trivial = [r for r in sorted_low if r['quotient_nnz'] <= 15]

    result = {
        'purpose': 'classify 4D E11 A-prefix-span orbits and quotient invariants for corrected coset-lift route',
        'field': 'F2',
        'group': 'verified 576-element corrected E11 quotient action from analysis',
        'dim4_orbit_count': len(dim4_records),
        'q_nnz_distribution': dict(sorted(by_qnnz.items())),
        'flattening_lower_bound_distribution': dict(sorted(by_lb.items())),
        'Wang_cap_distribution_rank19': dict(sorted(by_cap.items())),
        'q_nnz_by_flattening_lb': {f'{k[0]},{k[1]}': v for k, v in sorted(by_qnnz_lb.items())},
        'located_prefixes': {
            'leaf0_80_122_191_213': locate([80, 122, 191, 213]),
            'standard_1_2_4_8': locate([1, 2, 4, 8]),
        },
        'low_qnnz_representatives_head': sorted_low[:args.top],
        'high_Wang_cap_low_qnnz_head': sorted_high_cap_low[:args.top],
        'directly_testable_by_trivial_quotient_rank_le15_count': len(directly_rank19_trivial),
        'directly_testable_by_trivial_quotient_rank_le15_head': directly_rank19_trivial[:args.top],
        'meaning': 'These are prefix-span orbit representatives, not CPD classifications. q_nnz gives only a coordinate upper bound on quotient rank. General coset-lift SAT on a representative tests a chosen quotient scheme, not all quotient schemes.',
        'elapsed_sec': time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'dim4_orbit_count': result['dim4_orbit_count'],
        'q_nnz_distribution': result['q_nnz_distribution'],
        'flattening_lower_bound_distribution': result['flattening_lower_bound_distribution'],
        'directly_q_le15': result['directly_testable_by_trivial_quotient_rank_le15_count'],
        'located_prefixes': result['located_prefixes'],
        'out': str(args.out),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
