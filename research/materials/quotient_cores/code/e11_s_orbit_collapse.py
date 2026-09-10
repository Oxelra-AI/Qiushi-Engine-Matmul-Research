#!/usr/bin/env python3
"""Collapse E11 quotient CPD schemes to matrix-subspace S orbits.

For a fixed 4-dimensional E11 A-prefix V and a pool of quotient CPDs, each
quotient scheme supplies q rank-one B-C matrices M_j=b_j\otimes c_j.  The
lift-back problem only uses their span S=span(M_j) through the coset
T - \tilde Q + V\otimes S, provided the quotient tensor lies in (A/V)\otimes S.

This script extracts the distinct S subspaces from a quotient CPD pool and
collapses them under the verified E11 quotient stabilizer subgroup that preserves
V as a subspace.  It records representatives, multiplicities, dimensions and
hashes so later S-level coset tests can avoid repeated scheme-level negatives.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from collections import Counter, defaultdict, deque
from pathlib import Path

import numpy as np

SCRIPTS = Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import e11_quotient_action_verify as qact  # noqa: E402

N_MAT = 81


def gf2_rank_int(vecs: list[int]) -> int:
    basis: dict[int, int] = {}
    for v in vecs:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                break
    return len(basis)


def rref_basis(vecs: list[int], nbits: int = N_MAT) -> tuple[int, ...]:
    """Canonical reduced row-echelon basis, using highest set bit as pivot."""
    basis = [0] * nbits
    for v in vecs:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if basis[p]:
                x ^= basis[p]
            else:
                basis[p] = x
                break
    # Reduce lower pivot bits out of higher pivot rows.
    for p in range(nbits):
        if not basis[p]:
            continue
        bit = 1 << p
        for q in range(p + 1, nbits):
            if basis[q] & bit:
                basis[q] ^= basis[p]
    return tuple(basis[p] for p in range(nbits - 1, -1, -1) if basis[p])


def basis_hash(basis: tuple[int, ...]) -> str:
    h = hashlib.sha256()
    h.update(len(basis).to_bytes(2, 'little'))
    for x in basis:
        h.update(int(x).to_bytes(11, 'little'))  # 81 bits fit in 11 bytes
    return h.hexdigest()


def span_nonzero(prefix: list[int]) -> set[int]:
    out = {0}
    for v in prefix:
        out |= {x ^ int(v) for x in list(out)}
    out.discard(0)
    return out


def outer_mask(bmask: int, cmask: int) -> int:
    out = 0
    c = int(cmask)
    b = int(bmask)
    for i in range(9):
        if (b >> i) & 1:
            out ^= c << (9 * i)
    return out


def rows_from_mask81(mask: int) -> list[int]:
    return [(int(mask) >> (9 * i)) & 0x1ff for i in range(9)]


def apply_linear_to_mask(mask: int, bit_images: list[int]) -> int:
    x = int(mask)
    out = 0
    pos = 0
    while x:
        if x & 1:
            out ^= bit_images[pos]
        x >>= 1
        pos += 1
    return out


def bit_images_for_pair(P: np.ndarray, Q: np.ndarray) -> list[int]:
    imgs: list[int] = []
    for b in range(9):
        b2 = qact.apply_B(1 << b, Q)
        for c in range(9):
            c2 = qact.apply_W(1 << c, P)
            imgs.append(outer_mask(b2, c2))
    return imgs


def scheme_s_basis(scheme: np.ndarray) -> tuple[int, ...]:
    q = len(scheme) // 3
    mats = []
    for j in range(q):
        b = int(scheme[3 * j + 1])
        c = int(scheme[3 * j + 2])
        mats.append(outer_mask(b, c))
    return rref_basis(mats)


def make_stabilizer(prefix: list[int]) -> list[dict]:
    gl = qact.generate_gl3()
    P_list = qact.direct_P_row_stabilizer(gl)
    Q_list = qact.direct_Q_col_stabilizer(gl)
    Vset = span_nonzero(prefix)
    stabs = []
    seen_perm = set()
    for P in P_list:
        for Q in Q_list:
            perm = qact.perm_for_pair(P, Q)
            img = {perm[x] for x in Vset}
            if img == Vset:
                pt = tuple(perm)
                if pt in seen_perm:
                    continue
                seen_perm.add(pt)
                stabs.append({
                    'P_key': qact.mat_key(P),
                    'Q_key': qact.mat_key(Q),
                    'perm': pt,
                    'bit_images': bit_images_for_pair(P, Q),
                })
    return stabs


def transform_basis(basis: tuple[int, ...], bit_images: list[int]) -> tuple[int, ...]:
    return rref_basis([apply_linear_to_mask(x, bit_images) for x in basis])


def canonical_under_stabilizer(basis: tuple[int, ...], stabs: list[dict]) -> tuple[int, ...]:
    best = basis
    for g in stabs:
        img = transform_basis(basis, g['bit_images'])
        if img < best:
            best = img
    return best


def orbit_from_seed(seed: tuple[int, ...], stabs: list[dict], universe: set[tuple[int, ...]] | None = None) -> set[tuple[int, ...]]:
    seen = {seed}
    dq = deque([seed])
    while dq:
        b = dq.popleft()
        for g in stabs:
            im = transform_basis(b, g['bit_images'])
            if universe is not None and im not in universe:
                # This can happen when the full orbit contains S spaces not present in the sampled pool.
                continue
            if im not in seen:
                seen.add(im)
                dq.append(im)
    return seen


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--pool', type=Path, required=True)
    ap.add_argument('--prefix', required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--save-npz', type=Path, default=None)
    args = ap.parse_args()

    t0 = time.time()
    prefix = [int(x) for x in args.prefix.split(',') if x.strip()]
    if len(prefix) != 4 or gf2_rank_int(prefix) != 4:
        raise ValueError('prefix must be an independent 4-tuple')
    pool = np.load(args.pool)
    q = pool.shape[1] // 3

    stabs = make_stabilizer(prefix)
    basis_to_schemes: dict[tuple[int, ...], list[int]] = defaultdict(list)
    for i, scheme in enumerate(pool):
        b = scheme_s_basis(scheme)
        basis_to_schemes[b].append(i)

    distinct = sorted(basis_to_schemes.keys())
    canon_to_members: dict[tuple[int, ...], list[tuple[int, ...]]] = defaultdict(list)
    for b in distinct:
        canon_to_members[canonical_under_stabilizer(b, stabs)].append(b)

    # Compute sampled-pool orbits by closing only inside the observed distinct-S universe.
    universe = set(distinct)
    unseen = set(distinct)
    observed_orbits = []
    while unseen:
        seed = min(unseen)
        orb = orbit_from_seed(seed, stabs, universe=universe)
        unseen -= orb
        observed_orbits.append(sorted(orb))

    dim_dist = Counter(len(b) for b in distinct)
    mult_dist = Counter(len(v) for v in basis_to_schemes.values())
    sampled_orbit_size_dist = Counter(len(o) for o in observed_orbits)

    records = []
    for idx, b in enumerate(distinct):
        records.append({
            's_index': idx,
            'dim': len(b),
            'multiplicity': len(basis_to_schemes[b]),
            'scheme_indices_head': basis_to_schemes[b][:20],
            'basis_hash': basis_hash(b),
            'basis_hex': [hex(x) for x in b],
            'canonical_hash': basis_hash(canonical_under_stabilizer(b, stabs)),
        })

    orbit_records = []
    for oi, orb in enumerate(sorted(observed_orbits, key=lambda o: (len(o), min(o)))):
        mult = sum(len(basis_to_schemes[b]) for b in orb)
        rep = min(orb)
        orbit_records.append({
            'observed_s_orbit_index': oi,
            'observed_size_in_pool': len(orb),
            'total_scheme_multiplicity': mult,
            'rep_hash': basis_hash(rep),
            'rep_basis_hex': [hex(x) for x in rep],
            'member_hashes': [basis_hash(b) for b in orb],
            'scheme_indices_head': sorted([j for b in orb for j in basis_to_schemes[b]])[:30],
        })

    result = {
        'purpose': 'collapse quotient CPD schemes to matrix subspace S and S-orbits under the V-stabilizer',
        'field': 'F2',
        'prefix': prefix,
        'pool': str(args.pool),
        'pool_shape': list(pool.shape),
        'q_terms': q,
        'stabilizer_size_preserving_V': len(stabs),
        'distinct_S_count': len(distinct),
        'distinct_S_dim_distribution': {str(k): int(v) for k, v in sorted(dim_dist.items())},
        'scheme_multiplicity_per_S_distribution': {str(k): int(v) for k, v in sorted(mult_dist.items())},
        'canonical_hash_count_one_step': len(canon_to_members),
        'observed_pool_S_orbit_count': len(observed_orbits),
        'observed_pool_S_orbit_size_distribution': {str(k): int(v) for k, v in sorted(sampled_orbit_size_dist.items())},
        'records': records,
        'observed_orbits': orbit_records,
        'elapsed_sec': time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')

    if args.save_npz:
        maxdim = max((len(b) for b in distinct), default=0)
        arr = np.zeros((len(distinct), maxdim, 2), dtype=np.uint64)
        # split 81-bit ints into low/high uint64 for exact reload.
        for i, b in enumerate(distinct):
            for j, x in enumerate(b):
                arr[i, j, 0] = int(x) & ((1 << 64) - 1)
                arr[i, j, 1] = int(x) >> 64
        args.save_npz.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(args.save_npz, S_basis_uint64=arr)

    print(json.dumps({
        'pool_schemes': int(pool.shape[0]),
        'q_terms': q,
        'stabilizer_size_preserving_V': len(stabs),
        'distinct_S_count': len(distinct),
        'dim_distribution': result['distinct_S_dim_distribution'],
        'multiplicity_distribution': result['scheme_multiplicity_per_S_distribution'],
        'observed_pool_S_orbit_count': len(observed_orbits),
        'observed_pool_S_orbit_size_distribution': result['observed_pool_S_orbit_size_distribution'],
        'elapsed_sec': result['elapsed_sec'],
    }, indent=2, sort_keys=True))
    print('wrote', args.out)


if __name__ == '__main__':
    main()
