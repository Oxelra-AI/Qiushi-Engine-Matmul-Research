#!/usr/bin/env python3
r"""
analysis: exact semisimple repeated-difference arrangement and block-rank test.

This upgrades the analysis small-box pilot.  A semisimple termwise-aligned
configuration is governed by eigenvalues p_a, q_b, r_c and weights

    alpha(a,b,c) = p_a - q_b,
    beta(a,b,c)  = q_b - r_c,
    gamma        = -alpha-beta = r_c - p_a.

A rank-one summand aligned with a noncentral stabilizer element must lie in a
single weight block.  Therefore a rank-22 aligned decomposition would imply
that the sum of the tensor ranks of all coordinate blocks of T333 for one of
these weight partitions is at most 22.

This script enumerates the intersection lattice of all equal-weight hyperplanes
for the 27 triples (a,b,c), using exact rational row-reduction.  For each flat it
computes the generic weight partition, discards central scalar flats, and
computes a strengthened lower bound for the sum of block ranks.  The extra
input beyond flattening is a finite table of small matrix-multiplication block
rank lower bounds needed by this classification:

    R(M_{<3,3,2>}) >= 14,

including cyclic permutations of the three tensor factors.  For the other low
blocks, the script uses only the internally checked exterior-flattening lower
bounds R(M_{<3,2,2>}) >= 8 and R(M_{<2,2,2>}) >= 6, which already suffice.
Thus the only zero-margin external small-format input is M_{<3,3,2>} >= 14;
the script checks that, with this input and no unsupported universal formula,
every noncentral semisimple weight pattern has block-rank sum at least 23.

The enumeration itself is exact over characteristic zero: row spaces are over Q.
"""
from __future__ import annotations

import argparse
import itertools
import json
import time
from collections import Counter, defaultdict, deque
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

Triple = Tuple[int, int, int]
Vec = Tuple[Fraction, ...]
Key = Tuple[Vec, ...]

TRIPLES: List[Triple] = [(a, b, c) for a in range(3) for b in range(3) for c in range(3)]
TRIPLE_INDEX: Dict[Triple, int] = {t: i for i, t in enumerate(TRIPLES)}


def wt_forms(t: Triple) -> Tuple[Tuple[int, ...], Tuple[int, ...]]:
    """Return integer coefficient vectors for alpha and beta in variables
    (p0,p1,p2,q0,q1,q2,r0,r1,r2)."""
    a, b, c = t
    alpha = [0] * 9
    beta = [0] * 9
    alpha[a] += 1
    alpha[3 + b] -= 1
    beta[3 + b] += 1
    beta[6 + c] -= 1
    return tuple(alpha), tuple(beta)

FORMS = [wt_forms(t) for t in TRIPLES]

# Pair-equality equations: alpha_i-alpha_j=0 and beta_i-beta_j=0.
PAIR_EQS: List[Tuple[int, int, Tuple[int, ...], Tuple[int, ...]]] = []
for i in range(27):
    for j in range(i + 1, 27):
        da = tuple(FORMS[i][0][k] - FORMS[j][0][k] for k in range(9))
        db = tuple(FORMS[i][1][k] - FORMS[j][1][k] for k in range(9))
        PAIR_EQS.append((i, j, da, db))

# Equations defining the scalar-central subspace: each of P,Q,R is scalar.
CENTRAL_EQS = [
    (1, -1, 0, 0, 0, 0, 0, 0, 0),
    (1, 0, -1, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 1, -1, 0, 0, 0, 0),
    (0, 0, 0, 1, 0, -1, 0, 0, 0),
    (0, 0, 0, 0, 0, 0, 1, -1, 0),
    (0, 0, 0, 0, 0, 0, 1, 0, -1),
]


def to_frac_row(row: Sequence[int | Fraction]) -> Vec:
    return tuple(Fraction(x) for x in row)


def rref(rows: Iterable[Sequence[int | Fraction]]) -> Key:
    A = [list(to_frac_row(row)) for row in rows if any(Fraction(x) != 0 for x in row)]
    if not A:
        return tuple()
    m = len(A)
    n = len(A[0])
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        if piv != r:
            A[r], A[piv] = A[piv], A[r]
        inv = 1 / A[r][c]
        A[r] = [x * inv for x in A[r]]
        for i in range(m):
            if i == r:
                continue
            fac = A[i][c]
            if fac:
                A[i] = [A[i][j] - fac * A[r][j] for j in range(n)]
        r += 1
        if r == m:
            break
    # Remove zero rows and keep canonical pivot order.
    nz = [tuple(row) for row in A if any(x != 0 for x in row)]
    return tuple(nz)


def pivots(key: Key) -> List[int]:
    out = []
    for row in key:
        for i, x in enumerate(row):
            if x != 0:
                out.append(i)
                break
    return out


def reduce_by_rref(vec: Sequence[int | Fraction], key: Key) -> Vec:
    v = list(to_frac_row(vec))
    for row in key:
        pc = next((i for i, x in enumerate(row) if x != 0), None)
        if pc is None:
            continue
        fac = v[pc]
        if fac:
            v = [v[j] - fac * row[j] for j in range(len(v))]
    return tuple(v)


def in_rowspace(vec: Sequence[int | Fraction], key: Key) -> bool:
    return all(x == 0 for x in reduce_by_rref(vec, key))


def add_equations(key: Key, *rows: Sequence[int | Fraction]) -> Key:
    return rref(list(key) + [row for row in rows if any(Fraction(x) != 0 for x in row)])


def generic_partition(key: Key) -> Tuple[Tuple[Triple, ...], ...]:
    """Generic partition of triples on the flat defined by key.

    Two triples are in the same block iff equality of their alpha and beta
    weights is forced by the flat, i.e. both difference equations lie in the
    rowspace.
    """
    parent = list(range(27))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(i: int, j: int) -> None:
        ri, rj = find(i), find(j)
        if ri != rj:
            if ri > rj:
                ri, rj = rj, ri
            parent[rj] = ri

    for i, j, da, db in PAIR_EQS:
        if in_rowspace(da, key) and in_rowspace(db, key):
            union(i, j)
    blocks: Dict[int, List[Triple]] = defaultdict(list)
    for i, t in enumerate(TRIPLES):
        blocks[find(i)].append(t)
    return tuple(sorted(tuple(v) for v in blocks.values()))


def flat_has_noncentral_points(key: Key) -> bool:
    # The solution subspace is contained in the scalar-central subspace iff all
    # central equations vanish on it, i.e. lie in the flat's rowspace.
    return not all(in_rowspace(eq, key) for eq in CENTRAL_EQS)


def rank_mod(M: np.ndarray, p: int = 1000003) -> int:
    A = np.array(M % p, dtype=np.int64, copy=True)
    m, n = A.shape
    r = 0
    for c in range(n):
        if r >= m:
            break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + int(nz[0])
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        fac = A[:, c].copy()
        fac[r] = 0
        rows = np.nonzero(fac)[0]
        if len(rows):
            A[rows] = (A[rows] - fac[rows, None] * A[r]) % p
        r += 1
    return r


def flattening_ranks(support: Sequence[Triple]) -> Tuple[int, int, int]:
    Uids = sorted(set((a, b) for a, b, c in support))
    Vids = sorted(set((b, c) for a, b, c in support))
    Wids = sorted(set((a, c) for a, b, c in support))
    ui = {x: i for i, x in enumerate(Uids)}
    vi = {x: i for i, x in enumerate(Vids)}
    wi = {x: i for i, x in enumerate(Wids)}
    MU = np.zeros((len(Uids), len(Vids) * len(Wids)), dtype=np.int64)
    MV = np.zeros((len(Vids), len(Uids) * len(Wids)), dtype=np.int64)
    MW = np.zeros((len(Wids), len(Uids) * len(Vids)), dtype=np.int64)
    for a, b, c in support:
        u = ui[(a, b)]
        v = vi[(b, c)]
        w = wi[(a, c)]
        MU[u, v * len(Wids) + w] = 1
        MV[v, u * len(Wids) + w] = 1
        MW[w, u * len(Vids) + v] = 1
    return rank_mod(MU), rank_mod(MV), rank_mod(MW)


def is_complete_rectangular(support: Sequence[Triple]) -> Tuple[bool, Tuple[int, int, int], List[List[int]]]:
    A = sorted(set(a for a, b, c in support))
    B = sorted(set(b for a, b, c in support))
    C = sorted(set(c for a, b, c in support))
    prod = {(a, b, c) for a in A for b in B for c in C}
    supp = set(support)
    return supp == prod, (len(A), len(B), len(C)), [A, B, C]


SMALL_FORMAT_BLOCK_LB = {
    # These values are external proof inputs, not proved by this script.
    # Tuples are sorted because cyclic permutation of tensor factors preserves tensor rank.
    (1, 1, 1): 1,
    (1, 1, 2): 2,
    (1, 1, 3): 3,
    (1, 2, 2): 4,
    (1, 2, 3): 6,
    (1, 3, 3): 9,
    # The next two values are not external assumptions here: analysis's
    # exterior-flattening check gives at least 6 for (2,2,2) and at least 8 for
    # cyclic permutations of (3,2,2); these weaker values are enough.
    (2, 2, 2): 6,
    (2, 2, 3): 8,
    # Zero-margin external input, supported by Blaser's small-format rank work;
    # Landsberg 2012 line 37 quotes the needed rectangular lower bound for
    # M_{<n,n,m>}, giving 14 at (n,m)=(3,2).  Original theorem/proof should be
    # inspected before final publication-level use.
    (2, 3, 3): 14,
}


def small_rect_lb(m: int, n: int, p: int) -> int | None:
    return SMALL_FORMAT_BLOCK_LB.get(tuple(sorted((m, n, p))))


def rectangular_subtensor_lb(support: Sequence[Triple]) -> Tuple[int, Tuple[int, int, int] | None]:
    supp = set(support)
    best = 0
    best_dims = None
    for A_mask in range(1, 1 << 3):
        A = [i for i in range(3) if (A_mask >> i) & 1]
        for B_mask in range(1, 1 << 3):
            B = [i for i in range(3) if (B_mask >> i) & 1]
            for C_mask in range(1, 1 << 3):
                C = [i for i in range(3) if (C_mask >> i) & 1]
                prod = {(a, b, c) for a in A for b in B for c in C}
                if prod and prod.issubset(supp):
                    val = small_rect_lb(len(A), len(B), len(C))
                    if val is not None and val > best:
                        best = val
                        best_dims = (len(A), len(B), len(C))
    return best, best_dims


def block_info(block: Sequence[Triple]) -> Dict:
    support = list(block)
    Udim = len(set((a, b) for a, b, c in support))
    Vdim = len(set((b, c) for a, b, c in support))
    Wdim = len(set((a, c) for a, b, c in support))
    fr = flattening_ranks(support)
    flat_lb = max(fr)
    is_rect, rect_dims, rect_sets = is_complete_rectangular(support)
    rect_lb = small_rect_lb(*rect_dims) if is_rect else None
    sub_lb, sub_dims = rectangular_subtensor_lb(support)
    lb_candidates = [('flattening', flat_lb)]
    if rect_lb is not None:
        lb_candidates.append(('small-format rectangular MM rank table', rect_lb))
    if sub_lb:
        lb_candidates.append(('small-format rectangular MM rank table subtensor', sub_lb))
    source, lb = max(lb_candidates, key=lambda x: x[1])
    return {
        'support': [list(t) for t in sorted(support)],
        'support_size': len(support),
        'dims': [Udim, Vdim, Wdim],
        'flattening_ranks': list(fr),
        'flattening_lb': flat_lb,
        'is_complete_rectangular_mm': is_rect,
        'rectangular_index_dims': list(rect_dims),
        'rectangular_index_sets': rect_sets,
        'small_rectangular_mm_lb': rect_lb,
        'best_rectangular_subtensor_lb': sub_lb,
        'best_rectangular_subtensor_dims': list(sub_dims) if sub_dims else None,
        'certified_lb': lb,
        'certified_lb_source': source,
    }


def partition_signature(partition: Tuple[Tuple[Triple, ...], ...]) -> Tuple:
    infos = [block_info(b) for b in partition]
    sig = []
    for inf in infos:
        sig.append((
            inf['support_size'],
            tuple(inf['dims']),
            tuple(inf['flattening_ranks']),
            inf['is_complete_rectangular_mm'],
            tuple(inf['rectangular_index_dims']),
            inf['small_rectangular_mm_lb'],
            inf['certified_lb'],
        ))
    return tuple(sorted(sig, reverse=True))


def analyze_partition(partition: Tuple[Tuple[Triple, ...], ...]) -> Dict:
    infos = [block_info(b) for b in partition]
    infos.sort(key=lambda x: (-x['support_size'], -x['certified_lb'], x['support']))
    flat_sum = sum(i['flattening_lb'] for i in infos)
    cert_sum = sum(i['certified_lb'] for i in infos)
    return {
        'num_blocks': len(partition),
        'flattening_lb_sum': flat_sum,
        'certified_block_lb_sum': cert_sum,
        'blocks': infos,
    }


def enumerate_flats(max_flats: int | None = None) -> Dict:
    t0 = time.time()
    zero: Key = tuple()
    seen: Dict[Key, Tuple[Tuple[Triple, ...], ...]] = {}
    q: deque[Key] = deque([zero])
    queued = {zero}
    rank_hist = Counter()
    max_queue = 1
    while q:
        key = q.popleft()
        queued.discard(key)
        if key in seen:
            continue
        part = generic_partition(key)
        seen[key] = part
        rank_hist[len(key)] += 1
        # impose equality of one pair of current generic blocks; adding pairs
        # inside a block would not change this flat.
        block_id: Dict[int, int] = {}
        for bi, block in enumerate(part):
            for t in block:
                block_id[TRIPLE_INDEX[t]] = bi
        for i, j, da, db in PAIR_EQS:
            if block_id[i] == block_id[j]:
                continue
            nk = add_equations(key, da, db)
            if nk not in seen and nk not in queued:
                q.append(nk)
                queued.add(nk)
        max_queue = max(max_queue, len(q))
        if max_flats is not None and len(seen) >= max_flats:
            break
    return {
        'flats': seen,
        'rank_hist': rank_hist,
        'elapsed_sec': time.time() - t0,
        'max_queue': max_queue,
        'truncated': max_flats is not None and len(seen) >= max_flats,
    }


def fraction_to_str(x: Fraction) -> str:
    if x.denominator == 1:
        return str(x.numerator)
    return f'{x.numerator}/{x.denominator}'


def key_to_json(key: Key) -> List[List[str]]:
    return [[fraction_to_str(x) for x in row] for row in key]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default='data/semisimple_arrangement/semisimple_arrangement_blockrank.json')
    ap.add_argument('--max-flats', type=int, default=None)
    ap.add_argument('--keep', type=int, default=100)
    args = ap.parse_args()

    enum = enumerate_flats(args.max_flats)
    flats: Dict[Key, Tuple[Tuple[Triple, ...], ...]] = enum['flats']

    sig_records: Dict[Tuple, Dict] = {}
    sig_counts = Counter()
    cert_hist = Counter()
    flat_hist = Counter()
    block_count_hist = Counter()
    noncentral_flat_count = 0
    central_flat_count = 0

    for key, part in flats.items():
        if not flat_has_noncentral_points(key):
            central_flat_count += 1
            continue
        noncentral_flat_count += 1
        rec = analyze_partition(part)
        sig = partition_signature(part)
        sig_counts[sig] += 1
        cert_hist[rec['certified_block_lb_sum']] += 1
        flat_hist[rec['flattening_lb_sum']] += 1
        block_count_hist[rec['num_blocks']] += 1
        if sig not in sig_records or (
            rec['certified_block_lb_sum'], rec['flattening_lb_sum'], rec['num_blocks']
        ) < (
            sig_records[sig]['certified_block_lb_sum'],
            sig_records[sig]['flattening_lb_sum'],
            sig_records[sig]['num_blocks'],
        ):
            sig_records[sig] = rec | {'example_flat_rank': len(key), 'example_flat_rref': key_to_json(key)}

    reps = sorted(sig_records.values(), key=lambda r: (r['certified_block_lb_sum'], r['flattening_lb_sum'], r['num_blocks']))
    hard_reps = [r for r in reps if r['flattening_lb_sum'] <= 22]
    low_cert = [r for r in reps if r['certified_block_lb_sum'] <= 22]

    result = {
        'purpose': 'Exact hyperplane-arrangement enumeration of semisimple repeated-difference termwise-aligned strata for T333, with strengthened block-rank lower bounds.',
        'field': 'Characteristic zero arrangement; block lower bounds use flattening plus an explicit finite table of small rectangular matrix-multiplication lower-bound inputs over the relevant coefficient field.',
        'external_small_format_block_lb_inputs': {str(k): v for k, v in sorted(SMALL_FORMAT_BLOCK_LB.items())},
        'external_input_status': 'The arrangement enumeration is exact. The final exclusion of semisimple aligned rank 22 depends only on independently citing or proving the zero-margin small-format input (2,3,3)->14; weaker values (2,2,2)->6 and (2,2,3)->8 are internally supported by analysis exterior-flattening checks and already suffice.',
        'triples_order': [list(t) for t in TRIPLES],
        'flat_count_total': len(flats),
        'flat_rank_histogram': {str(k): int(v) for k, v in sorted(enum['rank_hist'].items())},
        'central_only_flat_count': central_flat_count,
        'noncentral_flat_count': noncentral_flat_count,
        'distinct_noncentral_partition_signatures': len(sig_records),
        'noncentral_flattening_lb_histogram': {str(k): int(v) for k, v in sorted(flat_hist.items())},
        'noncentral_certified_lb_histogram': {str(k): int(v) for k, v in sorted(cert_hist.items())},
        'noncentral_block_count_histogram': {str(k): int(v) for k, v in sorted(block_count_hist.items())},
        'min_flattening_lb_sum': min(flat_hist) if flat_hist else None,
        'min_certified_block_lb_sum': min(cert_hist) if cert_hist else None,
        'hard_flattening_signature_count': len(hard_reps),
        'certified_le22_signature_count': len(low_cert),
        'hard_flattening_representatives': hard_reps[: args.keep],
        'lowest_certified_representatives': reps[: args.keep],
        'all_noncentral_patterns_excluded_for_rank22_by_certified_block_lbs': (min(cert_hist) >= 23 if cert_hist else False),
        'interpretation': (
            'Each noncentral semisimple termwise-aligned rank-r decomposition would split into the listed coordinate blocks; '
            'rank is at least the sum of the block ranks.  The exhaustive arrangement enumeration shows all possible repeated-difference equality patterns. '
            'If min_certified_block_lb_sum >= 23, the full-span noncentral semisimple aligned stratum cannot contain a rank-22 decomposition, subject to the named rectangular matrix multiplication lower-bound input.'
        ),
        'elapsed_sec': enum['elapsed_sec'],
        'max_queue': enum['max_queue'],
        'truncated': enum['truncated'],
    }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'exact flats={len(flats)} noncentral={noncentral_flat_count} central={central_flat_count} signatures={len(sig_records)}')
    print(f'flattening hist={dict(sorted(flat_hist.items()))}')
    print(f'certified hist={dict(sorted(cert_hist.items()))}')
    print(f'min certified={result["min_certified_block_lb_sum"]} excluded={result["all_noncentral_patterns_excluded_for_rank22_by_certified_block_lbs"]}')
    print(f'wrote {out}')


if __name__ == '__main__':
    main()
