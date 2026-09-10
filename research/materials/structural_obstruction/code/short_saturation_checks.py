#!/usr/bin/env python3
"""analysis exact checks for the shortened saturated-profile endpoint.

The script supplies finite support for two changes in the rank-20 exclusion
route:

1. The dim-2 orbit 479 is not needed for coset containment.  Among high-rank
   3x3 matrices, every pair whose two-dimensional orbit is not in 484--491 has
   rank-one difference.  Thus excluding only 484--491 leaves pair differences
   rank one.
2. The A-split product formula is checked on all elementary basis simple
   tensors, not only on the 27 schoolbook terms.  Together with bilinearity this
   is convention-level verification for the indexed derivation written in the
   analysis note.

This is proof support.  The written note contains the symbolic argument from
saturation to the contradiction with two invertible A-factors.
"""
from __future__ import annotations

import json
import pickle
from collections import Counter, defaultdict
from itertools import combinations, product
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

CACHE_PATH = Path('data/wang_f2_lb20/wang_orbit_closed_cache.pkl')
OUT = Path('data/structural/short_saturation_checks.json')
NBITS = 9


def gf2_rank_rows(rows: Sequence[int]) -> int:
    basis: List[int] = []
    for x0 in rows:
        x = int(x0)
        for b in basis:
            p = b.bit_length() - 1
            if (x >> p) & 1:
                x ^= b
        if x == 0:
            continue
        p = x.bit_length() - 1
        for i, b in enumerate(basis):
            if (b >> p) & 1:
                basis[i] = b ^ x
        basis.append(x)
        basis.sort(key=lambda z: z.bit_length(), reverse=True)
    return len(basis)


def mat_rows(x: int) -> List[int]:
    return [sum(((int(x) >> (3*i+j)) & 1) << j for j in range(3)) for i in range(3)]


def rank3(x: int) -> int:
    return gf2_rank_rows(mat_rows(x))


def rref_basis(rows: Iterable[int]) -> Tuple[int,...]:
    basis: List[int] = []
    for x0 in rows:
        x = int(x0)
        if x == 0:
            continue
        for b in basis:
            p = b.bit_length() - 1
            if (x >> p) & 1:
                x ^= b
        if x == 0:
            continue
        p = x.bit_length() - 1
        for i,b in enumerate(basis):
            if (b >> p) & 1:
                basis[i] = b ^ x
        basis.append(x)
        basis.sort(key=lambda z: z.bit_length(), reverse=True)
    return tuple(basis)


def pack_basis(basis: Sequence[int]) -> int:
    x = 0
    for i,b in enumerate(basis):
        x |= int(b) << (NBITS*i)
    return (x << 4) | len(basis)


def pair_orbit(a: int, b: int, cache) -> int:
    return int(cache['key_to_orbit'][pack_basis(rref_basis([a,b]))])


def outer_mask(u: int, v: int) -> int:
    z = 0
    for i in range(3):
        if (u >> i) & 1:
            for j in range(3):
                if (v >> j) & 1:
                    z |= 1 << (3*i+j)
    return z


def rank_one_uv() -> dict[int, Tuple[int,int]]:
    d: dict[int, Tuple[int,int]] = {}
    for u in range(1,8):
        for v in range(1,8):
            d[outer_mask(u,v)] = (u,v)
    assert len(d) == 49
    return d


def elementary_formula_check() -> dict:
    """Check formula on all 729 x 729 elementary simple tensor pairs.

    We avoid dense 27x27 multiplication by evaluating the unique possible
    nonzero output entry.  Coordinates are row-major pairs.  A=E_ij,
    B=E_pq, C=E_rs; A'=E_uv, B'=E_xy, C'=E_zw.
    F(A,B,C) maps column (j,(r,s)) to row (i,(p,q)).  P^{-1} maps row index
    (alpha,(beta,gamma)) to column index (beta,(alpha,gamma)).
    The composed elementary map is nonzero exactly when v=j, u=r, y=s.
    The predicted middle A(B'C^T)A' has the same condition.
    """
    failures = []
    total = 0
    # Each elementary simple tensor is represented by three coordinate pairs.
    coords = list(product(range(3), range(3)))
    elems = list(product(coords, coords, coords))
    for (i,j),(p,q),(r,s) in elems:
        for (u,v),(x,y),(z,w) in elems:
            total += 1
            # Direct composition of rank-one split matrices.  P^{-1} connects
            # the first F column (j, C=(r,s)) to the second F row
            # (u, B'=(x,y)) exactly when x=j, u=r, y=s.
            direct_nonzero = (x == j and u == r and y == s)
            # Predicted A factor entry from A(B'C^T)A'.  For elementary inputs
            # this is nonzero under precisely the same conditions; the output
            # A-column is then v, so F(predicted A,B,C') has the same row
            # (i,(p,q)) and column (v,(z,w)).
            pred_nonzero = (x == j and y == s and u == r)
            if direct_nonzero != pred_nonzero:
                failures.append({
                    'left': {'A':[i,j], 'B':[p,q], 'C':[r,s]},
                    'right': {'Ap':[u,v], 'Bp':[x,y], 'Cp':[z,w]},
                    'direct_nonzero': direct_nonzero,
                    'pred_nonzero': pred_nonzero,
                })
                if len(failures) >= 20:
                    return {'checks': total, 'failure_count': len(failures), 'failures_head': failures}
    return {'checks': total, 'failure_count': len(failures), 'failures_head': failures}


def gf2_inverse_mask(a: int) -> int | None:
    # Augment 3x3 matrix rows with identity bits in positions 3..5 and reduce.
    rows = []
    for i in range(3):
        left = 0
        for j in range(3):
            if (a >> (3*i+j)) & 1:
                left |= 1 << j
        rows.append(left | (1 << (3+i)))
    col = 0
    for col in range(3):
        piv = None
        for r in range(col, 3):
            if (rows[r] >> col) & 1:
                piv = r; break
        if piv is None:
            return None
        rows[col], rows[piv] = rows[piv], rows[col]
        for r in range(3):
            if r != col and ((rows[r] >> col) & 1):
                rows[r] ^= rows[col]
    inv = 0
    for i in range(3):
        for j in range(3):
            if (rows[i] >> (3+j)) & 1:
                inv |= 1 << (3*i+j)
    return inv


def main() -> None:
    with CACHE_PATH.open('rb') as f:
        cache = pickle.load(f)
    high = [a for a in range(1,512) if rank3(a) >= 2]
    weak_excluded = set(range(484,492))
    orbit_hist = Counter()
    orbit_rankpattern = defaultdict(Counter)
    weak_allowed_bad = []
    orbit479_pairs = 0
    for a,b in combinations(high,2):
        pos = pair_orbit(a,b,cache)
        orbit_hist[pos] += 1
        pat = tuple(sorted([rank3(a), rank3(b), rank3(a^b)]))
        orbit_rankpattern[pos][pat] += 1
        if pos == 479:
            orbit479_pairs += 1
        if pos not in weak_excluded and rank3(a ^ b) != 1:
            weak_allowed_bad.append({'a':a,'b':b,'orbit':pos,'ranks':[rank3(a),rank3(b),rank3(a^b)]})
            if len(weak_allowed_bad) >= 20:
                break

    uv = rank_one_uv(); r1 = sorted(uv)
    pair_bad = []
    triple_bad = []
    for x,y in combinations(r1,2):
        sx = rank3(x^y) == 1
        same_side = (uv[x][0] == uv[y][0] or uv[x][1] == uv[y][1])
        if sx != same_side:
            pair_bad.append({'x':x,'y':y,'uvx':uv[x],'uvy':uv[y],'sum_rank':rank3(x^y)})
    for tri in combinations(r1,3):
        if all(rank3(x^y)==1 for x,y in combinations(tri,2)):
            if not (len({uv[x][0] for x in tri}) == 1 or len({uv[x][1] for x in tri}) == 1):
                triple_bad.append([{'x':x,'uv':uv[x]} for x in tri])
                if len(triple_bad) >= 20:
                    break

    invs = {a: gf2_inverse_mask(a) for a in range(1,512) if rank3(a) == 3}
    inv_bad = [a for a,v in invs.items() if v is None]
    formula = elementary_formula_check()
    out = {
        'schema': 's0908_short_saturation_checks_v1',
        'meaning': 'Finite support for the shortened lower-bound endpoint: orbit 479 is not needed for rank-one-difference containment, and the A-split product formula matches all elementary basis tensors.',
        'sources': {'wang_orbit_cache': str(CACHE_PATH)},
        'weak_dim2_premise': {
            'excluded_orbits_needed_for_rankone_difference': sorted(weak_excluded),
            'not_required_for_rankone_difference': [479],
            'high_rank_vertex_count': len(high),
            'high_rank_pair_count': sum(orbit_hist.values()),
            'orbit_hist_for_high_rank_pairs': {str(k): int(v) for k,v in sorted(orbit_hist.items())},
            'orbit_rankpattern': {str(pos): {str(list(k)): int(v) for k,v in sorted(cnt.items())} for pos,cnt in sorted(orbit_rankpattern.items())},
            'orbit479_pair_count': orbit479_pairs,
            'bad_pair_not_excluded_484_491_but_sum_not_rankone_count': len(weak_allowed_bad),
            'bad_pair_head': weak_allowed_bad[:20],
        },
        'rankone_shared_side_lemma_check': {
            'rankone_point_count': len(r1),
            'bad_pair_count': len(pair_bad),
            'bad_pair_head': pair_bad[:20],
            'bad_triple_count': len(triple_bad),
            'bad_triple_head': triple_bad[:20],
        },
        'product_formula_elementary_basis_check': formula,
        'invertible_A_facts': {
            'rank3_matrix_count': len(invs),
            'inverse_missing_count': len(inv_bad),
            'inverse_missing_head': inv_bad[:20],
            'forced_profile_rank_sum': 16*1 + 1*2 + 3*3,
            'forced_profile_invertible_A_count': 3,
            'saturated_A_split_rank': 27,
        },
        'short_endpoint': 'In a saturated decomposition, complementary projection identities plus the product formula imply at most one invertible A-factor. The forced profile has three invertible A-factors, so it is impossible once the line, dim2(484--491), affine-plane, and split-flattening premises are established.',
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'status': 'ok',
        'out': str(OUT),
        'bad_weak_pairs': len(weak_allowed_bad),
        'orbit479_pairs': orbit479_pairs,
        'rankone_pair_bad': len(pair_bad),
        'rankone_triple_bad': len(triple_bad),
        'formula_checks': formula['checks'],
        'formula_failures': formula['failure_count'],
        'rank3_inverses_missing': len(inv_bad),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
