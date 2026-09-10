#!/usr/bin/env python3
"""analysis: exact basic checks for the cyclic outer De Groote stratum.

This script does not search for a rank-22 algorithm.  It records the linear
algebra behind the proposed next attack: the cyclic factor rotation fixes a
249-dimensional subspace of the 9^3-dimensional ambient tensor space; the
projectively fixed rank-one locus is the Veronese/Sym^3 locus whose linear span
has dimension binom(9+3-1,3)=165; T_<3,3,3> is cyclic-invariant but not fully
symmetric, so an all-fixed cyclic decomposition is impossible.
"""
from __future__ import annotations

import json
from pathlib import Path
from math import comb

import sympy as sp

N = 9


def idx(a: int, b: int) -> int:
    return 3 * a + b


def flat(i: int, j: int, k: int) -> int:
    return (i * N + j) * N + k


def main() -> None:
    # Cyclic permutation rho(i,j,k)=(j,k,i) on the ambient basis.
    seen = set()
    cyclic_orbits = []
    for i in range(N):
        for j in range(N):
            for k in range(N):
                t = (i, j, k)
                if t in seen:
                    continue
                orb = []
                x = t
                while x not in orb:
                    orb.append(x)
                    seen.add(x)
                    x = (x[1], x[2], x[0])
                cyclic_orbits.append(tuple(orb))
    orbit_len_hist = {}
    for o in cyclic_orbits:
        orbit_len_hist[len(o)] = orbit_len_hist.get(len(o), 0) + 1
    cyclic_fixed_dim = len(cyclic_orbits)

    # Span of projectively fixed rank-one terms for pure cyclic rotation:
    # tensors u\otimes u\otimes u, i.e. Sym^3(K^9).
    sym3_dim = comb(N + 3 - 1, 3)

    # Build T_<3,3,3> as a vector in U\otimes V\otimes W, with
    # U=(a,b), V=(b,c), W=(c,a).  The cyclic factor rotation sends
    # U->V->W->U and maps (ab,bc,ca) to (bc,ca,ab), preserving the support sum.
    T = [0] * (N ** 3)
    for a in range(3):
        for b in range(3):
            for c in range(3):
                i = idx(a, b)
                j = idx(b, c)
                k = idx(c, a)
                T[flat(i, j, k)] = 1

    def cyclic_perm_vec(vec):
        out = [0] * len(vec)
        for i in range(N):
            for j in range(N):
                for k in range(N):
                    out[flat(j, k, i)] = vec[flat(i, j, k)]
        return out

    def swap12_vec(vec):
        out = [0] * len(vec)
        for i in range(N):
            for j in range(N):
                for k in range(N):
                    out[flat(j, i, k)] = vec[flat(i, j, k)]
        return out

    cyclic_invariant = cyclic_perm_vec(T) == T
    swap12_invariant = swap12_vec(T) == T
    asym_support = []
    S = swap12_vec(T)
    for n, (x, y) in enumerate(zip(T, S)):
        if x != y:
            i = n // (N * N)
            rem = n % (N * N)
            j = rem // N
            k = rem % N
            asym_support.append((i, j, k, x, y))
            if len(asym_support) >= 10:
                break

    # Symmetric subspace dimension can also be counted as S3-orbits on [9]^3.
    seen = set()
    s3_orbits = []
    for i in range(N):
        for j in range(N):
            for k in range(N):
                t = (i, j, k)
                if t in seen:
                    continue
                orb = sorted({
                    (i, j, k), (i, k, j), (j, i, k), (j, k, i), (k, i, j), (k, j, i)
                })
                for x in orb:
                    seen.add(x)
                s3_orbits.append(tuple(orb))
    assert len(s3_orbits) == sym3_dim

    skeletons_rank22 = []
    for f in range(23):
        if (22 - f) >= 0 and (22 - f) % 3 == 0:
            m = (22 - f) // 3
            raw_vars = 9 * f + 27 * m
            skeletons_rank22.append({'fixed_terms': f, 'three_orbits': m, 'raw_vector_variables': raw_vars})
    skeletons_rank23 = []
    for f in range(24):
        if (23 - f) >= 0 and (23 - f) % 3 == 0:
            m = (23 - f) // 3
            raw_vars = 9 * f + 27 * m
            skeletons_rank23.append({'fixed_terms': f, 'three_orbits': m, 'raw_vector_variables': raw_vars})

    result = {
        'purpose': 'basic exact linear algebra for cyclic outer-symmetry attack',
        'ambient_dim': N ** 3,
        'cyclic_factor_rotation': 'rho(i,j,k)=(j,k,i)',
        'cyclic_orbit_length_histogram': orbit_len_hist,
        'cyclic_fixed_subspace_dim': cyclic_fixed_dim,
        'formula_check_cyclic_dim': '(9^3 + 2*9)/3 = 249',
        'projectively_fixed_rank_one_span': 'span{u^⊗3}=Sym^3(K^9)',
        'projectively_fixed_rank_one_span_dim': sym3_dim,
        's3_symmetric_subspace_dim': len(s3_orbits),
        'T333_cyclic_invariant': cyclic_invariant,
        'T333_invariant_under_swap_first_two_factors': swap12_invariant,
        'first_swap_asymmetry_entries': asym_support,
        'all_terms_fixed_by_cyclic_rotation_impossible_reason': 'all projectively fixed terms lie in Sym^3(K^9), but T333 is not S3-symmetric (swap first two factors changes it)',
        'rank22_cyclic_skeletons_f_plus_3m': skeletons_rank22,
        'rank23_cyclic_skeletons_f_plus_3m': skeletons_rank23,
        'raw_variable_count_rank22_each_skeleton': 198,
        'cyclic_invariant_equation_count': cyclic_fixed_dim,
        'interpretation': 'Rank-22 cyclic-invariant ansatz has 198 raw vector variables against 249 cyclic-invariant linear coordinates; rank-23 has 207 variables and is known to contain structured algorithms, so dimension count alone neither excludes nor constructs rank 22.',
    }
    out = Path('data/outer_symmetry')
    out.mkdir(parents=True, exist_ok=True)
    (out / 'cyclic_outer_basic_checks.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
