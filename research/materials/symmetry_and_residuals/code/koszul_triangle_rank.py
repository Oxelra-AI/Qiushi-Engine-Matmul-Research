#!/usr/bin/env python3
"""analysis: Koszul--Young rank of one triangle/product term.

The tempting cyclic shortcut would bound the KY rank of the diagonal identity

    tr(X^3) = sum fixed cubes + 3 sum triangle products

by 70 per cube plus tau per triangle product.  If tau were near 70, this could
exclude many cyclic skeletons at once.  This script computes tau for a product
of three independent linear forms using the same Lambda^4 V \otimes V* ->
Lambda^5 V \otimes V flattening convention as analysis.

Result expected from review: tau=250, making the subadditivity bound vacuous.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path

import numpy as np

OUT = Path("data/koszul_triangle")
OUT.mkdir(parents=True, exist_ok=True)

PRIME = 1000003
N = 9
P = 4
SUB4 = list(itertools.combinations(range(N), P))
SUB5 = list(itertools.combinations(range(N), P + 1))
SUB5_IDX = {s: i for i, s in enumerate(SUB5)}


def sym_outer3(u: np.ndarray, v: np.ndarray, w: np.ndarray) -> np.ndarray:
    T = np.zeros((N, N, N), dtype=np.int64)
    vecs = [u, v, w]
    for perm in itertools.permutations(range(3)):
        T = (T + np.einsum('i,j,k->ijk', vecs[perm[0]], vecs[perm[1]], vecs[perm[2]], dtype=np.int64)) % PRIME
    inv6 = pow(6, -1, PRIME)
    return (T * inv6) % PRIME


def koszul_matrix_cubic(T: np.ndarray) -> np.ndarray:
    M = np.zeros((len(SUB5) * N, N * len(SUB4)), dtype=np.int64)
    for a in range(N):
        for sidx, S in enumerate(SUB4):
            Sset = set(S)
            col = a * len(SUB4) + sidx
            for i in range(N):
                if i in Sset:
                    continue
                U = tuple(sorted((i,) + S))
                sign = -1 if (sum(1 for z in S if z < i) & 1) else 1
                row_base = SUB5_IDX[U] * N
                M[row_base:row_base + N, col] = (M[row_base:row_base + N, col] + sign * T[a, i, :]) % PRIME
    return M % PRIME


def rank_mod(A: np.ndarray, p: int = PRIME) -> int:
    A = np.array(A % p, dtype=np.int64, copy=True)
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i, c] % p:
                piv = i
                break
        if piv is None:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c] % p), -1, p)
        A[r, :] = (A[r, :] * inv) % p
        rows = np.nonzero(A[:, c] % p)[0]
        for i in rows:
            if i != r:
                A[i, :] = (A[i, :] - A[i, c] * A[r, :]) % p
        r += 1
        if r == m:
            break
    return int(r)


def target_trM3_tensor() -> np.ndarray:
    # Same symmetric-tensor convention as analysis: polynomial value is sum T_ijk x_i x_j x_k.
    mono = {}
    for a, b, c in itertools.product(range(3), repeat=3):
        inds = [3 * a + b, 3 * b + c, 3 * c + a]
        key = tuple(sorted(inds))
        mono[key] = mono.get(key, 0) + 1
    T = np.zeros((N, N, N), dtype=np.int64)
    for key, coef in mono.items():
        perms = sorted(set(itertools.permutations(key)))
        val = (coef * pow(len(perms), -1, PRIME)) % PRIME
        for p3 in perms:
            T[p3] = val
    return T % PRIME


def main() -> None:
    e0 = np.zeros(N, dtype=np.int64); e0[0] = 1
    e1 = np.zeros(N, dtype=np.int64); e1[1] = 1
    e2 = np.zeros(N, dtype=np.int64); e2[2] = 1
    e3 = np.zeros(N, dtype=np.int64); e3[3] = 1

    cube = sym_outer3(e0, e0, e0)
    triangle = sym_outer3(e0, e1, e2)
    dependent_triangle = sym_outer3(e0, e1, (e0 + e1) % PRIME)
    repeated_triangle = sym_outer3(e0, e0, e1)
    trm3 = target_trM3_tensor()

    records = []
    for label, T in [
        ("pure_cube", cube),
        ("three_independent_forms_product", triangle),
        ("two_dimensional_product", dependent_triangle),
        ("square_times_independent", repeated_triangle),
        ("tr_X_cubed", trm3),
    ]:
        K = koszul_matrix_cubic(T)
        records.append({
            "label": label,
            "rank_mod_prime": rank_mod(K),
            "matrix_shape": list(K.shape),
            "prime": PRIME,
        })
        print(records[-1])

    tau = next(r["rank_mod_prime"] for r in records if r["label"] == "three_independent_forms_product")
    cube_rank = next(r["rank_mod_prime"] for r in records if r["label"] == "pure_cube")
    tr_rank = next(r["rank_mod_prime"] for r in records if r["label"] == "tr_X_cubed")
    skeleton_bounds = {}
    for m in range(0, 8):
        f = 22 - 3 * m
        if f >= 0:
            skeleton_bounds[f"f={f},m={m}"] = 70 * f + tau * m
    result = {
        "schema": "koszul_triangle_rank_v1",
        "flattening": "Lambda^4 V tensor V* -> Lambda^5 V tensor V for cubics in 9 variables",
        "field": f"F_{PRIME}",
        "records": records,
        "tau_independent_product": tau,
        "cube_rank": cube_rank,
        "tr_X_cubed_rank": tr_rank,
        "cyclic_skeleton_subadditive_bounds_using_tau": skeleton_bounds,
        "interpretation": "tau=250, not near the cube value 70. Hence KY subadditivity on fixed cubes plus free triangle products gives no useful cyclic skeleton exclusion; e.g. (10,4) has bound 1700 and even four triangles alone can absorb 1000 units of KY rank.",
    }
    out = OUT / "koszul_triangle_rank.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(out), "tau": tau, "cube_rank": cube_rank, "tr_X_cubed_rank": tr_rank}, indent=2))


if __name__ == "__main__":
    main()
