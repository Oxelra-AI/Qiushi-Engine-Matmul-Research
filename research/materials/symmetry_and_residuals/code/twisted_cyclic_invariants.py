#!/usr/bin/env python3
"""analysis: first exact invariants for twisted order-3 cyclic classes.

This script follows the twisted fixed-locus model described in the analysis
review note.  For a diagonal order-3 class P and g=Ad(P), it studies

    C_P(X) = tr(X * g(X) * g^2(X))

and the alternating trilinear target obtained from

    F_P(X,Y,Z) = tr(X * g(Y) * g^2(Z)).

It records the quantities that controlled the untwisted cyclic results:
  * invariant-subspace dimension formula (729 + tr(g) + tr(g^2))/3;
  * traceless projected alternating trivector and its GL_8 stabilizer dimension;
  * rank of the trace-grading quadratic coefficient in C_P(X0+sI);
  * Koszul--Young rank of C_P, calibrated against the pure P=I case.

All rank computations are modular over primes p = 1 mod 3.  The diagonal
classes over an algebraically closed characteristic-zero field are represented
by eigenvalue multiplicities (3), (2,1), and (1,1,1); scalar lifts with
P^3 scalar have the same Ad(P) and hence the same values here.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import numpy as np

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "twisted_cyclic"
OUT.mkdir(parents=True, exist_ok=True)

N = 9
SLN = 8
P_KOSZUL = 4
SUB4 = list(itertools.combinations(range(N), P_KOSZUL))
SUB5 = list(itertools.combinations(range(N), P_KOSZUL + 1))
SUB5_IDX = {s: i for i, s in enumerate(SUB5)}
TRIP9 = list(itertools.combinations(range(N), 3))
TRIP8 = list(itertools.combinations(range(SLN), 3))
TRIP8_IDX = {t: i for i, t in enumerate(TRIP8)}

# sl_3 basis used in the analysis files:
# E01,E02,E10,E12,E20,E21,H0=E00-E11,H1=E11-E22.
SL3_BASIS_MATS: List[np.ndarray] = []
for (a, b) in [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]:
    M = np.zeros((3, 3), dtype=object)
    M[a, b] = 1
    SL3_BASIS_MATS.append(M)
H0 = np.zeros((3, 3), dtype=object); H0[0, 0] = 1; H0[1, 1] = -1
H1 = np.zeros((3, 3), dtype=object); H1[1, 1] = 1; H1[2, 2] = -1
SL3_BASIS_MATS.extend([H0, H1])

# Coordinate matrix B[gl_index, sl_index].
SL3_B = np.zeros((N, SLN), dtype=object)
for j, M in enumerate(SL3_BASIS_MATS):
    for a in range(3):
        for b in range(3):
            SL3_B[3 * a + b, j] = int(M[a, b])


def sort_sign(xs: Iterable[int]) -> int:
    xs = list(xs)
    inv = 0
    for i in range(len(xs)):
        for j in range(i + 1, len(xs)):
            if xs[i] > xs[j]:
                inv += 1
    return -1 if inv & 1 else 1


def find_zeta(p: int) -> int:
    for z in range(2, p):
        if (z * z + z + 1) % p == 0:
            return z
    raise RuntimeError(f"no primitive cubic root found mod {p}")


def idx(a: int, b: int) -> int:
    return 3 * a + b


def rank_mod(A: np.ndarray, p: int) -> int:
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


def nullity_mod(A: np.ndarray, p: int) -> int:
    return A.shape[1] - rank_mod(A, p)


def ad_weights(diag: Tuple[int, int, int], p: int) -> List[int]:
    inv = [pow(x % p, -1, p) for x in diag]
    return [(diag[a] * inv[b]) % p for a in range(3) for b in range(3)]


def ad_trace(diag: Tuple[int, int, int], power: int, p: int) -> int:
    ws = ad_weights(diag, p)
    return sum(pow(w, power, p) for w in ws) % p


def recognize_ad_trace(label: str) -> Tuple[int, int, int]:
    # Return characteristic-zero integer traces tr(Ad P), tr(Ad P^2), and the deprecated
    # scalar Burnside diagnostic (729+tr(g)+tr(g^2))/3.  analysis review and the
    # action-level selfcheck proved this is NOT the invariant dimension of the
    # actual order-3 cyclic action rho_P on M3^⊗3; that dimension is 249 for all
    # three classes.
    if label == "pure_I":
        return 9, 9, 249
    if label == "two_plus_one":
        return 3, 3, 245
    if label == "regular_three":
        return 0, 0, 243
    raise KeyError(label)


def F_coeff_ordered(diag: Tuple[int, int, int], p: int) -> Dict[Tuple[int, int, int], int]:
    """Ordered trilinear coefficients of tr(X g(Y) g^2(Z))."""
    inv = [pow(x % p, -1, p) for x in diag]
    diag2 = [(x * x) % p for x in diag]
    inv2 = [(x * x) % p for x in inv]
    coeffs: Dict[Tuple[int, int, int], int] = {}
    for a, b, c in itertools.product(range(3), repeat=3):
        i = idx(a, b)      # X_{a b}
        j = idx(b, c)      # Y_{b c}
        k = idx(c, a)      # Z_{c a}
        weight_y = (diag[b] * inv[c]) % p
        weight_z = (diag2[c] * inv2[a]) % p
        coeffs[(i, j, k)] = (coeffs.get((i, j, k), 0) + weight_y * weight_z) % p
    return {k: v % p for k, v in coeffs.items() if v % p}


def alternating_trivector_gl3(diag: Tuple[int, int, int], p: int) -> Dict[Tuple[int, int, int], int]:
    """Exterior projection of F_P to Lambda^3(gl_3)."""
    alt: Dict[Tuple[int, int, int], int] = {}
    for (i, j, k), coef in F_coeff_ordered(diag, p).items():
        if len({i, j, k}) < 3:
            continue
        s = tuple(sorted((i, j, k)))
        alt[s] = (alt.get(s, 0) + sort_sign((i, j, k)) * coef) % p
    return {k: v % p for k, v in alt.items() if v % p}


def alt_value_from_sorted(alt: Dict[Tuple[int, int, int], int], inds: Tuple[int, int, int], p: int) -> int:
    if len(set(inds)) < 3:
        return 0
    s = tuple(sorted(inds))
    c = alt.get(s, 0)
    if c == 0:
        return 0
    return (sort_sign(inds) * c) % p


def restrict_alt_to_sl3(alt: Dict[Tuple[int, int, int], int], p: int) -> Dict[Tuple[int, int, int], int]:
    out: Dict[Tuple[int, int, int], int] = {}
    B = np.array(SL3_B, dtype=object)
    for (a, b, c) in TRIP8:
        val = 0
        for i, j, k in itertools.product(range(N), repeat=3):
            coef = int(B[i, a]) * int(B[j, b]) * int(B[k, c])
            if coef:
                val += coef * alt_value_from_sorted(alt, (i, j, k), p)
        val %= p
        if val:
            out[(a, b, c)] = val
    return out


def contraction_trace_alt(alt: Dict[Tuple[int, int, int], int], p: int) -> Dict[Tuple[int, int], int]:
    diag_indices = {0, 4, 8}
    biv: Dict[Tuple[int, int], int] = {}
    for (i, j, k), coef in alt.items():
        arr = [i, j, k]
        for pos, elem in enumerate(arr):
            if elem not in diag_indices:
                continue
            rem = [arr[q] for q in range(3) if q != pos]
            pair = tuple(sorted(rem))
            biv[pair] = (biv.get(pair, 0) + ((-1) ** pos) * coef) % p
    return {k: v % p for k, v in biv.items() if v % p}


def gl8_stabilizer_dim(omega: Dict[Tuple[int, int, int], int], p: int) -> Tuple[int, int, int]:
    n = 8
    mat = np.zeros((len(TRIP8), n * n), dtype=np.int64)
    for (i, j, k), coef in omega.items():
        coef %= p
        for l in range(n):
            if l != j and l != k:
                trip = tuple(sorted((l, j, k)))
                row = TRIP8_IDX[trip]
                col = l * n + i
                mat[row, col] = (mat[row, col] + sort_sign((l, j, k)) * coef) % p
            if l != i and l != k:
                trip = tuple(sorted((i, l, k)))
                row = TRIP8_IDX[trip]
                col = l * n + j
                mat[row, col] = (mat[row, col] + sort_sign((i, l, k)) * coef) % p
            if l != i and l != j:
                trip = tuple(sorted((i, j, l)))
                row = TRIP8_IDX[trip]
                col = l * n + k
                mat[row, col] = (mat[row, col] + sort_sign((i, j, l)) * coef) % p
    r = rank_mod(mat, p)
    return n * n, r, n * n - r


def matmul_mod(A: np.ndarray, B: np.ndarray, p: int) -> np.ndarray:
    return (A.astype(object) @ B.astype(object) % p).astype(object)


def trace_mod(A: np.ndarray, p: int) -> int:
    return int(sum(int(A[i, i]) for i in range(A.shape[0])) % p)


def g_apply(M: np.ndarray, diag: Tuple[int, int, int], power: int, p: int) -> np.ndarray:
    out = np.zeros((3, 3), dtype=object)
    dp = [pow(x % p, power, p) for x in diag]
    invp = [pow(x, -1, p) for x in dp]
    for a in range(3):
        for b in range(3):
            out[a, b] = (int(M[a, b]) * dp[a] * invp[b]) % p
    return out


def full_exterior_stabilizer(alt: Dict[Tuple[int, int, int], int], p: int) -> dict:
    """GL_9 stabilizer/orbit dimension for the full exterior target in Lambda^3(gl_3)."""
    n = 9
    triples = list(itertools.combinations(range(n), 3))
    tidx = {t: i for i, t in enumerate(triples)}
    mat = np.zeros((len(triples), n * n), dtype=np.int64)
    for (i, j, k), coef in alt.items():
        coef %= p
        for l in range(n):
            if l != j and l != k:
                trip = tuple(sorted((l, j, k)))
                mat[tidx[trip], l * n + i] = (mat[tidx[trip], l * n + i] + sort_sign((l, j, k)) * coef) % p
            if l != i and l != k:
                trip = tuple(sorted((i, l, k)))
                mat[tidx[trip], l * n + j] = (mat[tidx[trip], l * n + j] + sort_sign((i, l, k)) * coef) % p
            if l != i and l != j:
                trip = tuple(sorted((i, j, l)))
                mat[tidx[trip], l * n + k] = (mat[tidx[trip], l * n + k] + sort_sign((i, j, l)) * coef) % p
    map_rank = rank_mod(mat, p)
    return {
        "dim_gl9": n * n,
        "map_rank": map_rank,
        "stab_dim": n * n - map_rank,
        "orbit_dim": map_rank,
        "ambient_lambda3_gl3_dim": len(triples),
        "sigma3_affine_upper_dim": 3 * (3 * (9 - 3)) + 3,
        "sigma3_dimension_argument_excludes_m_le_3": map_rank > 3 * (3 * (9 - 3)) + 3,
    }


def trace_quadratic_matrix(diag: Tuple[int, int, int], p: int) -> Tuple[np.ndarray, int]:
    """Quadratic coefficient of s in C_P(X0+sI), restricted to sl_3.

    We compute the symmetric bilinear matrix by evaluating the coefficient
    polynomial on basis sums: q(e_i+e_j)-q(e_i)-q(e_j).
    """
    I = np.eye(3, dtype=object)

    def q(M: np.ndarray) -> int:
        gM = g_apply(M, diag, 1, p)
        g2M = g_apply(M, diag, 2, p)
        # coefficient of s in tr((M+sI)(gM+sI)(g2M+sI))
        term = matmul_mod(gM, g2M, p)
        val = trace_mod(term, p)
        val = (val + trace_mod(matmul_mod(M, g2M, p), p)) % p
        val = (val + trace_mod(matmul_mod(M, gM, p), p)) % p
        return val % p

    qs = [q(np.array(B, dtype=object)) for B in SL3_BASIS_MATS]
    Q = np.zeros((SLN, SLN), dtype=np.int64)
    inv2 = pow(2, -1, p)
    # diagonal entries satisfy q(e_i)=Q_ii for polynomial x^T Q x convention.
    for i in range(SLN):
        Q[i, i] = qs[i] % p
    for i in range(SLN):
        for j in range(i + 1, SLN):
            M = (SL3_BASIS_MATS[i] + SL3_BASIS_MATS[j]) % p
            cross = (q(M) - qs[i] - qs[j]) % p
            # In x^T Q x, cross term is 2 Q_ij x_i x_j.
            Q[i, j] = Q[j, i] = (cross * inv2) % p
    return Q % p, rank_mod(Q, p)


def cubic_tensor_CP(diag: Tuple[int, int, int], p: int) -> np.ndarray:
    """Symmetric tensor for the cubic polynomial C_P(X)."""
    mono: Dict[Tuple[int, int, int], int] = {}
    for (i, j, k), coef in F_coeff_ordered(diag, p).items():
        key = tuple(sorted((i, j, k)))
        mono[key] = (mono.get(key, 0) + coef) % p
    T = np.zeros((N, N, N), dtype=np.int64)
    for key, coef in mono.items():
        perms = sorted(set(itertools.permutations(key)))
        val = (coef * pow(len(perms), -1, p)) % p
        for perm in perms:
            T[perm] = val
    return T % p


def cube_tensor(p: int) -> np.ndarray:
    T = np.zeros((N, N, N), dtype=np.int64)
    T[0, 0, 0] = 1
    return T


def koszul_matrix_cubic(T: np.ndarray, p: int) -> np.ndarray:
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
                M[row_base:row_base + N, col] = (M[row_base:row_base + N, col] + sign * T[a, i, :]) % p
    return M % p


def ky_rank(T: np.ndarray, p: int) -> int:
    return rank_mod(koszul_matrix_cubic(T, p), p)


def analyze_class(label: str, diag: Tuple[int, int, int], p: int) -> dict:
    tr1_int, tr2_int, invdim_int = recognize_ad_trace(label)
    tr1_mod = ad_trace(diag, 1, p)
    tr2_mod = ad_trace(diag, 2, p)
    alt = alternating_trivector_gl3(diag, p)
    alt_sl3 = restrict_alt_to_sl3(alt, p)
    biv_trace = contraction_trace_alt(alt, p)
    dim_gl8, stab_map_rank, stab_dim = gl8_stabilizer_dim(alt_sl3, p)
    Q, qrank = trace_quadratic_matrix(diag, p)
    T = cubic_tensor_CP(diag, p)
    kyr = ky_rank(T, p)
    return {
        "label": label,
        "diag_mod_p": list(map(int, diag)),
        "prime": p,
        "ad_trace_mod": {"tr_g": int(tr1_mod), "tr_g2": int(tr2_mod)},
        "ad_trace_char0_integer": {"tr_g": tr1_int, "tr_g2": tr2_int},
        "deprecated_wrong_invariant_dimension_formula_using_trace_AdP": invdim_int,
        "actual_order3_rhoP_invariant_dimension_from_action_selfcheck": 249,
        "exterior_gl3_nonzero_terms": len(alt),
        "iota_trace_nonzero_terms": len(biv_trace),
        "traceless_projection_nonzero_terms": len(alt_sl3),
        "traceless_projection_terms_mod_p": {str(k): int(v) for k, v in sorted(alt_sl3.items())},
        "gl8_stabilizer_on_traceless_projection": {
            "dim_gl8": dim_gl8,
            "map_rank": stab_map_rank,
            "stab_dim": stab_dim,
            "orbit_dim": dim_gl8 - stab_dim,
            "ambient_lambda3_sl3_dim": 56,
            "open_orbit_by_stabilizer_8": stab_dim == 8,
            "sigma3_affine_upper_dim": 48,
            "sigma3_dimension_argument_excludes_m_le_3_from_sl3_projection": stab_dim == 8,
        },
        "gl9_stabilizer_on_full_exterior_target": full_exterior_stabilizer(alt, p),
        "trace_grading_quadratic_rank_on_sl3": qrank,
        "trace_grading_quadratic_matrix_mod_p": Q.astype(int).tolist(),
        "koszul_young_rank_CP": kyr,
        "koszul_young_matrix_shape": [len(SUB5) * N, N * len(SUB4)],
    }


def main() -> None:
    # Use two primes for the small ranks; KY ranks are computed at the first prime
    # and pure calibration checks the convention.  The second prime repeats all
    # non-KY ranks cheaply enough for stability.
    primes = [65521, 1000003]
    all_records = []
    for p in primes:
        z = find_zeta(p)
        classes = {
            "pure_I": (1, 1, 1),
            "two_plus_one": (1, 1, z),
            "regular_three": (1, z, (z * z) % p),
        }
        print(f"prime {p}, zeta={z}")
        cube_rank = ky_rank(cube_tensor(p), p)
        print(f"  cube KY rank={cube_rank}")
        for label, diag in classes.items():
            rec = analyze_class(label, diag, p)
            rec["cube_KY_rank_calibration"] = cube_rank
            all_records.append(rec)
            g = rec["gl8_stabilizer_on_traceless_projection"]
            print(
                f"  {label}: deprecated_trace_diag={rec['deprecated_wrong_invariant_dimension_formula_using_trace_AdP']} actual_dim=249 "
                f"alt_sl3_terms={rec['traceless_projection_nonzero_terms']} "
                f"stab={g['stab_dim']} qrank={rec['trace_grading_quadratic_rank_on_sl3']} "
                f"KY={rec['koszul_young_rank_CP']}"
            )

    # Compact comparison by characteristic-zero class, using both primes.
    comparison = {}
    for label in ["pure_I", "two_plus_one", "regular_three"]:
        rows = [r for r in all_records if r["label"] == label]
        comparison[label] = {
            "deprecated_wrong_invariant_dimension_formula_using_trace_AdP": rows[0]["deprecated_wrong_invariant_dimension_formula_using_trace_AdP"],
            "actual_order3_rhoP_invariant_dimension": 249,
            "ad_trace_char0": rows[0]["ad_trace_char0_integer"],
            "primes": [r["prime"] for r in rows],
            "stab_dims": [r["gl8_stabilizer_on_traceless_projection"]["stab_dim"] for r in rows],
            "trace_quadratic_ranks": [r["trace_grading_quadratic_rank_on_sl3"] for r in rows],
            "KY_ranks_CP": [r["koszul_young_rank_CP"] for r in rows],
            "exterior_m_ge_4_by_full_gl9_orbit_all_primes": all(
                r["gl9_stabilizer_on_full_exterior_target"]["orbit_dim"] > r["gl9_stabilizer_on_full_exterior_target"]["sigma3_affine_upper_dim"] for r in rows
            ),
            "sl3_projection_open_orbit_all_primes": all(
                r["gl8_stabilizer_on_traceless_projection"]["stab_dim"] == 8 for r in rows
            ),
        }

    out = {
        "schema": "twisted_cyclic_invariants_v1",
        "model": "twisted fixed-locus model C_P(X)=tr(X Ad(P)X Ad(P)^2X) with diagonal representatives of PGL3 order-3 classes",
        "class_representatives_char0": {
            "pure_I": "P=I, already studied as pure cyclic",
            "two_plus_one": "P=diag(1,1,zeta)",
            "regular_three": "P=diag(1,zeta,zeta^2)",
        },
        "central_lift_note": "Multiplying P by a scalar or allowing P^3 to be scalar does not change Ad(P), the fixed-locus cubic C_P, or the modular invariants recorded here. A full sandwich-extension action/fixed-locus faithfulness proof is still a separate algebraic task.",
        "comparison": comparison,
        "records": all_records,
        "interpretation": (
            "The 245 and 243 values for the nontrivial classes are only the deprecated "
            "scalar trace diagnostic (729+tr(AdP)+tr(AdP)^2)/3; they are not invariant "
            "dimensions of the actual order-3 cyclic action.  The action selfcheck gives "
            "dimension 249 for all three rho_P actions.  For all three "
            "classes the full exterior target in Lambda^3(gl3) has GL9 orbit dimension 64, "
            "larger than the affine sigma_3(G(3,9)) upper bound 57, so the same orbit-dimension "
            "mechanism excludes m<=3 at the level of the full exterior equation.  The sl3 "
            "projection behaves differently: the two-plus-one class remains open-orbit in "
            "Lambda^3(sl3), while the regular-three class has stabilizer dimension 22 after "
            "trace-free projection, so the old Cartan-only formulation does not transfer.  "
            "The trace-grading quadratic rank remains 8 and the KY rank of C_P is 950 in all "
            "three classes; the missing pieces are the exact sandwich-extension/fixed-locus "
            "faithfulness proof and the mixed-independent-verification-record hypotheses needed to turn "
            "these measurements into a theorem about cyclic-type rank-22 skeletons."
        ),
    }
    path = OUT / "twisted_cyclic_invariants.json"
    path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(f"SAVED {path}")


if __name__ == "__main__":
    main()
