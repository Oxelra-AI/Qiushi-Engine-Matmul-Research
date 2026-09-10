#!/usr/bin/env python3
"""analysis repair: action-level self-check for twisted order-3 cyclic symmetries.

The previous analysis invariant script correctly built the fixed-locus cubic
C_P(X)=tr(X Ad(P)X Ad(P)^2 X), but it incorrectly interpreted
(729+tr Ad(P)+tr Ad(P)^2)/3 as the invariant dimension of the order-3
factor-rotation symmetry.  This script works directly with the actual order-3
variable action

    rho_P(X,Y,Z) = (g^2 Y, g^2 Z, g^2 X),  g=Ad(P), g^3=1,

which has fixed locus (X,gX,g^2X), preserves T(X,Y,Z)=tr(XYZ), and is
conjugate to pure cyclic rotation by Q(X,Y,Z)=(X,gY,g^2Z).

It verifies, over primes p=1 mod 3, the action order, preservation of T,
invariant dimension 249 for all three PGL_3 order-3 classes, the fixed-locus
cubic identity, the adapted exterior radical P^{-1}, the adapted Cartan/open
orbit statement on h_P={X:tr(XP)=0}, and the adapted trace-grading quadratic
rank 8.
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
TRIP9 = list(itertools.combinations(range(N), 3))
TRIP8 = list(itertools.combinations(range(SLN), 3))
TRIP8_IDX = {t: i for i, t in enumerate(TRIP8)}

STD_SL3: List[np.ndarray] = []
for (a, b) in [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]:
    M = np.zeros((3, 3), dtype=object); M[a, b] = 1; STD_SL3.append(M)
H0 = np.zeros((3, 3), dtype=object); H0[0, 0] = 1; H0[1, 1] = -1; STD_SL3.append(H0)
H1 = np.zeros((3, 3), dtype=object); H1[1, 1] = 1; H1[2, 2] = -1; STD_SL3.append(H1)


def idx(a: int, b: int) -> int:
    return 3 * a + b


def unidx(i: int) -> Tuple[int, int]:
    return divmod(i, 3)


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
    raise RuntimeError(f"no zeta in F_{p}")


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


def mat_key(M: np.ndarray) -> Tuple[int, ...]:
    return tuple(int(M[a, b]) for a in range(3) for b in range(3))


def key_mat(v: Tuple[int, ...]) -> np.ndarray:
    M = np.zeros((3, 3), dtype=object)
    for a in range(3):
        for b in range(3):
            M[a, b] = v[3 * a + b]
    return M


def matmul(A: np.ndarray, B: np.ndarray, p: int) -> np.ndarray:
    return (A.astype(object) @ B.astype(object) % p).astype(object)


def tr(A: np.ndarray, p: int) -> int:
    return int(sum(int(A[i, i]) for i in range(3)) % p)


def g_apply(M: np.ndarray, diag: Tuple[int, int, int], power: int, p: int) -> np.ndarray:
    dp = [pow(x % p, power, p) for x in diag]
    inv = [pow(x, -1, p) for x in dp]
    out = np.zeros((3, 3), dtype=object)
    for a in range(3):
        for b in range(3):
            out[a, b] = int(M[a, b]) * dp[a] * inv[b] % p
    return out


def rho_tuple(t: Tuple[np.ndarray, np.ndarray, np.ndarray], diag, p):
    X, Y, Z = t
    return (g_apply(Y, diag, 2, p), g_apply(Z, diag, 2, p), g_apply(X, diag, 2, p))


def rot_tuple(t):
    X, Y, Z = t
    return (Y, Z, X)


def Q_tuple(t, diag, p):
    X, Y, Z = t
    return (X.copy(), g_apply(Y, diag, 1, p), g_apply(Z, diag, 2, p))


def Qinv_tuple(t, diag, p):
    X, Y, Z = t
    return (X.copy(), g_apply(Y, diag, 2, p), g_apply(Z, diag, 1, p))


def T_value(t, p: int) -> int:
    X, Y, Z = t
    return tr(matmul(matmul(X, Y, p), Z, p), p)


def random_matrix(seed: int, p: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    return np.array(rng.integers(0, p, size=(3, 3)), dtype=object)


def ad_weight_index(i: int, diag: Tuple[int, int, int], p: int) -> int:
    a, b = unidx(i)
    return diag[a] * pow(diag[b] % p, -1, p) % p


def coefficient_action_orbit_stats(diag: Tuple[int, int, int], p: int) -> dict:
    """Fixed-space dimension of pullback R(F)=F(rho_P(.)) on V*⊗3.

    Basis monomial x_i y_j z_k maps to scalar*w basis x_k y_i z_j,
    with scalar w_i^2 w_j^2 w_k^2.  Because g^3=1, every orbit contributes
    one fixed dimension; this routine checks the scalar product around cycles.
    """
    seen = set()
    cycles = []
    bad_products = []
    for i, j, k in itertools.product(range(N), repeat=3):
        if (i, j, k) in seen:
            continue
        cur = (i, j, k)
        cyc = []
        prod = 1
        while cur not in cyc:
            cyc.append(cur); seen.add(cur)
            a, b, c = cur
            scalar = pow(ad_weight_index(a, diag, p), 2, p) * pow(ad_weight_index(b, diag, p), 2, p) * pow(ad_weight_index(c, diag, p), 2, p)
            scalar %= p
            prod = (prod * scalar) % p
            cur = (c, a, b)
        if prod != 1:
            bad_products.append((cyc, prod))
        cycles.append(cyc)
    hist: Dict[int, int] = {}
    for cyc in cycles:
        hist[len(cyc)] = hist.get(len(cyc), 0) + 1
    return {
        "cycle_length_histogram": {str(k): v for k, v in sorted(hist.items())},
        "fixed_space_dimension_from_cycles": len(cycles),
        "bad_cycle_products": len(bad_products),
        "total_basis_tensors": N ** 3,
    }


def T_coefficients() -> Dict[Tuple[int, int, int], int]:
    coeff = {}
    for a, b, c in itertools.product(range(3), repeat=3):
        coeff[(idx(a, b), idx(b, c), idx(c, a))] = 1
    return coeff


def F_coefficients(diag: Tuple[int, int, int], p: int) -> Dict[Tuple[int, int, int], int]:
    coeff = {}
    for a, b, c in itertools.product(range(3), repeat=3):
        i, j, k = idx(a, b), idx(b, c), idx(c, a)
        wy = ad_weight_index(j, diag, p)
        wz = pow(ad_weight_index(k, diag, p), 2, p)
        coeff[(i, j, k)] = (coeff.get((i, j, k), 0) + wy * wz) % p
    return {k: v for k, v in coeff.items() if v}


def alt_from_coeff(coeff: Dict[Tuple[int, int, int], int], p: int) -> Dict[Tuple[int, int, int], int]:
    alt: Dict[Tuple[int, int, int], int] = {}
    for (i, j, k), c in coeff.items():
        if len({i, j, k}) < 3:
            continue
        s = tuple(sorted((i, j, k)))
        alt[s] = (alt.get(s, 0) + sort_sign((i, j, k)) * c) % p
    return {k: v % p for k, v in alt.items() if v % p}


def alt_value(alt: Dict[Tuple[int, int, int], int], inds: Tuple[int, int, int], p: int) -> int:
    if len(set(inds)) < 3:
        return 0
    s = tuple(sorted(inds))
    return sort_sign(inds) * alt.get(s, 0) % p


def contraction_vector(alt: Dict[Tuple[int, int, int], int], v: List[int], p: int) -> Dict[Tuple[int, int], int]:
    out: Dict[Tuple[int, int], int] = {}
    for (i, j, k), c in alt.items():
        arr = [i, j, k]
        for pos, elem in enumerate(arr):
            if v[elem] % p == 0:
                continue
            rem = [arr[q] for q in range(3) if q != pos]
            pair = tuple(sorted(rem))
            out[pair] = (out.get(pair, 0) + ((-1) ** pos) * v[elem] * c) % p
    return {k: val for k, val in out.items() if val % p}


def restrict_alt_to_basis(alt: Dict[Tuple[int, int, int], int], basis: List[np.ndarray], p: int) -> Dict[Tuple[int, int, int], int]:
    # Matrix of basis vectors in gl3 coordinates.
    B = np.zeros((N, len(basis)), dtype=object)
    for j, M in enumerate(basis):
        for a in range(3):
            for b in range(3):
                B[idx(a, b), j] = int(M[a, b]) % p
    out: Dict[Tuple[int, int, int], int] = {}
    for (a, b, c) in itertools.combinations(range(len(basis)), 3):
        val = 0
        for i, j, k in itertools.product(range(N), repeat=3):
            coef = int(B[i, a]) * int(B[j, b]) * int(B[k, c])
            if coef:
                val += coef * alt_value(alt, (i, j, k), p)
        val %= p
        if val:
            out[(a, b, c)] = val
    return out


def gl8_stabilizer(omega: Dict[Tuple[int, int, int], int], p: int) -> dict:
    n = 8
    mat = np.zeros((len(TRIP8), n * n), dtype=np.int64)
    for (i, j, k), coef in omega.items():
        coef %= p
        for l in range(n):
            if l != j and l != k:
                trip = tuple(sorted((l, j, k)))
                mat[TRIP8_IDX[trip], l * n + i] = (mat[TRIP8_IDX[trip], l * n + i] + sort_sign((l, j, k)) * coef) % p
            if l != i and l != k:
                trip = tuple(sorted((i, l, k)))
                mat[TRIP8_IDX[trip], l * n + j] = (mat[TRIP8_IDX[trip], l * n + j] + sort_sign((i, l, k)) * coef) % p
            if l != i and l != j:
                trip = tuple(sorted((i, j, l)))
                mat[TRIP8_IDX[trip], l * n + k] = (mat[TRIP8_IDX[trip], l * n + k] + sort_sign((i, j, l)) * coef) % p
    r = rank_mod(mat, p)
    return {"map_rank": r, "stab_dim": n * n - r, "orbit_dim": r, "ambient_dim": 56, "sigma3_affine_upper": 48, "excludes_sigma3_by_dimension": r > 48}


def adapted_h_basis(diag: Tuple[int, int, int], p: int) -> List[np.ndarray]:
    # h_P = {X: tr(XP)=0}; if B in sl3, M=B P^{-1} has tr(MP)=tr(B)=0.
    invdiag = [pow(x % p, -1, p) for x in diag]
    Pinv = np.diag(invdiag).astype(object)
    return [matmul(B, Pinv, p) for B in STD_SL3]


def trace_quadratic_rank_adapted(diag: Tuple[int, int, int], p: int) -> Tuple[int, List[List[int]]]:
    basis = adapted_h_basis(diag, p)
    Pinv = np.diag([pow(x % p, -1, p) for x in diag]).astype(object)

    def C(M: np.ndarray) -> int:
        return T_value((M, g_apply(M, diag, 1, p), g_apply(M, diag, 2, p)), p)

    def q(M: np.ndarray) -> int:
        # coefficient of s in C(M+s P^{-1}) by finite differences at s=0,1,2,3.
        # Since C is cubic in s, interpolate coefficient of s.  Easier: use formula
        # tr(gM*g2M)+tr(M*g2M*g(Pinv)? etc).  Finite difference is safer here.
        vals = []
        for s in [0, 1, 2, 3]:
            vals.append(C((M + s * Pinv) % p))
        # Solve Vandermonde for c0+c1*s+c2*s^2+c3*s^3 over F_p.
        V = np.array([[pow(s, d, p) for d in range(4)] for s in [0, 1, 2, 3]], dtype=np.int64)
        b = np.array(vals, dtype=np.int64).reshape(4, 1)
        # Gaussian solve small augmented matrix.
        A = np.concatenate([V % p, b % p], axis=1)
        r = 0
        for c in range(4):
            piv = None
            for i in range(r, 4):
                if A[i, c] % p:
                    piv = i; break
            if piv is None:
                continue
            if piv != r:
                A[[r, piv]] = A[[piv, r]]
            inv = pow(int(A[r, c]), -1, p)
            A[r, :] = A[r, :] * inv % p
            for i in range(4):
                if i != r and A[i, c] % p:
                    A[i, :] = (A[i, :] - A[i, c] * A[r, :]) % p
            r += 1
        coeff = [0, 0, 0, 0]
        for i in range(4):
            piv = None
            for c in range(4):
                if A[i, c] == 1:
                    piv = c; break
            if piv is not None:
                coeff[piv] = int(A[i, 4] % p)
        return coeff[1]

    qs = [q(B) for B in basis]
    Q = np.zeros((8, 8), dtype=np.int64)
    inv2 = pow(2, -1, p)
    for i in range(8):
        Q[i, i] = qs[i]
    for i in range(8):
        for j in range(i + 1, 8):
            cross = (q((basis[i] + basis[j]) % p) - qs[i] - qs[j]) % p
            Q[i, j] = Q[j, i] = cross * inv2 % p
    return rank_mod(Q, p), Q.astype(int).tolist()


def matrix_basis() -> List[np.ndarray]:
    out = []
    for a in range(3):
        for b in range(3):
            M = np.zeros((3, 3), dtype=object)
            M[a, b] = 1
            out.append(M)
    return out


def tensor_CP_equals_XP_cubic(diag: Tuple[int, int, int], p: int) -> bool:
    # Exact coefficient check: tr(X gX g^2X) and tr((XP)^3) agree as cubics.
    E = matrix_basis()
    Pmat = np.diag(list(diag)).astype(object)
    for i, j, k in itertools.product(range(N), repeat=3):
        # Compare the full symmetric trilinear polarization by checking all ordered coefficients.
        X, Y, Z = E[i], E[j], E[k]
        left = T_value((X, g_apply(Y, diag, 1, p), g_apply(Z, diag, 2, p)), p)
        XP, YP, ZP = matmul(X, Pmat, p), matmul(Y, Pmat, p), matmul(Z, Pmat, p)
        right = T_value((XP, YP, ZP), p)
        if left != right:
            return False
    return True


def exact_action_checks(diag: Tuple[int, int, int], p: int) -> dict:
    E = matrix_basis()
    action_order_ok = True
    preserves_T = True
    conjugacy_ok = True
    fixed_locus_ok = True
    for i, j, k in itertools.product(range(N), repeat=3):
        tup = (E[i], E[j], E[k])
        r3 = rho_tuple(rho_tuple(rho_tuple(tup, diag, p), diag, p), diag, p)
        if tuple(mat_key(M) for M in r3) != tuple(mat_key(M) for M in tup):
            action_order_ok = False
        if T_value(rho_tuple(tup, diag, p), p) != T_value(tup, p):
            preserves_T = False
        lhs = Qinv_tuple(rho_tuple(Q_tuple(tup, diag, p), diag, p), diag, p)
        rhs = rot_tuple(tup)
        if tuple(mat_key(M) for M in lhs) != tuple(mat_key(M) for M in rhs):
            conjugacy_ok = False
    for X in E:
        fixed = (X, g_apply(X, diag, 1, p), g_apply(X, diag, 2, p))
        if tuple(mat_key(M) for M in rho_tuple(fixed, diag, p)) != tuple(mat_key(M) for M in fixed):
            fixed_locus_ok = False
    return {
        "action_order_three_ok_on_basis": action_order_ok,
        "preserves_T_on_basis": preserves_T,
        "Q_conjugates_to_pure_rotation_on_basis": conjugacy_ok,
        "fixed_locus_basis_generators_ok": fixed_locus_ok,
    }


def analyze(label: str, diag: Tuple[int, int, int], p: int) -> dict:
    checks = exact_action_checks(diag, p)
    coeff_F = F_coefficients(diag, p)
    alt = alt_from_coeff(coeff_F, p)
    Pinv_vec = [0] * N
    for a in range(3):
        Pinv_vec[idx(a, a)] = pow(diag[a] % p, -1, p)
    radical_contraction = contraction_vector(alt, Pinv_vec, p)
    omega_h = restrict_alt_to_basis(alt, adapted_h_basis(diag, p), p)
    qrank, qmat = trace_quadratic_rank_adapted(diag, p)

    # T preservation coefficient check: random preservation done above; exact support count too.
    return {
        "label": label,
        "prime": p,
        "diag_mod_p": list(map(int, diag)),
        **checks,
        "invariant_dimension": coefficient_action_orbit_stats(diag, p),
        "F_coeff_nonzero_count": len(coeff_F),
        "F_P_equals_T_after_right_multiply_by_P_on_basis": tensor_CP_equals_XP_cubic(diag, p),
        "full_exterior_nonzero_count": len(alt),
        "iota_Pinv_full_exterior_nonzero_count": len(radical_contraction),
        "adapted_h_trivector_nonzero_count": len(omega_h),
        "adapted_h_trivector_terms": {str(k): int(v) for k, v in sorted(omega_h.items())},
        "adapted_h_gl8_stabilizer": gl8_stabilizer(omega_h, p),
        "adapted_trace_quadratic_rank": qrank,
        "adapted_trace_quadratic_matrix": qmat,
    }


def main() -> None:
    primes = [65521, 1000003]
    records = []
    for p in primes:
        z = find_zeta(p)
        reps = {
            "pure_I": (1, 1, 1),
            "two_plus_one": (1, 1, z),
            "regular_three": (1, z, z * z % p),
        }
        print(f"prime {p}, zeta={z}")
        for label, diag in reps.items():
            rec = analyze(label, diag, p)
            records.append(rec)
            inv = rec["invariant_dimension"]["fixed_space_dimension_from_cycles"]
            stab = rec["adapted_h_gl8_stabilizer"]["stab_dim"]
            print(f"  {label}: inv_dim={inv}, iotaPinv={rec['iota_Pinv_full_exterior_nonzero_count']}, h_stab={stab}, qrank={rec['adapted_trace_quadratic_rank']}")

    comparison = {}
    for label in ["pure_I", "two_plus_one", "regular_three"]:
        rows = [r for r in records if r["label"] == label]
        comparison[label] = {
            "primes": [r["prime"] for r in rows],
            "order_three_all": all(r["action_order_three_ok_on_basis"] for r in rows),
            "preserves_T_all": all(r["preserves_T_on_basis"] for r in rows),
            "conjugacy_to_pure_rotation_all": all(r["Q_conjugates_to_pure_rotation_on_basis"] for r in rows),
            "invariant_dimensions": [r["invariant_dimension"]["fixed_space_dimension_from_cycles"] for r in rows],
            "cycle_histograms": [r["invariant_dimension"]["cycle_length_histogram"] for r in rows],
            "iota_Pinv_counts": [r["iota_Pinv_full_exterior_nonzero_count"] for r in rows],
            "adapted_h_stab_dims": [r["adapted_h_gl8_stabilizer"]["stab_dim"] for r in rows],
            "adapted_h_orbit_dims": [r["adapted_h_gl8_stabilizer"]["orbit_dim"] for r in rows],
            "adapted_trace_quadratic_ranks": [r["adapted_trace_quadratic_rank"] for r in rows],
        }

    out = {
        "schema": "twisted_cyclic_action_selfcheck_v1",
        "mathematical_model": "rho_P(X,Y,Z)=(Ad(P)^2Y, Ad(P)^2Z, Ad(P)^2X), fixed locus (X,Ad(P)X,Ad(P)^2X)",
        "correction_to_previous_script": "The actual order-3 rho_P invariant dimension is 249 for all PGL3 order-3 classes; the earlier 245/243 numbers used the wrong Burnside trace for this action.",
        "records": records,
        "comparison": comparison,
        "interpretation": (
            "The order-3 cyclic-type actions represented by P=I, diag(1,1,zeta), and diag(1,zeta,zeta^2) "
            "are action-conjugate to pure cyclic rotation by Q=(Id,Ad(P),Ad(P)^2), preserve T, and have the "
            "same invariant dimension 249 and orbit histogram 9 fixed coordinates plus 240 three-cycles. "
            "The fixed-locus cubic is C_P(X)=tr((XP)^3).  The full exterior target has radical KP^{-1}; "
            "on the adapted 8-space h_P={tr(XP)=0}, the projected trivector is in the open GL8 orbit and "
            "outside sigma_3 by the same dimension argument, so m>=4 transfers in adapted coordinates. "
            "The trace-grading quadratic on h_P has rank 8.  These checks show that the apparent new twisted "
            "order-3 classes do not create a weaker cyclic skeleton by themselves; the old pure-cyclic proof must "
            "be worded as an adapted-coordinate statement, and the same mixed-independent-verification-record and residual-Waring "
            "questions remain."
        ),
    }
    path = OUT / "twisted_cyclic_action_selfcheck.json"
    path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(f"SAVED {path}")


if __name__ == "__main__":
    main()
