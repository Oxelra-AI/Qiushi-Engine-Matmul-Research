#!/usr/bin/env python3
"""
analysis: canonical Q-basis convention for the characteristic-zero Z4 block model.

Rule implemented here:
  1. Convert stored packed forms L, paired as tr(L^T M), to A=L^T so the pairing is tr(A M).
  2. Diagonalize the matrix acting on form coefficients: Q^{-1} a0^T Q = D.
  3. Use the same basis on matrices: A''=Q^{-1}AQ, M''=Q^{-1}MQ.  Then
       A'' -> D A'' D^{-1},  M'' -> D^{-1} M'' D,
       tr(A M)=tr(A'' M'').

The script verifies the convention without relying on BILR alone: in the Q-basis
tr(X^3) must split into the short p/q/z/w blocks with rank-one hyperbolic qz^2
and qw^2 pieces and different q-directions.  It then checks that the reconstructed
BILR residual is a 1+2+4+4 Z4 orbit-sum of cubes in the same convention.
"""
from __future__ import annotations

import itertools
import json
import random
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "z4_qbasis"
OUT.mkdir(parents=True, exist_ok=True)

N = 9
MONOS = list(itertools.combinations_with_replacement(range(N), 3))
MONO_IDX = {m: i for i, m in enumerate(MONOS)}
# Canonical coordinate order for M'' entries n_ab.
COORDS = [
    (0, 0), (1, 1), (2, 2),       # p
    (1, 2), (2, 1),               # q = n23,n32
    (1, 0), (0, 2),               # z = n21,n13
    (0, 1), (2, 0),               # w = n12,n31
]
GROUPS = {
    "p": [0, 1, 2],
    "q": [3, 4],
    "z": [5, 6],
    "w": [7, 8],
}


def inv(a: int, p: int) -> int:
    return pow(int(a) % p, -1, p)


def matmul(A, B, p: int) -> np.ndarray:
    A = np.array(A, dtype=object) % p
    B = np.array(B, dtype=object) % p
    C = np.zeros((A.shape[0], B.shape[1]), dtype=object)
    for i in range(A.shape[0]):
        for j in range(B.shape[1]):
            s = 0
            for k in range(A.shape[1]):
                s += int(A[i, k]) * int(B[k, j])
            C[i, j] = s % p
    return C


def mat_inv(M, p: int) -> np.ndarray:
    M = np.array(M, dtype=object) % p
    n = M.shape[0]
    aug = [[int(M[i, j]) % p for j in range(n)] + [1 if i == j else 0 for j in range(n)] for i in range(n)]
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, n):
            if aug[i][c] % p:
                piv = i
                break
        if piv is None:
            raise ValueError("singular matrix")
        aug[r], aug[piv] = aug[piv], aug[r]
        scale = inv(aug[r][c], p)
        aug[r] = [(x * scale) % p for x in aug[r]]
        for i in range(n):
            if i != r and aug[i][c] % p:
                f = aug[i][c] % p
                aug[i] = [(aug[i][j] - f * aug[r][j]) % p for j in range(2 * n)]
        r += 1
    return np.array([[aug[i][n + j] % p for j in range(n)] for i in range(n)], dtype=object)


def rank_mod(A, p: int) -> int:
    A = np.array(A, dtype=object) % p
    m, n = A.shape
    B = [[int(A[i, j]) % p for j in range(n)] for i in range(m)]
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if B[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        B[r], B[piv] = B[piv], B[r]
        scale = inv(B[r][c], p)
        B[r] = [(x * scale) % p for x in B[r]]
        for i in range(m):
            if i != r and B[i][c] % p:
                f = B[i][c] % p
                B[i] = [(B[i][j] - f * B[r][j]) % p for j in range(n)]
        r += 1
        if r == m:
            break
    return r


def sqrt_minus_one(p: int) -> int:
    for x in range(2, p):
        if (x * x) % p == p - 1:
            return x
    raise ValueError("prime must split i")


def q_basis(p: int):
    i = sqrt_minus_one(p)
    a0 = np.array([[0, 0, -1], [1, 0, -1], [0, 1, -1]], dtype=object) % p
    # Columns are eigenvectors of a0^T with eigenvalues -1, i, -i.
    Q = np.array([[1, 1, 1], [-1, i, -i], [1, -1, -1]], dtype=object) % p
    Qi = mat_inv(Q, p)
    mu = [p - 1, i, (p - i) % p]
    D = matmul(matmul(Qi, a0.T, p), Q, p)
    diag_ok = True
    for r in range(3):
        for c in range(3):
            want = mu[r] if r == c else 0
            if int(D[r, c]) % p != want % p:
                diag_ok = False
    # Coordinate weights for n_ab in M'' -> D^{-1} M'' D and for form coefficients.
    weights = [(mu[c] * inv(mu[r], p)) % p for (r, c) in COORDS]
    return a0, Q, Qi, mu, weights, diag_ok, i


def tr3_value(M, p: int) -> int:
    s = 0
    for a, b, c in itertools.product(range(3), repeat=3):
        s += int(M[a, b]) * int(M[b, c]) * int(M[c, a])
    return s % p


def y_matrix_from_coords(y) -> np.ndarray:
    M = np.zeros((3, 3), dtype=object)
    for idx, (r, c) in enumerate(COORDS):
        M[r, c] = y[idx]
    return M


def coeff_vec_prod(u, v, w, p: int, factor: int = 1) -> np.ndarray:
    u = [int(x) % p for x in np.array(u, dtype=object).reshape(N)]
    v = [int(x) % p for x in np.array(v, dtype=object).reshape(N)]
    w = [int(x) % p for x in np.array(w, dtype=object).reshape(N)]
    out = np.zeros(len(MONOS), dtype=object)
    for a in range(N):
        if u[a] == 0:
            continue
        for b in range(N):
            if v[b] == 0:
                continue
            for c in range(N):
                if w[c] == 0:
                    continue
                mi = MONO_IDX[tuple(sorted((a, b, c)))]
                out[mi] = (int(out[mi]) + factor * u[a] * v[b] * w[c]) % p
    return out


def cube_vec(l, p: int) -> np.ndarray:
    return coeff_vec_prod(l, l, l, p)


def target_vec_short(p: int) -> np.ndarray:
    out = np.zeros(len(MONOS), dtype=object)
    # Directly expand tr(M''^3) in the canonical coordinate order.
    basis = []
    for j in range(N):
        E = np.zeros((3, 3), dtype=object)
        r, c = COORDS[j]
        E[r, c] = 1
        basis.append(E)
    for a, b, c in itertools.product(range(3), repeat=3):
        # monomial n_{ab} n_{bc} n_{ca}, if each coordinate is present.
        coords = [(a, b), (b, c), (c, a)]
        idxs = [COORDS.index(rc) for rc in coords]
        out[MONO_IDX[tuple(sorted(idxs))]] = (int(out[MONO_IDX[tuple(sorted(idxs))]]) + 1) % p
    return out


def target_vec_formula(p: int) -> np.ndarray:
    out = np.zeros(len(MONOS), dtype=object)
    def add(indices, coeff):
        out[MONO_IDX[tuple(sorted(indices))]] = (int(out[MONO_IDX[tuple(sorted(indices))]]) + coeff) % p
    # p^3
    add([0, 0, 0], 1); add([1, 1, 1], 1); add([2, 2, 2], 1)
    # pq^2: 3(n22+n33)n23 n32
    add([1, 3, 4], 3); add([2, 3, 4], 3)
    # pzw
    add([0, 7, 5], 3); add([1, 7, 5], 3)  # 3(n11+n22)n12 n21
    add([0, 6, 8], 3); add([2, 6, 8], 3)  # 3(n11+n33)n13 n31
    # qz^2 and qw^2
    add([4, 5, 6], 3)  # 3 n32 n21 n13
    add([3, 7, 8], 3)  # 3 n23 n12 n31
    return out % p


def extract_blocks(C, p: int):
    C = np.array(C, dtype=object).reshape(len(MONOS)) % p
    qz = np.zeros((2, 3), dtype=object)
    qw = np.zeros((2, 3), dtype=object)
    pzw = np.zeros((3, 2, 2), dtype=object)
    pq2 = np.zeros((3, 3), dtype=object)  # p index, q-square monomial index q0^2,q0q1,q1^2
    p3 = np.zeros(10, dtype=object)
    qidx, zidx, widx, pidx = GROUPS["q"], GROUPS["z"], GROUPS["w"], GROUPS["p"]
    for qi, qv in enumerate(qidx):
        for ci, pair in enumerate([(zidx[0], zidx[0]), (zidx[0], zidx[1]), (zidx[1], zidx[1])]):
            qz[qi, ci] = C[MONO_IDX[tuple(sorted((qv, pair[0], pair[1])))]]
        for ci, pair in enumerate([(widx[0], widx[0]), (widx[0], widx[1]), (widx[1], widx[1])]):
            qw[qi, ci] = C[MONO_IDX[tuple(sorted((qv, pair[0], pair[1])))]]
    for pi, pv in enumerate(pidx):
        for zi, zv in enumerate(zidx):
            for wi, wv in enumerate(widx):
                pzw[pi, zi, wi] = C[MONO_IDX[tuple(sorted((pv, zv, wv)))]]
        for ci, pair in enumerate([(qidx[0], qidx[0]), (qidx[0], qidx[1]), (qidx[1], qidx[1])]):
            pq2[pi, ci] = C[MONO_IDX[tuple(sorted((pv, pair[0], pair[1])))]]
    p_monos = list(itertools.combinations_with_replacement(pidx, 3))
    for j, m in enumerate(p_monos):
        p3[j] = C[MONO_IDX[m]]
    return {"qz2": qz % p, "qw2": qw % p, "pzw": pzw % p, "pq2": pq2 % p, "p3": p3 % p}


def discr_quad(row, p: int) -> int:
    a, b, c = [int(x) % p for x in row]
    return (b * b - 4 * a * c) % p


def is_square_quad(row, p: int) -> bool:
    row = [int(x) % p for x in row]
    return any(row) and discr_quad(row, p) == 0


def is_hyperbolic_rank_one_block(B, active_row: int, p: int) -> bool:
    B = np.array(B, dtype=object) % p
    if rank_mod(B, p) != 1:
        return False
    for r in range(2):
        row = [int(B[r, c]) % p for c in range(3)]
        if r == active_row:
            if not any(row):
                return False
            if discr_quad(row, p) == 0:
                return False
        else:
            if any(row):
                return False
    return True


def transform_stored_form_to_y(L_stored, Q, Qi, p: int) -> np.ndarray:
    # Stored L is paired as tr(L^T M).  Put A=L^T, A''=Q^{-1}AQ.
    L = np.array(L_stored, dtype=object) % p
    A = L.T % p
    A2 = matmul(matmul(Qi, A, p), Q, p)
    # coefficient of n_{rc}=M''_{rc} in tr(A''M'') is A''_{cr}.
    l = np.zeros(N, dtype=object)
    for idx, (r, c) in enumerate(COORDS):
        l[idx] = A2[c, r] % p
    return l


def form_eval_stored(L_stored, M_old, p: int) -> int:
    L = np.array(L_stored, dtype=object) % p
    M = np.array(M_old, dtype=object) % p
    return sum(int(L[r, c]) * int(M[r, c]) for r in range(3) for c in range(3)) % p


def y_eval(l_y, M_y, p: int) -> int:
    y = []
    for (r, c) in COORDS:
        y.append(int(M_y[r, c]) % p)
    return sum(int(l_y[j]) * y[j] for j in range(N)) % p


def orbit_cube(l, weights, p: int, steps: int = 4) -> np.ndarray:
    l = np.array(l, dtype=object).reshape(N) % p
    out = np.zeros(len(MONOS), dtype=object)
    for k in range(steps):
        lk = np.array([(int(l[j]) * pow(int(weights[j]), k, p)) % p for j in range(N)], dtype=object)
        out = (out + cube_vec(lk, p)) % p
    return out


def free_contribution(Tcols, weights, p: int) -> np.ndarray:
    Tcols = np.array(Tcols, dtype=object) % p
    out = np.zeros(len(MONOS), dtype=object)
    for k in range(4):
        scaled = np.zeros_like(Tcols)
        for j in range(N):
            sc = pow(int(weights[j]), k, p)
            for col in range(3):
                scaled[j, col] = (int(Tcols[j, col]) * sc) % p
        out = (out + coeff_vec_prod(scaled[:, 0], scaled[:, 1], scaled[:, 2], p, factor=3)) % p
    return out


def projective_equal(u, v, p: int):
    u = [int(x) % p for x in np.array(u, dtype=object).reshape(-1)]
    v = [int(x) % p for x in np.array(v, dtype=object).reshape(-1)]
    lam = None
    for a, b in zip(u, v):
        if a:
            cur = b * inv(a, p) % p
            if lam is None:
                lam = cur
            elif cur != lam:
                return False, None
        elif b:
            return False, None
    return True, (0 if lam is None else lam)


def find_orbits(forms, weights, p: int):
    forms = [np.array(f, dtype=object) % p for f in forms]
    used = [False] * len(forms)
    orbits = []
    powers_seen = []
    for j in range(len(forms)):
        if used[j]:
            continue
        cur = forms[j].copy()
        orbit = []
        orbit_lams = []
        for step in range(4):
            match = None
            lam_match = None
            for k, f in enumerate(forms):
                ok, lam = projective_equal(cur, f, p)
                if ok:
                    match = k
                    lam_match = lam
                    break
            if match is None:
                orbit.append(None)
                orbit_lams.append(None)
            else:
                if match not in orbit:
                    orbit.append(match)
                    orbit_lams.append(lam_match)
                    used[match] = True
            # Apply one generator to coefficients.
            cur = np.array([(int(cur[t]) * int(weights[t])) % p for t in range(N)], dtype=object)
        orbits.append(orbit)
        powers_seen.append(orbit_lams)
    return orbits, powers_seen


def support_by_group(l, p: int):
    l = [int(x) % p for x in l]
    return {g: [l[i] for i in idxs] for g, idxs in GROUPS.items()}


def main():
    p = 65521
    a0, Q, Qi, mu, weights, diag_ok, ii = q_basis(p)
    assert diag_ok
    target_direct = target_vec_short(p)
    target_formula = target_vec_formula(p)
    target_formula_ok = bool(np.array_equal(target_direct % p, target_formula % p))
    if not target_formula_ok:
        raise SystemExit("short tr(X^3) block formula failed")
    tb = extract_blocks(target_direct, p)
    target_tests = {
        "target_formula_ok": target_formula_ok,
        "qz2_rank": int(rank_mod(tb["qz2"], p)),
        "qw2_rank": int(rank_mod(tb["qw2"], p)),
        "qz2_hyperbolic_active_row_n32": bool(is_hyperbolic_rank_one_block(tb["qz2"], 1, p)),
        "qw2_hyperbolic_active_row_n23": bool(is_hyperbolic_rank_one_block(tb["qw2"], 0, p)),
        "qz2_q_direction": [int(x) for x in tb["qz2"][:, 1].reshape(-1)],
        "qw2_q_direction": [int(x) for x in tb["qw2"][:, 1].reshape(-1)],
        "q_directions_different": bool(tb["qz2"][0, 1] % p == 0 and tb["qz2"][1, 1] % p != 0 and tb["qw2"][0, 1] % p != 0 and tb["qw2"][1, 1] % p == 0),
        "qz2_block": [[int(x) for x in row] for row in tb["qz2"].tolist()],
        "qw2_block": [[int(x) for x in row] for row in tb["qw2"].tolist()],
    }
    if not (target_tests["qz2_hyperbolic_active_row_n32"] and target_tests["qw2_hyperbolic_active_row_n23"] and target_tests["q_directions_different"]):
        raise SystemExit("target qz/qw self-test failed")

    scheme = json.loads((WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json").read_text())
    cubes_y = [transform_stored_form_to_y(L, Q, Qi, p) for L in scheme["cubes"]]
    free_cols_y = []
    for key in ["U", "V", "W"]:
        free_cols_y.append(transform_stored_form_to_y(scheme["free_orbit_representatives"][0][key], Q, Qi, p))
    T0_y = np.stack(free_cols_y, axis=1) % p

    # Pairing self-test on random points.
    rng = random.Random(46046)
    pairing_mismatches = 0
    for _ in range(20):
        M_y = np.array([[rng.randrange(p) for _ in range(3)] for _ in range(3)], dtype=object)
        M_old = matmul(matmul(Q, M_y, p), Qi, p)
        for L, ly in list(zip(scheme["cubes"], cubes_y))[:5]:
            if form_eval_stored(L, M_old, p) != y_eval(ly, M_y, p):
                pairing_mismatches += 1
    pairing_ok = pairing_mismatches == 0
    if not pairing_ok:
        raise SystemExit("pairing transform failed")

    free_vec = free_contribution(T0_y, weights, p)
    cube_vec_sum = np.zeros(len(MONOS), dtype=object)
    for l in cubes_y:
        cube_vec_sum = (cube_vec_sum + cube_vec(l, p)) % p
    residual = (target_direct - free_vec) % p
    residual_matches_cubes = bool(np.array_equal(residual % p, cube_vec_sum % p))
    if not residual_matches_cubes:
        raise SystemExit("BILR residual/cube identity failed")

    cube_orbits, cube_orbit_lams = find_orbits(cubes_y, weights, p)
    # Remove possible repeated Nones and sort by first real index for stable output.
    cube_orbits_clean = []
    for orb in cube_orbits:
        clean = [int(x) for x in orb if x is not None]
        if clean:
            cube_orbits_clean.append(clean)
    cube_orbits_clean.sort(key=lambda x: (len(x), x[0]))

    orbit_profiles = []
    for orb in cube_orbits_clean:
        rep = cubes_y[orb[0]]
        prof = support_by_group(rep, p)
        orbit_profiles.append({
            "orbit": orb,
            "length": len(orb),
            "nonzero_counts_by_group": {g: int(sum(1 for x in vals if int(x) % p)) for g, vals in prof.items()},
            "support_kind": (
                "p_only" if all(int(x) % p == 0 for g in ["q", "z", "w"] for x in prof[g]) else
                "p_plus_q" if all(int(x) % p == 0 for g in ["z", "w"] for x in prof[g]) else
                "general_size4"
            ),
        })

    rb = extract_blocks(residual, p)
    residual_block_summary = {
        "qz2_rank": int(rank_mod(rb["qz2"], p)),
        "qw2_rank": int(rank_mod(rb["qw2"], p)),
        "qz2_block": [[int(x) for x in row] for row in rb["qz2"].tolist()],
        "qw2_block": [[int(x) for x in row] for row in rb["qw2"].tolist()],
    }

    # Verify the 11 BILR cubes by orbit-summing representatives: 1+2+4+4.
    orbit_sum = np.zeros(len(MONOS), dtype=object)
    for rec in orbit_profiles:
        rep = cubes_y[rec["orbit"][0]]
        orbit_sum = (orbit_sum + orbit_cube(rep, weights, p, steps=rec["length"])) % p
    orbit_sum_matches = bool(np.array_equal(orbit_sum % p, residual % p))
    if not orbit_sum_matches:
        raise SystemExit("orbit-sum reconstruction failed")

    # Record formula coefficient list in readable block form.
    formula_blocks = {
        "p3": "n11^3+n22^3+n33^3",
        "pq2": "3(n22+n33)n23 n32",
        "pzw": "3(n11+n22)n12 n21 + 3(n11+n33)n13 n31",
        "qz2": "3 n32 n21 n13",
        "qw2": "3 n23 n12 n31",
    }

    result = {
        "prime": p,
        "imag_unit": int(ii),
        "rule": "stored L -> A=L^T; Q^{-1}a0^TQ=D; A2=Q^{-1}AQ; M2=Q^{-1}MQ; form coefficient for n_ab is A2_ba; both coefficient orbits and variable coordinates use weight mu_b/mu_a",
        "Q": [[int(x) for x in row] for row in Q.tolist()],
        "mu": [int(x) for x in mu],
        "coords": {str(j): {"entry": [int(a), int(b)], "group": next(g for g, idxs in GROUPS.items() if j in idxs), "weight": int(weights[j])} for j, (a, b) in enumerate(COORDS)},
        "target_formula_blocks": formula_blocks,
        "target_self_tests": target_tests,
        "pairing_random_tests": {"random_points": 20, "forms_per_point": 5, "mismatches": pairing_mismatches, "ok": pairing_ok},
        "bilr_positive_control": {
            "residual_matches_sum_of_11_cubes": residual_matches_cubes,
            "cube_orbits": cube_orbits_clean,
            "orbit_lengths_sorted": sorted([len(o) for o in cube_orbits_clean]),
            "orbit_profiles": orbit_profiles,
            "orbit_sum_matches_residual": orbit_sum_matches,
            "residual_blocks": residual_block_summary,
        },
        "interpretation": "This file fixes the Z4 coordinate convention and validates the block instrument. It is not a rank-22 construction or nonexistence theorem.",
    }
    out = OUT / "qbasis_selftest.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "out": str(out),
        "target_self_tests": target_tests,
        "orbit_lengths_sorted": result["bilr_positive_control"]["orbit_lengths_sorted"],
        "residual_matches_sum_of_11_cubes": residual_matches_cubes,
        "orbit_sum_matches_residual": orbit_sum_matches,
    }, indent=2))


if __name__ == "__main__":
    main()
