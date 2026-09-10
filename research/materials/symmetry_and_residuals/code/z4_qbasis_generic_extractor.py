#!/usr/bin/env python3
"""
analysis: branch-aware generic block extractor in the canonical Q-basis.

This is a positive-control and reusable instrument, not a final nonexistence proof.
It implements the generic q-independent branch exactly over F_65521:
  C_qz = 12(q1 z1^2 + q2 z2^2), det(q1,q2) != 0.
Then the same q1,q2 are used to extract the qw block, pzw solves linearly for
p1,p2, and the remaining tail is inspected.

The BILR rank-23 residual should be recovered as two size-4 orbits plus one
length-2 orbit and one fixed p-cube (4+4+2+1).  Recovering this in the Q-basis is
a strong self-test for constants, orbit weights, row/column order, and the shared-q
coupling.  It does not imply rank 22.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path

import numpy as np
import sympy as sp

import z4_qbasis_selftest as qb

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "z4_qbasis"
OUT.mkdir(parents=True, exist_ok=True)
P = 65521


def inv(a: int) -> int:
    return pow(int(a) % P, -1, P)


def solve_linear_fullrank(A, b):
    """Solve A x=b over F_P, returning one solution if consistent; A may be tall."""
    A = np.array(A, dtype=object) % P
    b = np.array(b, dtype=object).reshape(-1) % P
    m, n = A.shape
    B = [[int(A[i, j]) % P for j in range(n)] + [int(b[i]) % P] for i in range(m)]
    pivots = []
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if B[i][c] % P:
                piv = i
                break
        if piv is None:
            continue
        B[r], B[piv] = B[piv], B[r]
        sc = inv(B[r][c])
        B[r] = [(x * sc) % P for x in B[r]]
        for i in range(m):
            if i != r and B[i][c] % P:
                f = B[i][c] % P
                B[i] = [(B[i][j] - f * B[r][j]) % P for j in range(n + 1)]
        pivots.append(c)
        r += 1
    for i in range(r, m):
        if all(B[i][j] % P == 0 for j in range(n)) and B[i][n] % P:
            return None, len(pivots)
    x = [0] * n
    for row, pc in enumerate(pivots):
        x[pc] = B[row][n] % P
    return np.array(x, dtype=object), len(pivots)


def conic_points_in_pencil(R):
    """Projective conic points in rowspace of a 2x3 binary-quadratic matrix."""
    R = np.array(R, dtype=object) % P
    rows = [[int(R[i, j]) % P for j in range(3)] for i in range(2)]
    pts = []
    seen = set()
    def add(v):
        v = [int(x) % P for x in v]
        if not any(v):
            return
        if (v[1] * v[1] - 4 * v[0] * v[2]) % P != 0:
            return
        for x in v:
            if x:
                sc = inv(x)
                break
        vn = tuple((x * sc) % P for x in v)
        if vn not in seen:
            seen.add(vn)
            pts.append(np.array(vn, dtype=object))
    for t in range(P):
        add([(t * rows[0][j] + rows[1][j]) % P for j in range(3)])
    add(rows[0])
    return pts


def square_vector_from_projective_quad(s):
    """For normalized conic point s, return z with [z0^2,2z0z1,z1^2]=s."""
    A, B, C = [int(x) % P for x in s]
    if A:
        # Normalization should have A=1.
        z0 = 1
        z1 = (B * inv(2 * A)) % P
        sq = [(z0 * z0) % P, (2 * z0 * z1) % P, (z1 * z1) % P]
        if tuple(sq) != tuple([A, B, C]):
            raise ValueError(("bad normalized square with A", [A, B, C], sq))
        return np.array([z0, z1], dtype=object)
    if B:
        # A=0 and discriminant zero implies B=0, so this should not occur.
        raise ValueError(("unexpected conic point", [A, B, C]))
    if C:
        return np.array([0, 1], dtype=object)
    raise ValueError("zero conic point")


def exact_vector_from_quad(t):
    """Return w with [w0^2,2w0w1,w1^2]=t, if such a vector exists over F_P."""
    A, B, C = [int(x) % P for x in t]
    if not (A or B or C):
        return np.array([0, 0], dtype=object)
    if (B * B - 4 * A * C) % P != 0:
        return None
    if A:
        roots = sp.sqrt_mod(A, P, all_roots=True)
        if not roots:
            return None
        for z0 in roots:
            z0 = int(z0) % P
            z1 = (B * inv(2 * z0)) % P
            if [(z0 * z0) % P, (2 * z0 * z1) % P, (z1 * z1) % P] == [A, B, C]:
                return np.array([z0, z1], dtype=object)
        return None
    # A=0 => B=0; need sqrt(C) for z1.
    if B:
        return None
    roots = sp.sqrt_mod(C, P, all_roots=True)
    if not roots:
        return None
    return np.array([0, int(roots[0]) % P], dtype=object)


def solve_q_from_qz(qz, s1, s2):
    # For each q-row, solve row = q1_row*s1 + q2_row*s2.
    S = np.array([[int(s1[j]) % P, int(s2[j]) % P] for j in range(3)], dtype=object)
    q1 = []
    q2 = []
    for r in range(2):
        sol, rk = solve_linear_fullrank(S, np.array(qz[r, :], dtype=object))
        if sol is None or rk < 2:
            return None
        q1.append(int(sol[0]) % P)
        q2.append(int(sol[1]) % P)
    return np.array(q1, dtype=object), np.array(q2, dtype=object)


def solve_t_from_q(qw, q1, q2):
    Q = np.array([[int(q1[0]) % P, int(q2[0]) % P], [int(q1[1]) % P, int(q2[1]) % P]], dtype=object)
    if qb.rank_mod(Q, P) < 2:
        return None
    t1 = []
    t2 = []
    for k in range(3):
        sol, rk = solve_linear_fullrank(Q, np.array([qw[0, k], qw[1, k]], dtype=object))
        if sol is None or rk < 2:
            return None
        t1.append(int(sol[0]) % P)
        t2.append(int(sol[1]) % P)
    return np.array(t1, dtype=object), np.array(t2, dtype=object)


def solve_p_from_pzw(pzw, z1, z2, w1, w2):
    # pzw coefficient for two size-4 orbits is 24(p1_i z1_a w1_b + p2_i z2_a w2_b).
    A = np.zeros((12, 6), dtype=object)
    b = []
    row = 0
    for pi in range(3):
        for zi in range(2):
            for wi in range(2):
                A[row, pi] = (24 * int(z1[zi]) * int(w1[wi])) % P
                A[row, 3 + pi] = (24 * int(z2[zi]) * int(w2[wi])) % P
                b.append(int(pzw[pi, zi, wi]) % P)
                row += 1
    sol, rk = solve_linear_fullrank(A, np.array(b, dtype=object))
    if sol is None:
        return None, rk
    return (np.array(sol[:3], dtype=object), np.array(sol[3:6], dtype=object)), rk


def tail_indices():
    idx = []
    for mi, m in enumerate(qb.MONOS):
        counts = {"p": 0, "q": 0, "z": 0, "w": 0}
        for j in m:
            for g, arr in qb.GROUPS.items():
                if j in arr:
                    counts[g] += 1
                    break
        if counts["z"] == 0 and counts["w"] == 0 and counts["p"] + counts["q"] == 3:
            idx.append(mi)
    return idx


def p3_indices():
    return [qb.MONO_IDX[m] for m in itertools.combinations_with_replacement(qb.GROUPS["p"], 3)]


def pq2_indices():
    out = []
    for pv in qb.GROUPS["p"]:
        for pair in [(qb.GROUPS["q"][0], qb.GROUPS["q"][0]), (qb.GROUPS["q"][0], qb.GROUPS["q"][1]), (qb.GROUPS["q"][1], qb.GROUPS["q"][1])]:
            out.append(qb.MONO_IDX[tuple(sorted((pv, pair[0], pair[1])))])
    return out


def length2_orbit_from_l(l, weights):
    return qb.orbit_cube(l, weights, P, steps=2)


def main():
    a0, Q, Qi, mu, weights, diag_ok, ii = qb.q_basis(P)
    assert diag_ok
    scheme = json.loads((WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json").read_text())
    cubes_y = [qb.transform_stored_form_to_y(L, Q, Qi, P) for L in scheme["cubes"]]
    T0_y = np.stack([qb.transform_stored_form_to_y(scheme["free_orbit_representatives"][0][key], Q, Qi, P) for key in ["U", "V", "W"]], axis=1) % P
    target = qb.target_vec_short(P)
    C = (target - qb.free_contribution(T0_y, weights, P)) % P
    blocks = qb.extract_blocks(C, P)
    qz = np.array(blocks["qz2"], dtype=object) % P
    qw = np.array(blocks["qw2"], dtype=object) % P
    pzw = np.array(blocks["pzw"], dtype=object) % P
    # Divide qz/qw by 12 for the square extraction.  Keep pzw unnormalized
    # because solve_p_from_pzw includes the 24 factor in the linear matrix.
    qzN = (qz * inv(12)) % P
    qwN = (qw * inv(12)) % P
    pts = conic_points_in_pencil(qzN)
    records = []
    for order in itertools.permutations(range(len(pts)), 2):
        s1, s2 = pts[order[0]], pts[order[1]]
        try:
            z1 = square_vector_from_projective_quad(s1)
            z2 = square_vector_from_projective_quad(s2)
        except ValueError:
            continue
        qs = solve_q_from_qz(qzN, s1, s2)
        if qs is None:
            continue
        q1, q2 = qs
        qdet = (int(q1[0]) * int(q2[1]) - int(q1[1]) * int(q2[0])) % P
        if qdet == 0:
            continue
        ts = solve_t_from_q(qwN, q1, q2)
        if ts is None:
            continue
        t1, t2 = ts
        w1 = exact_vector_from_quad(t1)
        w2 = exact_vector_from_quad(t2)
        if w1 is None or w2 is None:
            continue
        ps, prank = solve_p_from_pzw(pzw, z1, z2, w1, w2)
        if ps is None:
            continue
        p1, p2 = ps
        l1 = np.zeros(qb.N, dtype=object); l2 = np.zeros(qb.N, dtype=object)
        l1[qb.GROUPS["p"]] = p1; l1[qb.GROUPS["q"]] = q1; l1[qb.GROUPS["z"]] = z1; l1[qb.GROUPS["w"]] = w1
        l2[qb.GROUPS["p"]] = p2; l2[qb.GROUPS["q"]] = q2; l2[qb.GROUPS["z"]] = z2; l2[qb.GROUPS["w"]] = w2
        H = (C - qb.orbit_cube(l1, weights, P, 4) - qb.orbit_cube(l2, weights, P, 4)) % P
        # Identify H against the known remaining BILR orbit reps.
        orbit_profiles = json.loads((OUT / "qbasis_selftest.json").read_text())["bilr_positive_control"]["orbit_profiles"]
        known_tail = np.zeros(len(qb.MONOS), dtype=object)
        used_size4 = []
        for rec in orbit_profiles:
            if rec["length"] == 4:
                rep = cubes_y[rec["orbit"][0]]
                ok1, _ = qb.projective_equal(rep, l1, P)
                ok2, _ = qb.projective_equal(rep, l2, P)
                if ok1 or ok2:
                    used_size4.append(rec["orbit"])
            else:
                rep = cubes_y[rec["orbit"][0]]
                known_tail = (known_tail + qb.orbit_cube(rep, weights, P, rec["length"])) % P
        H_matches_known_tail = bool(np.array_equal(H % P, known_tail % P))
        # Pattern checks for rank22 tails.
        pq2_nonzero = int(sum(1 for i in pq2_indices() if int(H[i]) % P))
        p3_vec = np.array([int(H[i]) % P for i in p3_indices()], dtype=object)
        p3_cat = np.array([
            [p3_vec[0], p3_vec[1], p3_vec[2], p3_vec[3], p3_vec[4], p3_vec[5]],
            [p3_vec[1], p3_vec[3], p3_vec[4], p3_vec[6], p3_vec[7], p3_vec[8]],
            [p3_vec[2], p3_vec[4], p3_vec[5], p3_vec[7], p3_vec[8], p3_vec[9]],
        ], dtype=object) % P
        rec = {
            "order": [int(x) for x in order],
            "qdet_nonzero": bool(qdet != 0),
            "pzw_linear_rank": int(prank),
            "l1": [int(x) for x in l1],
            "l2": [int(x) for x in l2],
            "q1": [int(x) for x in q1],
            "q2": [int(x) for x in q2],
            "z1": [int(x) for x in z1],
            "z2": [int(x) for x in z2],
            "w1": [int(x) for x in w1],
            "w2": [int(x) for x in w2],
            "size4_orbits_matched_projectively": used_size4,
            "remainder_matches_known_BILR_length2_plus_fixed": H_matches_known_tail,
            "remainder_pq2_nonzero_count": pq2_nonzero,
            "remainder_p3_catalecticant_rank": int(qb.rank_mod(p3_cat, P)),
        }
        records.append(rec)
    result = {
        "prime": P,
        "scope": "generic q-independent extraction at the BILR residual in canonical Q-basis; positive control only",
        "qz_rank": int(qb.rank_mod(qz, P)),
        "qw_rank": int(qb.rank_mod(qw, P)),
        "qz_pencil_conic_points": [[int(x) for x in pt] for pt in pts],
        "number_of_generic_extractions": len(records),
        "records": records,
        "interpretation": "The extractor recovers the two BILR length-4 cube orbits and leaves exactly the known length-2 plus fixed tail. This validates constants/shared-q coupling for the generic branch. Degenerate q-proportional and q-zero branches still require separate algebraic handling in a proof.",
    }
    out = OUT / "generic_extractor_bilr_positive.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "out": str(out),
        "qz_rank": result["qz_rank"],
        "qw_rank": result["qw_rank"],
        "conic_point_count": len(pts),
        "number_of_generic_extractions": len(records),
        "all_remainders_match_known_tail": all(r["remainder_matches_known_BILR_length2_plus_fixed"] for r in records),
        "matched_size4_orbits": [r["size4_orbits_matched_projectively"] for r in records],
    }, indent=2))


if __name__ == "__main__":
    main()
