#!/usr/bin/env python3
r"""analysis certificate for the order-7 sandwich-invariant rank-22 family over F2.

The script produces a compact replayable certificate for the following finite-family
statement.

Let g be the order-7 sandwich symmetry phi_{F,F,F} over F2 in this investigation's
QMM covector convention.  No rank-22 F2 decomposition of T_<3,3,3> whose 22
rank-one UV generators are permuted by <g> exists.

Only linear algebra over F2 is used.  The script checks the action convention by
verifying g_E T_flat = T_flat h_W exactly.  It then enumerates all nonzero
rank-one 9x9 UV points (261121) and their <g>-orbits.

Orbit skeletons for 22 terms are (free 7-orbits, fixed terms):
(0,22), (1,15), (2,8), (3,1).  The first two have UV-rank <22 because the fixed
rank-one locus spans only 9 dimensions.  Type (2,8) fails by the fixed-part
projection dimension budget.  For type (3,1), a full-rank candidate must use
three rank-7 free orbits.  The necessary fixed-projection condition is
sigma(O_j) in L0+<p> for the fixed summand p, where sigma=sum_{k=0}^6 g^k and
L0=L∩Fix_E.  The exact enumeration shows that every rank-7 orbit satisfying
this condition has sigma(O_j)=p, never p+ell with nonzero ell in L0.  Hence the
fixed part of such an S is only <p>, whereas L⊂S would force L0⊂S.  Therefore
type (3,1) also fails.
"""

from __future__ import annotations

import json
import time
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np


def gf2_rref(M):
    M = np.array(M, dtype=np.uint8, copy=True) & 1
    rows, cols = M.shape
    pivots = []
    r = 0
    for c in range(cols):
        found = -1
        for i in range(r, rows):
            if M[i, c]:
                found = i
                break
        if found < 0:
            continue
        if found != r:
            M[[r, found]] = M[[found, r]]
        pivots.append(c)
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        r += 1
        if r == rows:
            break
    return M[:r], r, pivots


def gf2_rank(M):
    return 0 if np.asarray(M).size == 0 else gf2_rref(M)[1]


def gf2_nullspace(M):
    M = np.array(M, dtype=np.uint8, copy=True) & 1
    rows, cols = M.shape
    rref, rank, pivots = gf2_rref(M)
    pivset = set(pivots)
    basis = []
    for f in [c for c in range(cols) if c not in pivset]:
        v = np.zeros(cols, dtype=np.uint8)
        v[f] = 1
        for i, p in enumerate(pivots):
            v[p] = rref[i, f]
        basis.append(v)
    return np.array(basis, dtype=np.uint8) if basis else np.zeros((0, cols), dtype=np.uint8)


def gf2_inv(M):
    M = np.array(M, dtype=np.uint8, copy=True) & 1
    n = M.shape[0]
    A = np.hstack([M, np.eye(n, dtype=np.uint8)])
    for c in range(n):
        found = -1
        for i in range(c, n):
            if A[i, c]:
                found = i
                break
        if found < 0:
            raise ValueError("singular matrix")
        if found != c:
            A[[c, found]] = A[[found, c]]
        for i in range(n):
            if i != c and A[i, c]:
                A[i] ^= A[c]
    return A[:, n:]


def gf2_matpow(M, k):
    M = np.array(M, dtype=np.uint8, copy=True) & 1
    n = M.shape[0]
    out = np.eye(n, dtype=np.uint8)
    base = M
    while k:
        if k & 1:
            out = (out @ base) & 1
        base = (base @ base) & 1
        k >>= 1
    return out


def intersection_dim(A, B):
    return gf2_rank(A) + gf2_rank(B) - gf2_rank(np.vstack([A, B]))


def span_all_ints(gens):
    s = {0}
    for g in gens:
        s |= {x ^ g for x in list(s)}
    return s


def fixed_coord(v, pivots):
    c = 0
    for i, p in enumerate(pivots):
        if v[p]:
            c |= 1 << i
    return c


def build_T333_flat():
    T = np.zeros((81, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[(3 * i + j) * 9 + (3 * j + k), 3 * k + i] = 1
    return T


def rowmajor_action(L, R):
    """row-major vec(L X R) = kron(L,R^T) vec_row(X)."""
    return np.kron(L, R.T).astype(np.uint8) & 1


def sandwich_actions(F):
    """Finite action compatible with the verified QMM covector convention."""
    Fi = gf2_inv(F)
    M9 = rowmajor_action(F.T & 1, Fi.T & 1)  # X -> F^T X F^{-T}; matrix kron(F^T,F^{-1})
    hW = rowmajor_action(Fi, F)              # X -> F^{-1} X F; matrix kron(F^{-1},F^T)
    gE = np.kron(M9, M9).astype(np.uint8) & 1
    return M9, gE, hW


def quotient_Q(T):
    Q = gf2_nullspace(T.T)
    assert Q.shape == (72, 81)
    assert np.all(((Q @ T) & 1) == 0)
    return Q


def right_inverse_Q(Q):
    _, _, pivots = gf2_rref(Q)
    inv = gf2_inv(Q[:, pivots])
    Qp = np.zeros((81, 72), dtype=np.uint8)
    for i, p in enumerate(pivots):
        Qp[p] = inv[i]
    assert np.array_equal((Q @ Qp) & 1, np.eye(72, dtype=np.uint8))
    return Qp


def enumerate_rank_one():
    pts = np.zeros(((2**9 - 1) ** 2, 81), dtype=np.uint8)
    vecs = [None] + [np.array([(z >> b) & 1 for b in range(9)], dtype=np.uint8) for z in range(1, 512)]
    t = 0
    for u in range(1, 512):
        for v in range(1, 512):
            pts[t] = np.outer(vecs[u], vecs[v]).reshape(-1)
            t += 1
    return pts


def classify_orbits(gE, pts, order=7):
    idx = {pts[i].tobytes(): i for i in range(len(pts))}
    seen = np.zeros(len(pts), dtype=bool)
    fixed = []
    free = []
    for i in range(len(pts)):
        if seen[i]:
            continue
        cur = pts[i]
        orb = [i]
        seen[i] = True
        for _ in range(order - 1):
            cur = (gE @ cur) & 1
            j = idx[cur.tobytes()]
            if seen[j]:
                break
            seen[j] = True
            orb.append(j)
        if len(orb) == 1:
            fixed.append(i)
        else:
            assert len(orb) == order
            free.append(orb)
    return fixed, free


def main():
    t0 = time.time()
    out_dir = Path("data/order7_exhaustive")
    out_dir.mkdir(parents=True, exist_ok=True)

    T = build_T333_flat()
    L = T.T & 1
    Q = quotient_Q(T)
    Qp = right_inverse_Q(Q)

    F7 = np.array([[0, 0, 1], [1, 0, 1], [0, 1, 0]], dtype=np.uint8)
    M9, gE, hW = sandwich_actions(F7)
    gbar = (Q @ gE @ Qp) & 1
    action_ok = bool(np.array_equal((gE @ T) & 1, (T @ hW) & 1))
    if not action_ok:
        raise AssertionError("sandwich action does not preserve T")

    order_checks = {
        "F7": bool(np.array_equal(gf2_matpow(F7, 7), np.eye(3, dtype=np.uint8))),
        "M9": bool(np.array_equal(gf2_matpow(M9, 7), np.eye(9, dtype=np.uint8))),
        "gE": bool(np.array_equal(gf2_matpow(gE, 7), np.eye(81, dtype=np.uint8))),
        "hW": bool(np.array_equal(gf2_matpow(hW, 7), np.eye(9, dtype=np.uint8))),
        "gbar": bool(np.array_equal(gf2_matpow(gbar, 7), np.eye(72, dtype=np.uint8))),
    }

    fixE = gf2_nullspace((gE ^ np.eye(81, dtype=np.uint8)) & 1)
    _, fixE_dim, fix_pivots = gf2_rref(fixE)
    fixQ_dim = gf2_nullspace((gbar ^ np.eye(72, dtype=np.uint8)) & 1).shape[0]
    L0 = (gf2_nullspace((hW ^ np.eye(9, dtype=np.uint8)) & 1) @ L) & 1
    L0_basis, L0_dim, _ = gf2_rref(L0)
    L0_coords = span_all_ints([fixed_coord(v, fix_pivots) for v in L0_basis])

    sigma = np.zeros((81, 81), dtype=np.uint8)
    pwr = np.eye(81, dtype=np.uint8)
    for _ in range(7):
        sigma ^= pwr
        pwr = (gE @ pwr) & 1
    sigma_checks = {
        "rank": int(gf2_rank(sigma)),
        "idempotent": bool(np.array_equal((sigma @ sigma) & 1, sigma)),
        "image_fixed_rank": int(gf2_rank(((gE ^ np.eye(81, dtype=np.uint8)) @ sigma) & 1)),
    }

    pts = enumerate_rank_one()
    fixed_idx, free_orbits = classify_orbits(gE, pts, 7)
    fixed_pts = pts[fixed_idx]
    fixed_span_rank = gf2_rank(fixed_pts)
    fixed_L_intersection = intersection_dim(fixed_pts, L)
    fixed_L0_intersection = intersection_dim(fixed_pts, L0_basis)
    fixed_coords = {fixed_coord(pts[i], fix_pivots): local for local, i in enumerate(fixed_idx)}

    orbit_profile = Counter()
    type31_by_fixed = {local: Counter() for local in range(len(fixed_idx))}
    all_rank7_good = True
    all_rank7_good_sigma_equal_p = True
    for orb in free_orbits:
        X = pts[orb]
        xrank = gf2_rank(X)
        sig = np.bitwise_xor.reduce(X, axis=0).astype(np.uint8)
        # projector identity for replay protection
        sig2 = (sigma @ X[0]) & 1
        if not np.array_equal(sig, sig2):
            raise AssertionError("orbit sum differs from sigma projector")
        sc = fixed_coord(sig, fix_pivots)
        in_L0 = sc in L0_coords
        in_fixed_rank_one = sc in fixed_coords
        in_fixed_plus_L0 = []
        for pc, local in fixed_coords.items():
            if (sc ^ pc) in L0_coords:
                in_fixed_plus_L0.append((local, sc ^ pc))
        tag = "L0" if in_L0 else ("fixed_rank_one_plus_L0" if in_fixed_plus_L0 else "other")
        orbit_profile[(xrank, tag, int(sc == 0), int(in_fixed_rank_one), len(in_fixed_plus_L0))] += 1
        for local, l0part in in_fixed_plus_L0:
            if xrank == 7:
                if l0part == 0:
                    type31_by_fixed[local]["rank7_sigma_equals_p"] += 1
                else:
                    type31_by_fixed[local]["rank7_sigma_equals_p_plus_nonzero_L0"] += 1
                    all_rank7_good_sigma_equal_p = False
            else:
                type31_by_fixed[local][f"rank{xrank}_not_full_orbit"] += 1
        if xrank == 7 and in_fixed_plus_L0 and not in_fixed_rank_one:
            all_rank7_good = False

    type31_hist = Counter()
    per_fixed = []
    for local in range(len(fixed_idx)):
        c = type31_by_fixed[local]
        rec = {
            "fixed_local": local,
            "filtered_orbits_total": int(sum(c.values())),
            "rank7_sigma_equals_p": int(c.get("rank7_sigma_equals_p", 0)),
            "rank7_sigma_equals_p_plus_nonzero_L0": int(c.get("rank7_sigma_equals_p_plus_nonzero_L0", 0)),
            "lower_rank_filtered_orbits": int(sum(v for k, v in c.items() if k.startswith("rank") and k != "rank7_sigma_equals_p" and k != "rank7_sigma_equals_p_plus_nonzero_L0")),
            "raw_counter": dict(c),
        }
        per_fixed.append(rec)
        type31_hist[(rec["filtered_orbits_total"], rec["rank7_sigma_equals_p"], rec["rank7_sigma_equals_p_plus_nonzero_L0"], rec["lower_rank_filtered_orbits"])] += 1

    skeletons = []
    for free_count, fixed_terms in [(0, 22), (1, 15), (2, 8), (3, 1)]:
        max_xrank = min(fixed_terms, fixed_span_rank) + 7 * free_count
        if free_count in (0, 1):
            impossible = max_xrank < 22
            reason = f"fixed rank-one span has dimension {fixed_span_rank}, so UV-rank <= min({fixed_terms},{fixed_span_rank})+7*{free_count}={max_xrank}<22"
        elif free_count == 2:
            needed = fixed_terms + L0_dim
            available = fixed_terms + free_count
            impossible = needed > available
            reason = f"full UV-rank would force {fixed_terms} independent fixed rank-one summands P; P∩L0=0, so S^g must contain P+L0 of dimension {needed}, but sigma(S) is generated by {fixed_terms} fixed summands plus {free_count} orbit sums, dimension at most {available}"
        else:
            impossible = all_rank7_good_sigma_equal_p and fixed_L0_intersection == 0 and L0_dim > 0
            reason = f"full UV-rank forces all three free orbits to have rank 7; enumeration shows every rank-7 orbit with sigma(O) in L0+<p> has sigma(O)=p, so sigma(S)⊆<p>; since p is a fixed rank-one point and fixed-rank-one span intersects L0 in dimension {fixed_L0_intersection}, L0 (dim {L0_dim}) is not contained in S"
        skeletons.append({
            "free_orbits": free_count,
            "fixed_terms": fixed_terms,
            "max_xrank_bound": int(max_xrank),
            "excluded": bool(impossible),
            "reason": reason,
        })

    conclusion_ok = all(s["excluded"] for s in skeletons)
    results = {
        "purpose": "Replayable linear-algebra certificate excluding order-7 sandwich-invariant rank-22 UV decompositions over F2.",
        "field": "F2",
        "F7_matrix": F7.astype(int).tolist(),
        "action_convention": {
            "U_and_V": "row-major covector action vec(F^T X F^{-T}) = kron(F^T,F^{-1}) vec_row(X)",
            "W": "row-major action vec(F^{-1} X F) = kron(F^{-1},F^T) vec_row(X)",
            "gE_T_equals_T_hW": action_ok,
            "order_checks": order_checks,
        },
        "fixed_spaces": {
            "Fix_E_dim": int(fixE_dim),
            "Fix_E_mod_L_dim": int(fixQ_dim),
            "L0_dim": int(L0_dim),
            "sigma_projector": sigma_checks,
        },
        "rank_one_orbits": {
            "rank_one_total": int(len(pts)),
            "fixed_count": int(len(fixed_idx)),
            "free_orbit_count": int(len(free_orbits)),
            "total_check": int(len(fixed_idx) + 7 * len(free_orbits)),
            "fixed_rank_one_span_rank": int(fixed_span_rank),
            "fixed_rank_one_span_intersection_L": int(fixed_L_intersection),
            "fixed_rank_one_span_intersection_L0": int(fixed_L0_intersection),
            "free_orbit_profile": {str(k): int(v) for k, v in sorted(orbit_profile.items())},
        },
        "type_3_1_filter": {
            "necessary_condition": "for the fixed summand p, each full-rank free orbit must satisfy sigma(O) in L0+<p>; otherwise the fixed projection cannot contain L0+<p>",
            "histogram_over_49_fixed_points": {str(k): int(v) for k, v in sorted(type31_hist.items())},
            "per_fixed": per_fixed,
            "rank7_filtered_orbits_always_have_sigma_equal_p": bool(all_rank7_good_sigma_equal_p),
        },
        "skeletons": skeletons,
        "theorem_status": "proved_exclusion_for_this_order7_sandwich_family" if conclusion_ok else "not_excluded_by_this_certificate",
        "supersedes": [
            "data/symmetry_search/orbit_search_results.json used a non-preserving action convention and random sampling only",
            "scripts/order7_exhaustive_fast.py attempted unnecessary triple enumeration and timed out",
        ],
        "elapsed_sec": time.time() - t0,
    }

    out = out_dir / "order7_family_certificate.json"
    out.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps({
        "action_ok": action_ok,
        "fixed_spaces": results["fixed_spaces"],
        "rank_one_orbits": results["rank_one_orbits"],
        "type31_histogram": results["type_3_1_filter"]["histogram_over_49_fixed_points"],
        "skeletons": skeletons,
        "theorem_status": results["theorem_status"],
        "out": str(out),
        "elapsed_sec": results["elapsed_sec"],
    }, indent=2))


if __name__ == "__main__":
    main()
