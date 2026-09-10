#!/usr/bin/env python3
r"""analysis fast exhaustive order-7 sandwich family over F2.

This is the optimized/replayable version of order7_exhaustive_sandwich.py.
It uses the corrected QMM finite sandwich convention and exact bitset GF(2)
ranks to exhaust the only possible order-7 orbit skeleton (3 free 7-orbits +
1 fixed rank-one summand).

The finite action is checked by g_E T = T h_W before any search.  A rank-22
solution in the canonical UV-span formulation would be exactly 22 rank-one UV
columns X with L <= span(X).  W is then recovered by solving X^T W = T.
"""

from __future__ import annotations

import itertools
import json
import time
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np


# ---------- GF(2) linear algebra on arrays ----------

def gf2_rref(M: np.ndarray):
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


def gf2_rank(M: np.ndarray) -> int:
    if np.asarray(M).size == 0:
        return 0
    return gf2_rref(M)[1]


def gf2_nullspace(M: np.ndarray) -> np.ndarray:
    M = np.array(M, dtype=np.uint8, copy=True) & 1
    rows, cols = M.shape
    rref, rank, pivots = gf2_rref(M)
    pivset = set(pivots)
    free = [c for c in range(cols) if c not in pivset]
    basis = []
    for f in free:
        v = np.zeros(cols, dtype=np.uint8)
        v[f] = 1
        for i, p in enumerate(pivots):
            v[p] = rref[i, f]
        basis.append(v)
    return np.array(basis, dtype=np.uint8) if basis else np.zeros((0, cols), dtype=np.uint8)


def gf2_inv(M: np.ndarray) -> np.ndarray:
    M = np.array(M, dtype=np.uint8, copy=True) & 1
    n = M.shape[0]
    aug = np.hstack([M, np.eye(n, dtype=np.uint8)])
    for c in range(n):
        found = -1
        for i in range(c, n):
            if aug[i, c]:
                found = i
                break
        if found < 0:
            raise ValueError("singular")
        if found != c:
            aug[[c, found]] = aug[[found, c]]
        for i in range(n):
            if i != c and aug[i, c]:
                aug[i] ^= aug[c]
    return aug[:, n:]


def gf2_matpow(M: np.ndarray, k: int) -> np.ndarray:
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


def intersection_dim(A: np.ndarray, B: np.ndarray) -> int:
    return gf2_rank(A) + gf2_rank(B) - gf2_rank(np.vstack([A, B]))


# ---------- fast bit ranks ----------

def vec_to_int(v: np.ndarray) -> int:
    out = 0
    # nonzero loop is much faster than checking all bits for sparse-ish rank-one rows.
    for b in np.flatnonzero(v):
        out |= 1 << int(b)
    return out


def rows_to_ints(M: np.ndarray) -> list[int]:
    return [vec_to_int(row) for row in np.asarray(M, dtype=np.uint8)]


def rank_int(rows: list[int] | tuple[int, ...]) -> int:
    basis = {}
    for x in rows:
        x = int(x)
        while x:
            p = x.bit_length() - 1
            y = basis.get(p)
            if y is None:
                basis[p] = x
                break
            x ^= y
    return len(basis)


def solve_coefficients_int(rows: list[int], target: int) -> list[int] | None:
    """Find coeffs c such that xor_i c_i rows[i] = target, or None."""
    # Basis pivot -> (row combination vector as int over coefficient indices, vector)
    basis_vec = {}
    basis_comb = {}
    for i, row in enumerate(rows):
        x = row
        comb = 1 << i
        while x:
            p = x.bit_length() - 1
            if p not in basis_vec:
                basis_vec[p] = x
                basis_comb[p] = comb
                break
            x ^= basis_vec[p]
            comb ^= basis_comb[p]
    x = target
    comb = 0
    while x:
        p = x.bit_length() - 1
        if p not in basis_vec:
            return None
        x ^= basis_vec[p]
        comb ^= basis_comb[p]
    return [(comb >> i) & 1 for i in range(len(rows))]


# ---------- tensor/action ----------

def build_T333_flat() -> np.ndarray:
    T = np.zeros((81, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[(3 * i + j) * 9 + (3 * j + k), 3 * k + i] = 1
    return T


def rowmajor_action_left_right(L: np.ndarray, R: np.ndarray) -> np.ndarray:
    # row-major vec(L X R) = kron(L, R.T) vec_row(X)
    return np.kron(L, R.T).astype(np.uint8) & 1


def sandwich_actions(F: np.ndarray):
    F = np.array(F, dtype=np.uint8) & 1
    Fi = gf2_inv(F)
    # Verified finite version of analysis infinitesimal pullback convention:
    # U,V -> F^T X F^{-T}; W -> F^{-1} X F.
    M9 = rowmajor_action_left_right(F.T & 1, Fi.T & 1)
    hW = rowmajor_action_left_right(Fi, F)
    gE = np.kron(M9, M9).astype(np.uint8) & 1
    return M9, gE, hW


def quotient_Q(T_flat: np.ndarray) -> np.ndarray:
    Q = gf2_nullspace(T_flat.T)
    assert Q.shape == (72, 81)
    assert gf2_rank(Q) == 72
    assert np.all(((Q @ T_flat) & 1) == 0)
    return Q


def right_inverse_Q(Q: np.ndarray) -> np.ndarray:
    _, _, pivots = gf2_rref(Q)
    Qpiv_inv = gf2_inv(Q[:, pivots])
    Qp = np.zeros((81, 72), dtype=np.uint8)
    for i, p in enumerate(pivots):
        Qp[p] = Qpiv_inv[i]
    assert np.array_equal((Q @ Qp) & 1, np.eye(72, dtype=np.uint8))
    return Qp


def enumerate_rank_one_f2() -> np.ndarray:
    pts = np.zeros(((2**9 - 1) ** 2, 81), dtype=np.uint8)
    idx = 0
    vectors = [None]
    for z in range(1, 512):
        vectors.append(np.array([(z >> b) & 1 for b in range(9)], dtype=np.uint8))
    for u_int in range(1, 512):
        u = vectors[u_int]
        for v_int in range(1, 512):
            pts[idx] = np.outer(u, vectors[v_int]).reshape(-1).astype(np.uint8)
            idx += 1
    return pts


def classify_orbits(gE: np.ndarray, pts: np.ndarray, order: int):
    index = {pts[i].tobytes(): i for i in range(len(pts))}
    visited = np.zeros(len(pts), dtype=bool)
    fixed = []
    free = []
    for i in range(len(pts)):
        if visited[i]:
            continue
        cur = pts[i]
        orb = [i]
        visited[i] = True
        for _ in range(order - 1):
            cur = (gE @ cur) & 1
            j = index[cur.tobytes()]
            if visited[j]:
                break
            visited[j] = True
            orb.append(j)
        if len(orb) == 1:
            fixed.append(i)
        else:
            if len(orb) != order:
                raise AssertionError(f"unexpected orbit length {len(orb)}")
            free.append(orb)
    return fixed, free


def fixed_coords_setup(fixE_basis: np.ndarray):
    rref, r, pivots = gf2_rref(fixE_basis)
    assert r == fixE_basis.shape[0]
    return rref, pivots


def fixed_coords(v: np.ndarray, pivots: list[int]) -> int:
    c = 0
    for i, p in enumerate(pivots):
        if v[p]:
            c |= 1 << i
    return c


def span_all_coords(coord_ints: list[int]) -> set[int]:
    vals = {0}
    for c in coord_ints:
        vals |= {x ^ c for x in list(vals)}
    return vals


def recover_W_and_verify_int(X_ints: list[int], T_ints: list[int], T_flat: np.ndarray):
    W_cols = []
    for target in T_ints:
        coeffs = solve_coefficients_int(X_ints, target)
        if coeffs is None:
            return None, False
        W_cols.append(coeffs)
    W = np.array(W_cols, dtype=np.uint8).T  # 22 x 9
    # reconstruct for an explicit check too
    X_mat = np.zeros((len(X_ints), 81), dtype=np.uint8)
    for i, x in enumerate(X_ints):
        for b in range(81):
            X_mat[i, b] = (x >> b) & 1
    recon = (X_mat.T @ W) & 1
    return W, bool(np.array_equal(recon, T_flat))


def main():
    t0 = time.time()
    out_dir = Path("data/order7_exhaustive")
    out_dir.mkdir(parents=True, exist_ok=True)

    T_flat = build_T333_flat()
    L_rows = T_flat.T & 1
    Q = quotient_Q(T_flat)
    Qp = right_inverse_Q(Q)
    L_ints = rows_to_ints(L_rows)
    T_ints = [vec_to_int(T_flat[:, c]) for c in range(9)]

    F7 = np.array([[0, 0, 1], [1, 0, 1], [0, 1, 0]], dtype=np.uint8)
    M9, gE, hW = sandwich_actions(F7)
    gbar = (Q @ gE @ Qp).astype(np.uint8) & 1
    action_ok = bool(np.array_equal((gE @ T_flat) & 1, (T_flat @ hW) & 1))
    if not action_ok:
        raise AssertionError("action does not preserve T")
    print("Corrected action verified: g_E T = T h_W")

    order_checks = {
        "F7": bool(np.array_equal(gf2_matpow(F7, 7), np.eye(3, dtype=np.uint8))),
        "M9": bool(np.array_equal(gf2_matpow(M9, 7), np.eye(9, dtype=np.uint8))),
        "gE": bool(np.array_equal(gf2_matpow(gE, 7), np.eye(81, dtype=np.uint8))),
        "hW": bool(np.array_equal(gf2_matpow(hW, 7), np.eye(9, dtype=np.uint8))),
        "gbar": bool(np.array_equal(gf2_matpow(gbar, 7), np.eye(72, dtype=np.uint8))),
    }
    print("Order checks:", order_checks)

    fixE_basis = gf2_nullspace((gE ^ np.eye(81, dtype=np.uint8)) & 1)
    fixQ_basis = gf2_nullspace((gbar ^ np.eye(72, dtype=np.uint8)) & 1)
    L0_basis = (gf2_nullspace((hW ^ np.eye(9, dtype=np.uint8)) & 1) @ L_rows) & 1
    L0_basis, L0_rank, _ = gf2_rref(L0_basis)
    fix_rref, fix_pivots = fixed_coords_setup(fixE_basis)
    print(f"Fixed dimensions: Fix(E)={fixE_basis.shape[0]}, L0={L0_rank}, Fix(E/L)={fixQ_basis.shape[0]}")

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
    print("Sigma checks:", sigma_checks)

    print("Enumerating rank-one points and orbits...")
    pts = enumerate_rank_one_f2()
    fixed_idx, free_orbits = classify_orbits(gE, pts, 7)
    fixed_pts = pts[fixed_idx]
    print(f"rank-one fixed={len(fixed_idx)}, free_orbits={len(free_orbits)}, total={len(fixed_idx)+7*len(free_orbits)}")

    fixed_ro_rank = gf2_rank(fixed_pts)
    fixed_ro_L_intersection = intersection_dim(fixed_pts, L_rows)
    fixed_ro_L0_intersection = intersection_dim(fixed_pts, L0_basis)
    print(f"fixed rank-one span rank={fixed_ro_rank}, intersection with L={fixed_ro_L_intersection}, with L0={fixed_ro_L0_intersection}")

    # Convert only the rows needed for triple ranks.
    pt_ints = rows_to_ints(pts)
    L0_coord_ints = [fixed_coords(row, fix_pivots) for row in L0_basis]
    L0_coord_span = span_all_coords(L0_coord_ints)
    assert len(L0_coord_span) == 2**L0_rank

    fixed_records = []
    for local_i, global_i in enumerate(fixed_idx):
        p = pts[global_i]
        pc = fixed_coords(p, fix_pivots)
        # p is outside L0 because fixed rank-one span meets L trivially.
        assert pc not in L0_coord_span
        fixed_records.append({"local": local_i, "global": global_i, "coord": pc, "int": pt_ints[global_i]})

    # Orbit sums and their fixed-space coordinates.
    sigma_to_orbits = defaultdict(list)
    orbit_member_ints = []
    orbit_qrank_profile = Counter()
    for oi, orb in enumerate(free_orbits):
        sig = np.bitwise_xor.reduce(pts[orb], axis=0).astype(np.uint8)
        # Check projector identity on representative.
        sig2 = (sigma @ pts[orb[0]]) & 1
        if not np.array_equal(sig, sig2):
            raise AssertionError("sigma mismatch")
        sc = fixed_coords(sig, fix_pivots)
        sigma_to_orbits[sc].append(oi)
        members_int = [pt_ints[j] for j in orb]
        orbit_member_ints.append(members_int)
        # Cheap corrected distribution by full/vector ranks for a single orbit, useful evidence.
        xr = rank_int(members_int)
        qr = gf2_rank((Q @ pts[orb].T).T & 1)
        lin = xr + 9 - rank_int(members_int + L_ints)
        orbit_qrank_profile[(xr, qr, lin, int(sc in L0_coord_span))] += 1
    print("single free orbit profiles (xrank,qrank,Loverlap,sigma_in_L0):")
    for k, v in sorted(orbit_qrank_profile.items()):
        print(f"  {k}: {v}")
    print(f"distinct orbit-sum fixed coords={len(sigma_to_orbits)}")

    skeletons = []
    for free_count, fixed_count in [(0, 22), (1, 15), (2, 8), (3, 1)]:
        max_xrank = min(fixed_count, fixed_ro_rank) + 7 * free_count
        if free_count == 2 and fixed_count == 8:
            fixed_part_needed = fixed_count + L0_rank
            fixed_part_available = fixed_count + free_count
            impossible = fixed_part_needed > fixed_part_available
            reason = (
                "full rank would force eight independent fixed rank-one points; "
                f"their span is disjoint from L0, so S^g must contain dimension 8+{L0_rank}={fixed_part_needed}, "
                f"but eight fixed terms plus two orbit sums give at most {fixed_part_available}"
            )
        else:
            impossible = max_xrank < 22
            reason = f"max UV rank <= min({fixed_count},{fixed_ro_rank}) + 7*{free_count} = {max_xrank}"
        skeletons.append({"free_orbits": free_count, "fixed_terms": fixed_count, "max_xrank_bound": int(max_xrank), "impossible": bool(impossible), "reason": reason})

    # Exhaust type (3,1) using the fixed-coordinate filter.
    total_filtered_triples = 0
    total_fullrank = 0
    total_Lcontain = 0
    successes = []
    best = {"score": [-1, -99, -1], "fixed_local": None, "triple": None, "test": None}
    per_fixed = []

    print("\nExhausting type (3,1) with sigma(O) in L0+<p> filter")
    for frec in fixed_records:
        allowed_coords = {x ^ (frec["coord"] if eps else 0) for x in L0_coord_span for eps in (0, 1)}
        survivors = []
        for ac in allowed_coords:
            survivors.extend(sigma_to_orbits.get(ac, []))
        survivors = sorted(set(survivors))
        n = len(survivors)
        triple_count = n * (n - 1) * (n - 2) // 6
        total_filtered_triples += triple_count
        p_fullrank = 0
        p_Lcontain = 0
        p_best = {"score": [-1, -99, -1], "triple": None, "test": None}
        for a, b, c in itertools.combinations(survivors, 3):
            X_ints = [frec["int"]] + orbit_member_ints[a] + orbit_member_ints[b] + orbit_member_ints[c]
            xr = rank_int(X_ints)
            # Skip qrank until we know something is close; L containment is decisive.
            comb_rank = rank_int(X_ints + L_ints)
            lin = xr + 9 - comb_rank
            if xr == 22:
                p_fullrank += 1
                total_fullrank += 1
            if lin == 9:
                p_Lcontain += 1
                total_Lcontain += 1
            qrank = xr - lin  # exact dim image of S in E/L
            test = {"x_rank": int(xr), "q_rank": int(qrank), "l_in_span": int(lin), "success": bool(xr == 22 and lin == 9)}
            score = [lin, -abs(qrank - 13), xr]
            if score > p_best["score"]:
                p_best = {"score": score, "triple": [int(a), int(b), int(c)], "test": test}
            if score > best["score"]:
                best = {"score": score, "fixed_local": int(frec["local"]), "triple": [int(a), int(b), int(c)], "test": test}
            if test["success"]:
                W, ok = recover_W_and_verify_int(X_ints, T_ints, T_flat)
                success = {"fixed_local": int(frec["local"]), "fixed_global": int(frec["global"]), "free_orbits": [int(a), int(b), int(c)], "test": test, "T_reconstruction_ok": bool(ok)}
                if ok:
                    cand_path = out_dir / f"rank22_candidate_fixed{frec['local']}_orbits{a}_{b}_{c}.npz"
                    # Reconstruct X matrix for saving only in success case.
                    X_mat = np.zeros((22, 81), dtype=np.uint8)
                    for ii, x in enumerate(X_ints):
                        for bit in range(81):
                            X_mat[ii, bit] = (x >> bit) & 1
                    np.savez_compressed(cand_path, X=X_mat, W=W, T_flat=T_flat, F7=F7, M9=M9, hW=hW)
                    success["candidate_npz"] = str(cand_path)
                successes.append(success)
                print("SUCCESS", success, flush=True)
        per = {
            "fixed_local": int(frec["local"]),
            "fixed_global": int(frec["global"]),
            "survivor_orbits": int(n),
            "triple_count": int(triple_count),
            "fullrank_triples": int(p_fullrank),
            "L_containing_triples": int(p_Lcontain),
            "best": p_best,
        }
        per_fixed.append(per)
        print(f"  fixed {frec['local']:02d}: survivors={n:3d}, triples={triple_count:6d}, fullrank={p_fullrank:6d}, L-containing={p_Lcontain:3d}, best={p_best['test']}", flush=True)

    print("\nSummary:")
    print(f"  total filtered triples={total_filtered_triples}")
    print(f"  fullrank triples={total_fullrank}")
    print(f"  L-containing triples={total_Lcontain}")
    print(f"  successes={len(successes)}")
    print(f"  best={best}")

    results = {
        "purpose": "Exact exhaustive order-7 sandwich-invariant rank-22 UV-span test over F2.",
        "field": "F2",
        "action_convention": {
            "U_V": "row-major vec(F^T X F^{-T}); matrix kron(F^T,F^{-1})",
            "W": "row-major vec(F^{-1} X F); matrix kron(F^{-1},F^T)",
            "gE_T_equals_T_hW": action_ok,
            "order_checks": order_checks,
            "F7_matrix": F7.astype(int).tolist(),
        },
        "fixed_dimensions": {
            "Fix_E": int(fixE_basis.shape[0]),
            "L0_dim": int(L0_rank),
            "Fix_E_mod_L": int(fixQ_basis.shape[0]),
            "sigma": sigma_checks,
        },
        "rank_one_orbits": {
            "fixed_count": int(len(fixed_idx)),
            "free_orbit_count": int(len(free_orbits)),
            "total_check": int(len(fixed_idx) + 7 * len(free_orbits)),
            "fixed_rank_one_span_rank": int(fixed_ro_rank),
            "fixed_rank_one_span_intersection_L": int(fixed_ro_L_intersection),
            "fixed_rank_one_span_intersection_L0": int(fixed_ro_L0_intersection),
            "single_free_orbit_profiles": {str(k): int(v) for k, v in sorted(orbit_qrank_profile.items())},
            "distinct_orbit_sum_fixed_coords": int(len(sigma_to_orbits)),
        },
        "skeletons": skeletons,
        "type_3_1_exhaustive": {
            "filter": "For each fixed p, only free orbits with sigma(O) in L0+<p> can occur in a successful (3,1) skeleton; every filtered triple is tested exactly by rank(X) and L<=span(X).",
            "per_fixed": per_fixed,
            "total_filtered_triples": int(total_filtered_triples),
            "fullrank_triples": int(total_fullrank),
            "L_containing_triples": int(total_Lcontain),
            "success_count": int(len(successes)),
            "successes": successes,
            "best": best,
        },
        "theorem_status": "No F2 rank-22 decomposition whose UV rank-one generators are permuted by the corrected order-7 sandwich subgroup." if not successes else "Candidate(s) found; inspect saved npz files and reconstruction flags.",
        "supersedes": "The analysis random/biased orbit_search_results.json used a non-preserving action convention and non-exhaustive sampling; this file is the replayable order-7 result.",
        "elapsed_sec": time.time() - t0,
    }
    out_path = out_dir / "order7_exhaustive_fast_results.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"Saved {out_path}; elapsed {time.time()-t0:.2f}s")


if __name__ == "__main__":
    main()
