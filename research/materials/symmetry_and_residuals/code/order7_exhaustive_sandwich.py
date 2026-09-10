#!/usr/bin/env python3
r"""analysis: exhaustive order-7 sandwich orbit-family test over F2.

This script repairs the analysis action convention and then uses the finite
orbit/eigenspace bookkeeping for the order-7 sandwich subgroup.

Tensor convention
-----------------
this investigation's QMM/Brent convention stores the matrix-multiplication tensor as
T_flat[uv,w] with rows uv=(i,j; j,k) and w=(k,i).  The infinitesimal convention
verified earlier is
    dU = p^T U - U q^T,
    dV = q^T V - V r^T,
    dW = -p W + W r.
For the diagonal/sandwich subgroup P=Q=R=F, the finite action on U and V
covectors is U -> F^T U F^{-T}; on W it is W -> F^{-1} W F.  In row-major
coordinates this is
    M9 = kron(F^T, F^{-1})
for U,V and
    HW = kron(F^{-1}, F^T)
for W.
This script checks g_E T = T H_W before using the action on E/L.

Mathematical target
-------------------
A rank-22 decomposition invariant under an order-7 action must have fixed/free
rank-one orbit skeletons (free_orbits, fixed_terms) among
(3,1), (2,8), (1,15), (0,22).  The latter two cannot have full UV-rank 22.
Type (2,8) is ruled out by the fixed-part dimension budget once the fixed
rank-one span is verified disjoint from L.  Type (3,1) is finite: for each fixed
rank-one p, a free orbit O may appear only if its orbit sum sigma(O) lies in
L0 + <p>, where L0=L∩Fix_E.  We exhaustively test every triple of surviving
free orbits by direct GF(2) rank computations for
    rank(X)=22 and L <= span(X).
If a success appears, W is recovered and T equality is checked exactly.
"""

from __future__ import annotations

import itertools
import json
import time
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np


# ---------- GF(2) linear algebra ----------

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
    if M.size == 0:
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
            raise ValueError("singular matrix")
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


def row_space_contains(B: np.ndarray, v: np.ndarray) -> bool:
    B = np.array(B, dtype=np.uint8) & 1
    v = np.array(v, dtype=np.uint8).reshape(1, -1) & 1
    return gf2_rank(np.vstack([B, v])) == gf2_rank(B)


def intersection_dim(A: np.ndarray, B: np.ndarray) -> int:
    return gf2_rank(A) + gf2_rank(B) - gf2_rank(np.vstack([A, B]))


def solve_rows_for_vector(rows: np.ndarray, target: np.ndarray) -> np.ndarray | None:
    """Find coefficients c with c @ rows = target, or None."""
    rows = np.array(rows, dtype=np.uint8) & 1
    target = np.array(target, dtype=np.uint8).reshape(-1) & 1
    # Solve rows.T c = target by row-reducing augmented system [rows.T | target].
    A = np.hstack([rows.T.copy(), target.reshape(-1, 1)]).astype(np.uint8)
    m, n_aug = A.shape
    n = n_aug - 1
    r = 0
    pivots = []
    for c in range(n):
        found = -1
        for i in range(r, m):
            if A[i, c]:
                found = i
                break
        if found < 0:
            continue
        if found != r:
            A[[r, found]] = A[[found, r]]
        pivots.append(c)
        for i in range(m):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
    # Inconsistent zero row with augmented 1.
    for i in range(r, m):
        if not A[i, :n].any() and A[i, n]:
            return None
    coeff = np.zeros(n, dtype=np.uint8)
    for i, p in enumerate(pivots):
        coeff[p] = A[i, n]
    return coeff


def basis_coords_in_rowspace(basis_rows: np.ndarray, vectors: np.ndarray) -> np.ndarray:
    """Coordinate rows of vectors relative to an independent row basis."""
    basis_rows = np.array(basis_rows, dtype=np.uint8) & 1
    vectors = np.array(vectors, dtype=np.uint8) & 1
    coords = []
    for v in vectors:
        c = solve_rows_for_vector(basis_rows, v)
        if c is None:
            raise ValueError("vector not in basis row span")
        coords.append(c)
    return np.array(coords, dtype=np.uint8)


# ---------- Tensor/action construction ----------

def build_T333_flat() -> np.ndarray:
    T = np.zeros((81, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                uv = (3 * i + j) * 9 + (3 * j + k)
                w = 3 * k + i
                T[uv, w] = 1
    return T


def rowmajor_action_left_right(L: np.ndarray, R: np.ndarray) -> np.ndarray:
    """Row-major vec(L X R) = kron(L, R.T) vec_row(X)."""
    return np.kron(L, R.T).astype(np.uint8) & 1


def sandwich_actions(F: np.ndarray):
    """Correct finite sandwich action in this investigation QMM convention."""
    F = np.array(F, dtype=np.uint8) & 1
    Fi = gf2_inv(F)
    M9 = rowmajor_action_left_right(F.T & 1, Fi.T & 1)  # F^T U F^{-T}
    # Since rowmajor_action uses R.T, passing R=Fi.T gives kron(F.T, Fi).
    HW = rowmajor_action_left_right(Fi, F)              # F^{-1} W F
    GE = np.kron(M9, M9).astype(np.uint8) & 1
    return M9, GE, HW


def quotient_Q(T_flat: np.ndarray) -> np.ndarray:
    Q = gf2_nullspace(T_flat.T)
    assert Q.shape == (72, 81)
    assert gf2_rank(Q) == 72
    assert np.all(((Q @ T_flat) & 1) == 0)
    return Q


def right_inverse_Q(Q: np.ndarray) -> np.ndarray:
    _, _, pivots = gf2_rref(Q)
    Qpiv = Q[:, pivots]
    Qpiv_inv = gf2_inv(Qpiv)
    Qp = np.zeros((81, 72), dtype=np.uint8)
    for i, p in enumerate(pivots):
        Qp[p] = Qpiv_inv[i]
    assert np.array_equal((Q @ Qp) & 1, np.eye(72, dtype=np.uint8))
    return Qp


def enumerate_rank_one_f2() -> np.ndarray:
    pts = np.zeros(((2**9 - 1) ** 2, 81), dtype=np.uint8)
    idx = 0
    for u_int in range(1, 512):
        u = np.array([(u_int >> b) & 1 for b in range(9)], dtype=np.uint8)
        for v_int in range(1, 512):
            v = np.array([(v_int >> b) & 1 for b in range(9)], dtype=np.uint8)
            pts[idx] = np.outer(u, v).reshape(-1).astype(np.uint8)
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


def qbar_action(gE: np.ndarray, Q: np.ndarray, Qp: np.ndarray) -> np.ndarray:
    return (Q @ gE @ Qp).astype(np.uint8) & 1


def direct_test_columns(X_rows: np.ndarray, L_rows: np.ndarray, Q: np.ndarray):
    x_rank = gf2_rank(X_rows)
    q_rank = gf2_rank((Q @ X_rows.T).T & 1)
    l_in = x_rank + gf2_rank(L_rows) - gf2_rank(np.vstack([X_rows, L_rows]))
    return {"x_rank": int(x_rank), "q_rank": int(q_rank), "l_in_span": int(l_in), "success": bool(x_rank == 22 and q_rank == 13 and l_in == 9)}


def recover_W_and_verify(X_rows: np.ndarray, T_flat: np.ndarray):
    W = np.zeros((X_rows.shape[0], T_flat.shape[1]), dtype=np.uint8)
    for c in range(T_flat.shape[1]):
        coeff = solve_rows_for_vector(X_rows, T_flat[:, c])
        if coeff is None:
            return None, False
        W[:, c] = coeff
    recon = (X_rows.T @ W) & 1
    return W, bool(np.array_equal(recon, T_flat))


# ---------- Main exhaustive test ----------

def main():
    t0 = time.time()
    out_dir = Path("data/order7_exhaustive")
    out_dir.mkdir(parents=True, exist_ok=True)

    T_flat = build_T333_flat()
    L_rows = T_flat.T & 1
    Q = quotient_Q(T_flat)
    Qp = right_inverse_Q(Q)

    F7 = np.array([[0, 0, 1], [1, 0, 1], [0, 1, 0]], dtype=np.uint8)
    M9, gE, hW = sandwich_actions(F7)

    action_check = bool(np.array_equal((gE @ T_flat) & 1, (T_flat @ hW) & 1))
    order_checks = {
        "F7_order": bool(np.array_equal(gf2_matpow(F7, 7), np.eye(3, dtype=np.uint8))),
        "M9_order": bool(np.array_equal(gf2_matpow(M9, 7), np.eye(9, dtype=np.uint8))),
        "gE_order": bool(np.array_equal(gf2_matpow(gE, 7), np.eye(81, dtype=np.uint8))),
        "hW_order": bool(np.array_equal(gf2_matpow(hW, 7), np.eye(9, dtype=np.uint8))),
    }
    if not action_check:
        raise AssertionError("corrected sandwich action still does not preserve T_flat")
    print("Corrected action verified: gE*T_flat = T_flat*hW")
    print("Order checks:", order_checks)

    # Fixed spaces in E, L, and E/L.
    I81 = np.eye(81, dtype=np.uint8)
    I72 = np.eye(72, dtype=np.uint8)
    fixE_basis = gf2_nullspace((gE ^ I81) & 1)
    L0_basis = gf2_nullspace((hW ^ np.eye(9, dtype=np.uint8)) & 1) @ L_rows & 1
    L0_basis, L0_rank, _ = gf2_rref(L0_basis)
    gbar = qbar_action(gE, Q, Qp)
    fixQ_basis = gf2_nullspace((gbar ^ I72) & 1)
    print(f"Fixed dimensions: E={fixE_basis.shape[0]}, L0={L0_rank}, E/L={fixQ_basis.shape[0]}")

    # Projector sigma=sum g^k onto Fix_E.
    sigma = np.zeros((81, 81), dtype=np.uint8)
    pwr = np.eye(81, dtype=np.uint8)
    for _ in range(7):
        sigma ^= pwr
        pwr = (gE @ pwr) & 1
    sigma_rank = gf2_rank(sigma)
    sigma_idempotent = bool(np.array_equal((sigma @ sigma) & 1, sigma))
    sigma_kills_nonfix_rank = gf2_rank(((gE ^ I81) @ sigma) & 1)
    print(f"sigma rank={sigma_rank}, idempotent={sigma_idempotent}, (g-I)sigma rank={sigma_kills_nonfix_rank}")

    print("Enumerating rank-one points and order-7 orbits...")
    pts = enumerate_rank_one_f2()
    fixed_idx, free_orbits = classify_orbits(gE, pts, 7)
    print(f"rank-one fixed={len(fixed_idx)}, free_orbits={len(free_orbits)}, total={len(fixed_idx)+7*len(free_orbits)}")

    fixed_pts = pts[fixed_idx]
    fixed_ro_basis, fixed_ro_rank, _ = gf2_rref(fixed_pts)
    fixed_ro_L_intersection = intersection_dim(fixed_pts, L_rows)
    fixed_ro_L0_intersection = intersection_dim(fixed_pts, L0_basis)
    fixed_plus_L0_rank = gf2_rank(np.vstack([fixed_pts, L0_basis]))
    print(f"fixed rank-one span rank={fixed_ro_rank}, intersection with L={fixed_ro_L_intersection}, with L0={fixed_ro_L0_intersection}, plus L0 rank={fixed_plus_L0_rank}")

    # Quick profile distribution for free orbit spans using the corrected action.
    profile_counter = Counter()
    orbit_records = []
    for oi, orb in enumerate(free_orbits):
        Xo = pts[orb]
        sig = np.bitwise_xor.reduce(Xo, axis=0).astype(np.uint8)  # sum over the orbit
        # qrank/xrank/l-overlap for the single orbit, now under corrected action.
        xrank = gf2_rank(Xo)
        qrank = gf2_rank((Q @ Xo.T).T & 1)
        l_in = xrank + 9 - gf2_rank(np.vstack([Xo, L_rows]))
        # sigma must match the row sum; check the projector too.
        sig2 = (sigma @ pts[orb[0]]) & 1
        if not np.array_equal(sig, sig2):
            raise AssertionError("orbit sum mismatch")
        s_in_L0 = row_space_contains(L0_basis, sig)
        orbit_records.append({
            "orbit_index": oi,
            "members": orb,
            "sigma": sig,
            "xrank": xrank,
            "qrank": qrank,
            "l_in": l_in,
            "sigma_in_L0": bool(s_in_L0),
        })
        profile_counter[(xrank, qrank, l_in, int(s_in_L0))] += 1
    print("Corrected single-free-orbit profile distribution (xrank,qrank,Loverlap,sigma_in_L0):")
    for k, v in sorted(profile_counter.items()):
        print(f"  {k}: {v}")

    # Skeleton impossibility data.
    skeletons = []
    for free_count, fixed_count in [(0, 22), (1, 15), (2, 8), (3, 1)]:
        max_xrank = min(fixed_count, fixed_ro_rank) + 7 * free_count
        if free_count == 2 and fixed_count == 8:
            # Full UV rank would force 8 independent fixed points; fixed part would need P+L0.
            fixed_part_available = fixed_count + free_count
            fixed_part_needed_if_full = fixed_count + L0_rank  # disjointness verified above
            reason = f"type (2,8): full rank would require fixed-point rank 8; then P∩L0=0 so fixed part must contain dim 8+{L0_rank}={fixed_part_needed_if_full}, but 8 fixed terms plus 2 orbit sums give at most {fixed_part_available}"
            impossible = fixed_part_needed_if_full > fixed_part_available
        else:
            reason = f"max UV rank <= min({fixed_count},{fixed_ro_rank}) + 7*{free_count} = {max_xrank}"
            impossible = max_xrank < 22
        skeletons.append({
            "free_orbits": free_count,
            "fixed_terms": fixed_count,
            "max_xrank_bound": int(max_xrank),
            "impossible_without_triple_scan": bool(impossible),
            "reason": reason,
        })

    # Exhaust type (3,1).
    # For each fixed p, survivor orbits have sigma(O) in L0 + <p>.
    print("\nExhausting type (3,1): one fixed point plus three size-7 orbits")
    per_fixed = []
    total_triples = 0
    fullrank_triples = 0
    l_containing_triples = 0
    successes = []
    best = {"score": (-1, -1, -1), "fixed_local": None, "triple": None, "test": None}

    # A compact independent basis of fixed rank-one points is useful for p rank info.
    for pi_local, p in enumerate(fixed_pts):
        Pspace = gf2_rref(np.vstack([L0_basis, p.reshape(1, 81)]))[0]
        assert gf2_rank(Pspace) == L0_rank + 1  # p is not in L0 because fixed_ro ∩ L = 0.
        survivors = [rec["orbit_index"] for rec in orbit_records if row_space_contains(Pspace, rec["sigma"])]
        n = len(survivors)
        triple_count = n * (n - 1) * (n - 2) // 6
        total_triples += triple_count
        p_fullrank = 0
        p_lcontain = 0
        p_best = {"score": (-1, -1, -1), "triple": None, "test": None}
        for a, b, c in itertools.combinations(survivors, 3):
            rows = [p]
            for oi in (a, b, c):
                rows.extend(pts[j] for j in free_orbits[oi])
            X = np.array(rows, dtype=np.uint8)
            test = direct_test_columns(X, L_rows, Q)
            if test["x_rank"] == 22:
                fullrank_triples += 1
                p_fullrank += 1
            if test["l_in_span"] == 9:
                l_containing_triples += 1
                p_lcontain += 1
            score = (test["l_in_span"], -abs(test["q_rank"] - 13), test["x_rank"])
            if score > best["score"]:
                best = {"score": score, "fixed_local": pi_local, "triple": [a, b, c], "test": test}
            if score > p_best["score"]:
                p_best = {"score": score, "triple": [a, b, c], "test": test}
            if test["success"]:
                W, ok = recover_W_and_verify(X, T_flat)
                success = {"fixed_local": pi_local, "free_orbits": [a, b, c], "test": test, "T_reconstruction_ok": ok}
                if ok:
                    # Save the candidate arrays for independent verification.
                    cand_path = out_dir / f"rank22_candidate_fixed{pi_local}_orbits{a}_{b}_{c}.npz"
                    np.savez_compressed(cand_path, X=X, W=W, T_flat=T_flat, F7=F7, M9=M9, hW=hW)
                    success["candidate_npz"] = str(cand_path)
                successes.append(success)
                print("SUCCESS", success)
        per_fixed.append({
            "fixed_local": pi_local,
            "survivor_orbits": n,
            "triple_count": triple_count,
            "fullrank_triples": p_fullrank,
            "L_containing_triples": p_lcontain,
            "best": p_best,
        })
        print(f"  fixed {pi_local:02d}: survivors={n:3d}, triples={triple_count:5d}, fullrank={p_fullrank:5d}, L-containing={p_lcontain:3d}, best={p_best['test']}")

    print("\nType (3,1) exhaustive summary")
    print(f"  total filtered triples={total_triples}")
    print(f"  fullrank triples={fullrank_triples}")
    print(f"  L-containing triples={l_containing_triples}")
    print(f"  successes={len(successes)}")
    print(f"  best={best}")

    results = {
        "purpose": "Exact F2 order-7 sandwich-invariant rank-22 orbit-family test with corrected QMM action convention.",
        "field": "F2",
        "action_convention": {
            "U_V": "row-major vec(F^T X F^{-T}) = kron(F^T,F^{-1}) vec(X)",
            "W": "row-major vec(F^{-1} X F) = kron(F^{-1},F^T) vec(X)",
            "gE_T_equals_T_hW": action_check,
            "order_checks": order_checks,
        },
        "fixed_dimensions": {
            "Fix_E": int(fixE_basis.shape[0]),
            "L0_equals_L_intersection_Fix_E": int(L0_rank),
            "Fix_E_mod_L": int(fixQ_basis.shape[0]),
            "sigma_rank": int(sigma_rank),
            "sigma_idempotent": sigma_idempotent,
            "g_minus_I_times_sigma_rank": int(sigma_kills_nonfix_rank),
        },
        "rank_one_orbits": {
            "fixed_count": int(len(fixed_idx)),
            "free_orbit_count": int(len(free_orbits)),
            "total_check": int(len(fixed_idx) + 7 * len(free_orbits)),
            "fixed_rank_one_span_rank": int(fixed_ro_rank),
            "fixed_rank_one_span_intersection_L": int(fixed_ro_L_intersection),
            "fixed_rank_one_span_intersection_L0": int(fixed_ro_L0_intersection),
            "fixed_rank_one_plus_L0_rank": int(fixed_plus_L0_rank),
            "single_free_orbit_profiles": {str(k): int(v) for k, v in sorted(profile_counter.items())},
        },
        "skeletons": skeletons,
        "type_3_1_exhaustive": {
            "filter": "For fixed rank-one p, require sigma(orbit) in L0+<p>; then test every triple directly by rank(X)=22 and L<=span(X).",
            "per_fixed": per_fixed,
            "total_filtered_triples": int(total_triples),
            "fullrank_triples": int(fullrank_triples),
            "L_containing_triples": int(l_containing_triples),
            "success_count": int(len(successes)),
            "successes": successes,
            "best": best,
        },
        "theorem_status": "excludes all rank-22 decompositions over F2 whose 22 UV rank-one generators are permuted by this corrected order-7 sandwich subgroup" if not successes else "rank-22 candidate(s) found; inspect candidate_npz and reconstruction status",
        "elapsed_sec": time.time() - t0,
    }
    out_path = out_dir / "order7_exhaustive_results.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2, default=lambda o: int(o) if isinstance(o, np.integer) else str(o))
    print(f"Saved {out_path}; elapsed {time.time()-t0:.2f}s")


if __name__ == "__main__":
    main()
