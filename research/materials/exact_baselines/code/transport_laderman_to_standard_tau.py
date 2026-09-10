#!/usr/bin/env python3
"""analysis: transport Laderman's Phi3*Phi4 symmetry to standard transpose tau.

Purpose
-------
analysis tested Laderman free-orbit bivectors using the *standard* tau anti-target
but left the Laderman decomposition in coordinates where the involution is
Phi = Phi3 o Phi4, not standard tau.  This script fixes that.

We use the sandwich automorphism
    g_{P,Q,R}(A,B,C) = (P A Q^{-1}, Q B R^{-1}, R C P^{-1})
with
    P = I,
    Q = eps1*pi12 = pi12*eps2,
    R = diag(i,1,1),  i^2=-1,
so that, over fields containing sqrt(-1),
    Phi = g^{-1} tau g      (equivalently tau g = g Phi),
where tau(A,B,C)=(A^T,C^T,B^T).

The script verifies the conjugacy identities, transports all 23 Laderman terms,
replays T_333 exactly modulo p=65521, checks standard-tau orbit matching, verifies
that fixed terms have zero standard bivector, then tests whether the eight free
orbit bivectors contain the standard anti target L_anti.

The result is field-explicit: p=65521 contains sqrt(-1).  Over F3 or Q this
particular inner transport is not available with R^T R=eps1.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "transport_laderman_tau"
OUT.mkdir(parents=True, exist_ok=True)

P_MOD = 65521
I_SQRT_MINUS_ONE = 41224  # verified in analysis; 41224^2 == -1 mod 65521
assert (I_SQRT_MINUS_ONE * I_SQRT_MINUS_ONE + 1) % P_MOD == 0

# ---------- finite-field linear algebra ----------
def mod(A, p=P_MOD):
    return np.asarray(A, dtype=object) % p

def inv_mod_int(a, p=P_MOD):
    return pow(int(a) % p, -1, p)

def mat_inv_mod(A, p=P_MOD):
    A = mod(A, p)
    n = A.shape[0]
    aug = np.concatenate([A.copy(), np.eye(n, dtype=object)], axis=1) % p
    row = 0
    for col in range(n):
        pivot = None
        for r in range(row, n):
            if int(aug[r, col]) % p != 0:
                pivot = r
                break
        if pivot is None:
            raise ValueError("singular matrix")
        if pivot != row:
            aug[[row, pivot]] = aug[[pivot, row]]
        invp = inv_mod_int(aug[row, col], p)
        aug[row, :] = (aug[row, :] * invp) % p
        for r in range(n):
            if r != row and int(aug[r, col]) % p != 0:
                aug[r, :] = (aug[r, :] - aug[r, col] * aug[row, :]) % p
        row += 1
    return aug[:, n:] % p

def rank_mod(M, p=P_MOD):
    M = mod(M, p).copy()
    m, n = M.shape
    rank = 0
    for col in range(n):
        pivot = None
        for r in range(rank, m):
            if int(M[r, col]) % p != 0:
                pivot = r
                break
        if pivot is None:
            continue
        if pivot != rank:
            M[[rank, pivot]] = M[[pivot, rank]]
        invp = inv_mod_int(M[rank, col], p)
        M[rank, :] = (M[rank, :] * invp) % p
        for r in range(m):
            if r != rank and int(M[r, col]) % p != 0:
                M[r, :] = (M[r, :] - M[r, col] * M[rank, :]) % p
        rank += 1
        if rank == m:
            break
    return rank

def rref_mod(M, p=P_MOD):
    M = mod(M, p).copy()
    m, n = M.shape
    rank = 0
    pivots = []
    for col in range(n):
        pivot = None
        for r in range(rank, m):
            if int(M[r, col]) % p != 0:
                pivot = r
                break
        if pivot is None:
            continue
        if pivot != rank:
            M[[rank, pivot]] = M[[pivot, rank]]
        invp = inv_mod_int(M[rank, col], p)
        M[rank, :] = (M[rank, :] * invp) % p
        for r in range(m):
            if r != rank and int(M[r, col]) % p != 0:
                M[r, :] = (M[r, :] - M[r, col] * M[rank, :]) % p
        pivots.append(col)
        rank += 1
        if rank == m:
            break
    return M, pivots

def solve_left_coeffs(B_rows, target_rows, p=P_MOD):
    """Solve X B_rows = target_rows over F_p, if possible.

    B_rows is m x n; target_rows is k x n. Returns k x m coefficient matrix.
    """
    B = mod(B_rows, p)
    T = mod(target_rows, p)
    m, n = B.shape
    k = T.shape[0]
    # solve B^T x = t^T for each target row
    A = B.T.copy()  # n x m
    coeffs = []
    for rr in range(k):
        b = T[rr, :].reshape(n, 1)
        aug = np.concatenate([A.copy(), b], axis=1) % p
        row = 0
        pivots = []
        inconsistent = False
        for col in range(m):
            pivot = None
            for r in range(row, n):
                if int(aug[r, col]) % p != 0:
                    pivot = r
                    break
            if pivot is None:
                continue
            if pivot != row:
                aug[[row, pivot]] = aug[[pivot, row]]
            invp = inv_mod_int(aug[row, col], p)
            aug[row, :] = (aug[row, :] * invp) % p
            for r in range(n):
                if r != row and int(aug[r, col]) % p != 0:
                    aug[r, :] = (aug[r, :] - aug[r, col] * aug[row, :]) % p
            pivots.append(col)
            row += 1
        for r in range(row, n):
            if all(int(aug[r, c]) % p == 0 for c in range(m)) and int(aug[r, m]) % p != 0:
                inconsistent = True
                break
        if inconsistent:
            return None
        x = np.zeros(m, dtype=object)
        for i, col in enumerate(pivots):
            x[col] = aug[i, m] % p
        coeffs.append(x)
    return np.vstack(coeffs) % p

# ---------- load analysis Laderman definitions without running output code ----------
src_path = SCRIPT_DIR / "laderman_tau_decomp.py"
src = src_path.read_text()
prefix = src.split('print(f"Sum matches T333')[0]
ns = {"__file__": str(src_path), "__name__": "defs_only"}
exec(compile(prefix, str(src_path), "exec"), ns)
terms_int = ns["terms"]
T333_int = ns["T333"]
pi12 = mod(ns["pi12"])
eps1 = mod(ns["eps1"])
eps2 = mod(ns["eps2"])
I3 = mod(ns["I3"])

terms = [(mod(a), mod(b), mod(c)) for a, b, c in terms_int]
T333 = mod(T333_int)

# Phi terms/permutation from analysis
fixed_1idx = [1, 4, 10, 12, 19, 21, 23]
two_cycles_1idx = [(2,5), (3,6), (7,16), (8,18), (9,17), (11,14), (13,15), (20,22)]
fixed = [i-1 for i in fixed_1idx]
two_cycles = [(i-1, j-1) for i, j in two_cycles_1idx]
perm = list(range(23))
for i, j in two_cycles:
    perm[i] = j
    perm[j] = i

# ---------- actions ----------
def Phi(a,b,c):
    # Phi3(Phi4(.)) from analysis, all mod p
    a4 = eps1 @ c @ pi12 % P_MOD
    b4 = pi12 @ a @ pi12 @ eps1 % P_MOD
    c4 = eps1 @ pi12 @ b @ eps1 % P_MOD
    return (b4.T @ eps2 % P_MOD, eps2 @ a4.T % P_MOD, c4.T % P_MOD)

def tau(a,b,c):
    return (a.T % P_MOD, c.T % P_MOD, b.T % P_MOD)

Q = eps1 @ pi12 % P_MOD
# check equality also pi12*eps2
Q_alt = pi12 @ eps2 % P_MOD
assert np.array_equal(Q, Q_alt)
Qinv = mat_inv_mod(Q)
R = np.diag([I_SQRT_MINUS_ONE, 1, 1]).astype(object) % P_MOD
Rinv = mat_inv_mod(R)
Pmat = I3

def g(a,b,c):
    return (Pmat @ a @ Qinv % P_MOD,
            Q @ b @ Rinv % P_MOD,
            R @ c @ Pmat % P_MOD)

def g_inv(a,b,c):
    return (Pmat @ a @ Q % P_MOD,
            Qinv @ b @ R % P_MOD,
            Rinv @ c @ Pmat % P_MOD)

# ---------- verification helpers ----------
def tensor_sum(term_list):
    T = np.zeros((9,9,9), dtype=object)
    for a,b,c in term_list:
        for r1 in range(3):
            for c1 in range(3):
                ia = 3*r1+c1
                av = a[r1,c1]
                if int(av) % P_MOD == 0: continue
                for r2 in range(3):
                    for c2 in range(3):
                        ib = 3*r2+c2
                        bv = b[r2,c2]
                        if int(bv) % P_MOD == 0: continue
                        for r3 in range(3):
                            for c3 in range(3):
                                cv = c[r3,c3]
                                if int(cv) % P_MOD:
                                    T[ia, ib, 3*r3+c3] = (T[ia, ib, 3*r3+c3] + av*bv*cv) % P_MOD
    return T % P_MOD

def flatten_nonzero(M):
    vals = list(np.asarray(M, dtype=object).reshape(-1))
    return [int(x) % P_MOD for x in vals]

def proportional_matrix(X, Y):
    """Return scalar lam with X = lam Y, or None."""
    Xv = flatten_nonzero(X); Yv = flatten_nonzero(Y)
    lam = None
    for x, y in zip(Xv, Yv):
        if y != 0:
            if lam is None:
                lam = x * inv_mod_int(y) % P_MOD
            elif x % P_MOD != (lam * y) % P_MOD:
                return None
        else:
            if x != 0:
                return None
    if lam is None:
        return 0 if all(x == 0 for x in Xv) else None
    return lam

def match_term_projective(term, candidates):
    a,b,c = term
    for j,(aa,bb,cc) in enumerate(candidates):
        la = proportional_matrix(a, aa)
        if la is None or la == 0: continue
        lb = proportional_matrix(b, bb)
        if lb is None or lb == 0: continue
        lc = proportional_matrix(c, cc)
        if lc is None or lc == 0: continue
        if (la * lb * lc) % P_MOD == 1:
            return j, (int(la), int(lb), int(lc))
    return None, None

# ---------- conjugacy identities ----------
# Matrix-level identities proving Phi = g^{-1} tau g for this P,Q,R.
conjugacy_checks = {
    "i_squared_minus_one": int((I_SQRT_MINUS_ONE * I_SQRT_MINUS_ONE) % P_MOD),
    "Q_equals_eps1_pi12_equals_pi12_eps2": bool(np.array_equal(Q, Q_alt)),
    "R_T_R_equals_eps1": bool(np.array_equal(R.T @ R % P_MOD, eps1)),
    "R_inv_R_inv_T_equals_eps1": bool(np.array_equal(Rinv @ Rinv.T % P_MOD, eps1)),
}
# Random/exhaustive basis check for tau(g(x)) == g(Phi(x)) termwise on basis triples
basis_ok = True
for pos in range(9):
    A = np.zeros((3,3), dtype=object); A.reshape(9)[pos] = 1
    Z = np.zeros((3,3), dtype=object)
    lhs = tau(*g(A,Z,Z))[0]
    rhs = g(*Phi(A,Z,Z))[0]
    if not np.array_equal(lhs % P_MOD, rhs % P_MOD): basis_ok = False
for pos in range(9):
    B = np.zeros((3,3), dtype=object); B.reshape(9)[pos] = 1
    Z = np.zeros((3,3), dtype=object)
    lhs = tau(*g(Z,B,Z))[2]  # B contributes to third factor under tau
    rhs = g(*Phi(Z,B,Z))[2]
    if not np.array_equal(lhs % P_MOD, rhs % P_MOD): basis_ok = False
for pos in range(9):
    C = np.zeros((3,3), dtype=object); C.reshape(9)[pos] = 1
    Z = np.zeros((3,3), dtype=object)
    lhs = tau(*g(Z,Z,C))[1]  # C contributes to second factor under tau
    rhs = g(*Phi(Z,Z,C))[1]
    if not np.array_equal(lhs % P_MOD, rhs % P_MOD): basis_ok = False
conjugacy_checks["basis_tau_g_equals_g_Phi"] = basis_ok

# ---------- transport and replay ----------
transported = [g(a,b,c) for a,b,c in terms]
T_trans = tensor_sum(transported)
replay_ok = bool(np.array_equal(T_trans % P_MOD, T333 % P_MOD))

# Standard tau orbit matching of transported scheme
std_tau_matches = []
for i,t in enumerate(transported):
    j, scales = match_term_projective(tau(*t), transported)
    std_tau_matches.append({"term": i+1, "tau_term": None if j is None else j+1, "scales": scales})
std_perm = [m["tau_term"] for m in std_tau_matches]
std_perm_ok = std_perm == [p+1 for p in perm]

# ---------- anti target and bivectors ----------
WEDGE_PAIRS = [(a,b) for a in range(9) for b in range(a+1,9)]
SKEW_PAIRS = [(0,1),(0,2),(1,2)]

def vec9(M):
    return np.asarray(M, dtype=object).reshape(9) % P_MOD

def wedge_vec(v,w):
    out = np.zeros(36, dtype=object)
    for t,(i,j) in enumerate(WEDGE_PAIRS):
        out[t] = (v[i]*w[j] - v[j]*w[i]) % P_MOD
    return out

def anti_target():
    def idx(i,k): return 3*i+k
    T = np.zeros((3,36), dtype=object)
    for r,(a,b) in enumerate(SKEW_PAIRS):
        M = np.zeros((9,9), dtype=object)
        for i in range(3):
            for j in range(3):
                Aij = 0
                if (i,j)==(a,b): Aij = 1
                elif (i,j)==(b,a): Aij = -1
                if Aij == 0: continue
                for k in range(3):
                    y = idx(j,k)
                    z = idx(i,k)
                    M[y,z] = (M[y,z] + Aij) % P_MOD
        # upper triangular storage: M[i,j] for i<j; wedge_vec stores twice skew orbit when paired
        for t,(i,j) in enumerate(WEDGE_PAIRS):
            T[r,t] = M[i,j] % P_MOD
    return T % P_MOD

A_TARGET = anti_target()
assert rank_mod(A_TARGET) == 3

all_bivectors = []
for a,b,c in transported:
    v = vec9(b)
    w = vec9(c.T)  # standard tau pairs second factor with transpose of third
    all_bivectors.append(wedge_vec(v,w))
all_bivectors = np.vstack(all_bivectors) % P_MOD

fixed_norm_zero = []
for i in fixed:
    fixed_norm_zero.append(bool(np.all(all_bivectors[i] % P_MOD == 0)))

rep_indices = [i for i,j in two_cycles]
partner_indices = [j for i,j in two_cycles]
rep_bivecs = all_bivectors[rep_indices]
partner_bivecs = all_bivectors[partner_indices]
# For exact tau-paired terms, partner bivector should be - rep (up to any factor-normalization; with product scaling 1 it should be -)
partner_relations = []
for idx,(i,j) in enumerate(two_cycles):
    eta_i = all_bivectors[i]
    eta_j = all_bivectors[j]
    lam = proportional_matrix(eta_j.reshape(1,36), eta_i.reshape(1,36))
    partner_relations.append({"pair": [i+1,j+1], "eta_partner_over_rep": None if lam is None else int(lam)})

# Containment ranks
rep_rank = rank_mod(rep_bivecs)
rep_aug_rank = rank_mod(np.vstack([rep_bivecs, A_TARGET]))
rep_contains = rep_rank == rep_aug_rank
partner_rank = rank_mod(partner_bivecs)
partner_aug_rank = rank_mod(np.vstack([partner_bivecs, A_TARGET]))
all_free_bivecs = np.vstack([rep_bivecs, partner_bivecs])
all_free_rank = rank_mod(all_free_bivecs)
all_free_aug_rank = rank_mod(np.vstack([all_free_bivecs, A_TARGET]))

coeffs_rep = solve_left_coeffs(rep_bivecs, A_TARGET) if rep_contains else None

# Compare canonical 9 again over same field
canonical = []
def idx(i,k): return 3*i+k
for (a,b) in SKEW_PAIRS:
    for k in range(3):
        va = np.zeros(9, dtype=object); vb = np.zeros(9, dtype=object)
        va[idx(a,k)] = 1; vb[idx(b,k)] = 1
        canonical.append(wedge_vec(va,vb))
canonical = np.vstack(canonical) % P_MOD
can_rank = rank_mod(canonical)
can_aug_rank = rank_mod(np.vstack([canonical,A_TARGET]))
can_skip_defects = []
for skip in range(9):
    sub = np.delete(canonical, skip, axis=0)
    can_skip_defects.append(int(rank_mod(np.vstack([sub,A_TARGET])) - rank_mod(sub)))

# Field-class note: R^T R = eps1 solvability over F3/Q.
# We certify determinant/square obstruction for this diagonal form: det(eps1)=-1.
field_notes = {
    "over_F65521_minus_one_square": True,
    "over_F3_minus_one_square": False,
    "over_Q_R_T_R_equals_eps1_with_rational_R": "impossible because det(R)^2 = det(eps1) = -1 is not a rational square",
    "over_C_or_Q_i": "possible; this script realizes the same algebra modulo p=65521 with i^2=-1"
}

out = {
    "field": f"F_{P_MOD}",
    "sqrt_minus_one": I_SQRT_MINUS_ONE,
    "conjugacy_checks": conjugacy_checks,
    "sandwich_g": {
        "P": [[int(x) for x in row] for row in Pmat.tolist()],
        "Q_eps1_pi12": [[int(x) for x in row] for row in Q.tolist()],
        "R_diag_i_1_1": [[int(x) for x in row] for row in R.tolist()],
        "formula": "g(A,B,C)=(P A Q^{-1}, Q B R^{-1}, R C P^{-1}); Phi=g^{-1} tau g"
    },
    "transported_replay_T333": replay_ok,
    "standard_tau_perm_matches_phi_perm": bool(std_perm_ok),
    "standard_tau_matches": std_tau_matches,
    "fixed_terms": fixed_1idx,
    "fixed_bivectors_all_zero": bool(all(fixed_norm_zero)),
    "fixed_bivectors_zero_by_term": {str(i+1): fixed_norm_zero[k] for k,i in enumerate(fixed)},
    "free_pairs": [[i+1,j+1] for i,j in two_cycles],
    "partner_bivector_relations": partner_relations,
    "anti_target_rank": int(rank_mod(A_TARGET)),
    "eight_rep_bivector_rank": int(rep_rank),
    "eight_rep_augmented_rank_with_Lanti": int(rep_aug_rank),
    "eight_rep_span_Lanti": bool(rep_contains),
    "eight_partner_bivector_rank": int(partner_rank),
    "eight_partner_augmented_rank_with_Lanti": int(partner_aug_rank),
    "eight_partner_span_Lanti": bool(partner_rank == partner_aug_rank),
    "all_16_free_bivector_rank": int(all_free_rank),
    "all_16_free_augmented_rank_with_Lanti": int(all_free_aug_rank),
    "all_16_free_span_Lanti": bool(all_free_rank == all_free_aug_rank),
    "coefficients_A_TARGET_in_eight_rep_basis": None if coeffs_rep is None else [[int(x) for x in row] for row in coeffs_rep.tolist()],
    "canonical_9_rank": int(can_rank),
    "canonical_9_span_Lanti": bool(can_rank == can_aug_rank),
    "canonical_skip_defects": can_skip_defects,
    "field_notes": field_notes,
    "interpretation": (
        "This is the convention-correct Laderman anti-sector test.  It transports "
        "Phi3*Phi4 to standard tau over a field with sqrt(-1), verifies exact T333 "
        "and standard tau invariance, and then tests whether the eight free standard "
        "tau bivectors span L_anti.  It supersedes the mismatched analysis Laderman "
        "bivector conclusions."
    )
}
path = OUT / "transported_laderman_standard_tau_F65521.json"
path.write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
print(f"SAVED {path}")
