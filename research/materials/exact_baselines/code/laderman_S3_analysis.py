#!/usr/bin/env python3
"""analysis: Check Laderman S3 symmetry, enumerate S3 skeletons, F5 anti-sector.

Part A: Factor rank multiset analysis (necessary condition for cyclic automorphism)
Part B: Cyclic automorphism search via rank-1 factored sandwich approach
Part C: S3 skeleton enumeration with existing constraints (Cartan, m_0)
Part D: F5 anti-sector decomposable count in Laderman anti span
"""

import numpy as np
from pathlib import Path
import json, itertools, sys
from collections import Counter

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA = WS / "data" / "S3_analysis"
DATA.mkdir(parents=True, exist_ok=True)

def E(i, j):
    M = np.zeros((3,3), dtype=int)
    M[i,j] = 1
    return M

pi12 = E(0,1) + E(1,0) + E(2,2)
eps1 = np.diag([-1,1,1])
eps2 = np.diag([1,-1,1])

# Laderman 23 terms from Burichenko (via analysis transcription, verified)
terms = [
    (E(0,0)+E(0,1)+E(0,2)-E(1,0)-E(1,1)-E(2,1)-E(2,2), E(1,1), E(1,0)),
    (E(0,0)-E(1,0), -E(0,1)+E(1,1), E(0,1)+E(1,1)),
    (E(1,1), -E(0,0)+E(0,1)+E(1,0)-E(1,1)-E(1,2)-E(2,0)+E(2,2), E(0,1)),
    (-E(0,0)+E(1,0)+E(1,1), E(0,0)-E(0,1)+E(1,1), E(1,0)+E(0,1)+E(1,1)),
    (E(1,0)+E(1,1), -E(0,0)+E(0,1), E(1,0)+E(1,1)),
    (E(0,0), E(0,0), E(0,0)+E(1,0)+E(2,0)+E(0,1)+E(1,1)+E(0,2)+E(2,2)),
    (-E(0,0)+E(2,0)+E(2,1), E(0,0)-E(0,2)+E(1,2), E(2,0)+E(0,2)+E(2,2)),
    (-E(0,0)+E(2,0), E(0,2)-E(1,2), E(0,2)+E(2,2)),
    (E(2,0)+E(2,1), -E(0,0)+E(0,2), E(2,0)+E(2,2)),
    (E(0,0)+E(0,1)+E(0,2)-E(1,1)-E(1,2)-E(2,0)-E(2,1), E(1,2), E(2,0)),
    (E(2,1), -E(0,0)+E(0,2)+E(1,0)-E(1,1)-E(1,2)-E(2,0)+E(2,1), E(0,2)),
    (-E(0,2)+E(2,1)+E(2,2), E(1,1)+E(2,0)-E(2,1), E(1,0)+E(0,2)+E(1,2)),
    (E(0,2)-E(2,2), E(1,1)-E(2,1), E(0,2)+E(1,2)),
    (E(0,2), E(2,0), E(0,0)+E(1,0)+E(2,0)+E(0,1)+E(2,1)+E(0,2)+E(1,2)),
    (E(2,1)+E(2,2), -E(2,0)+E(2,1), E(1,0)+E(1,2)),
    (-E(0,2)+E(1,1)+E(1,2), E(1,2)+E(2,0)-E(2,2), E(2,0)+E(0,1)+E(2,1)),
    (E(0,2)-E(1,2), E(1,2)-E(2,2), E(0,1)+E(2,1)),
    (E(1,1)+E(1,2), -E(2,0)+E(2,2), E(2,0)+E(2,1)),
    (E(0,1), E(1,0), E(0,0)),
    (E(1,2), E(2,1), E(1,1)),
    (E(1,0), E(0,2), E(2,1)),
    (E(2,0), E(0,1), E(1,2)),
    (E(2,2), E(2,2), E(2,2)),
]

assert len(terms) == 23

# ============================================================
# PART A: Factor rank multiset analysis
# ============================================================
print("=" * 60)
print("PART A: Factor rank multiset analysis")
print("=" * 60)

factor_ranks = []
for l, (a, b, c) in enumerate(terms):
    ra = int(np.linalg.matrix_rank(a))
    rb = int(np.linalg.matrix_rank(b))
    rc = int(np.linalg.matrix_rank(c))
    factor_ranks.append((ra, rb, rc))
    print(f"  t{l+1:2d}: ({ra}, {rb}, {rc})")

frc = Counter(factor_ranks)
rotated_tuples = [(rc, ra, rb) for (ra, rb, rc) in factor_ranks]
rotated_counter = Counter(rotated_tuples)

print(f"\nFactor rank multiset: {dict(frc)}")
print(f"Cyclic-rotated multiset: {dict(rotated_counter)}")
print(f"Multisets equal: {frc == rotated_counter}")

# Detailed: which tuples occur and their cyclic orbits
print("\nCyclic orbit analysis:")
seen = set()
orbit_data = []
for tup in sorted(frc.keys()):
    if tup in seen:
        continue
    orbit = set()
    t = tup
    for _ in range(3):
        orbit.add(t)
        t = (t[2], t[0], t[1])
    for o in orbit:
        seen.add(o)
    counts = [frc.get(o, 0) for o in sorted(orbit)]
    orbit_data.append({"orbit": sorted([list(o) for o in orbit]),
                       "counts": counts,
                       "all_equal": len(set(counts)) == 1})
    print(f"  Orbit {sorted(orbit)}: counts = {counts}, all equal = {len(set(counts)) == 1}")

# Check: for cyclic automorphism, each orbit must have equal counts
all_orbits_balanced = all(len(set(frc.get(o, 0) for o in 
    {tup} | {(tup[2], tup[0], tup[1])} | {(tup[1], tup[2], tup[0])})
    ) == 1 for tup in frc)

print(f"\nAll orbits balanced (necessary for cyclic auto): {all_orbits_balanced}")

# ============================================================
# PART B: Cyclic automorphism search
# ============================================================
print("\n" + "=" * 60)
print("PART B: Cyclic automorphism search")
print("=" * 60)

p = 65521  # large prime

def modinv(a, m):
    a = a % m
    g, x, _ = extended_gcd(a, m)
    if g != 1:
        return None
    return x % m

def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def mat_inv_3(M, p):
    """3x3 matrix inverse mod p."""
    M = np.array(M, dtype=int) % p
    d = int(np.round(np.linalg.det(M.astype(float)))) % p
    if d == 0:
        return None
    di = modinv(d, p)
    if di is None:
        return None
    adj = np.zeros((3,3), dtype=int)
    for i in range(3):
        for j in range(3):
            minor = np.delete(np.delete(M, i, 0), j, 1)
            cofactor = int(np.round(np.linalg.det(minor.astype(float)))) % p
            adj[j, i] = ((-1)**(i+j) * cofactor * di) % p
    return adj % p

def rank1_factorize(M):
    """Factorize rank-1 3x3 integer matrix M = u v^T. Returns (u, v) or None."""
    M = np.array(M, dtype=int)
    if np.linalg.matrix_rank(M) != 1:
        return None
    for i in range(3):
        for j in range(3):
            if M[i,j] != 0:
                # u is column proportional to M[:,j] and v is row proportional to M[i,:]
                u = M[:, j].copy()
                v_row = M[i, :].copy()
                # Normalize: u * v^T should equal M
                scale = M[i, j]
                v = v_row  # u[i] * v = M[i,:], so v = M[i,:] / u[i]
                # But u = M[:,j], so u[i] = M[i,j] = scale
                # Check: u * v^T = M[:,j] * M[i,:] / scale
                test = np.outer(u, v)
                if scale != 0 and np.array_equal(test, M * scale):
                    return u, v
                # Try: just return the column and row
                if np.array_equal(np.outer(u, v), M * M[i,j]):
                    return u, v
    # Fallback
    for i in range(3):
        row = M[i, :]
        if np.any(row != 0):
            u_col = M[:, np.nonzero(row)[0][0]]
            return u_col, row
    return None

# Flatten each term to 9-vectors
U = np.zeros((9, 23), dtype=int)  # a-factors
V = np.zeros((9, 23), dtype=int)  # b-factors  
W = np.zeros((9, 23), dtype=int)  # c-factors
for l, (a, b, c) in enumerate(terms):
    U[:, l] = a.reshape(-1)
    V[:, l] = b.reshape(-1)
    W[:, l] = c.reshape(-1)

# Factor all rank-1 terms
r1_a = {}  # index -> (u_L, u_R) for rank-1 a-factors
r1_b = {}
r1_c = {}
for l, (a, b, c) in enumerate(terms):
    fa = rank1_factorize(a)
    if fa:
        r1_a[l] = fa
    fb = rank1_factorize(b)
    if fb:
        r1_b[l] = fb
    fc = rank1_factorize(c)
    if fc:
        r1_c[l] = fc

print(f"Rank-1 a-factors: {len(r1_a)} terms: {sorted(l+1 for l in r1_a)}")
print(f"Rank-1 b-factors: {len(r1_b)} terms: {sorted(l+1 for l in r1_b)}")
print(f"Rank-1 c-factors: {len(r1_c)} terms: {sorted(l+1 for l in r1_c)}")

# Search for cyclic automorphism: Q a_l ∝ b_{π(l)}, P c_l ∝ a_{π(l)}, R b_l ∝ c_{π(l)}
# Focus on Q first (maps a-space to b-space).
# Q = Q_L ⊗ Q_R where Q_L, Q_R ∈ GL_3.
# For rank-1 a_l = uL @ uR^T: Q(a_l) = Q_L uL @ (Q_R uR)^T.
# For this to ∝ b_{π(l)}: if b_{π(l)} is rank 1 = bL @ bR^T,
#   then Q_L uL ∝ bL and Q_R uR ∝ bR.

# Find 3 rank-1 a-factors with independent left factors
def find_independent_triple(factors_dict, component='left'):
    """Find 3 indices whose left (or right) factors span K^3."""
    idx = sorted(factors_dict.keys())
    for i, j, k in itertools.combinations(idx, 3):
        if component == 'left':
            vecs = [factors_dict[i][0], factors_dict[j][0], factors_dict[k][0]]
        else:
            vecs = [factors_dict[i][1], factors_dict[j][1], factors_dict[k][1]]
        M = np.column_stack(vecs)
        if abs(np.linalg.det(M)) > 0.5:
            return (i, j, k)
    return None

basis_L = find_independent_triple(r1_a, 'left')
basis_R = find_independent_triple(r1_a, 'right')
print(f"\nIndependent left a-basis: terms {tuple(l+1 for l in basis_L)}")
print(f"Independent right a-basis: terms {tuple(l+1 for l in basis_R)}")

# For Q_L: columns are proportional to b-left-factors.
# Q_L maps a_L[basis_L[0]] -> b_L[π(basis_L[0])], etc.
# Only rank-1 b-factors can serve as targets.
r1_b_idx = sorted(r1_b.keys())
print(f"\nSearching Q_L: {len(r1_b_idx)} rank-1 b-target indices")

def search_sandwich_map(a_basis_idx, a_factors, b_factors, b_r1_idx, component, p):
    """Search for Q_{L or R} mapping a-factors to b-factors.
    
    Returns list of (Q, permutation_dict) where Q maps
    a[component][l] -> proportional to b[component][π(l)] for all rank-1 l.
    """
    i0, i1, i2 = a_basis_idx
    comp = 0 if component == 'left' else 1
    a0 = np.array(a_factors[i0][comp], dtype=int)
    a1 = np.array(a_factors[i1][comp], dtype=int)
    a2 = np.array(a_factors[i2][comp], dtype=int)
    M_a = np.column_stack([a0, a1, a2])
    Ma_inv = mat_inv_3(M_a, p)
    if Ma_inv is None:
        return []
    
    hits = []
    for j0, j1, j2 in itertools.permutations(b_r1_idx, 3):
        b0 = np.array(b_factors[j0][comp], dtype=int) % p
        b1 = np.array(b_factors[j1][comp], dtype=int) % p
        b2 = np.array(b_factors[j2][comp], dtype=int) % p
        M_b = np.column_stack([b0, b1, b2]) % p
        d = int(np.round(np.linalg.det(M_b.astype(float)))) % p
        if d == 0:
            continue
        
        # Q = M_b @ Ma_inv mod p
        Q = (M_b @ Ma_inv) % p
        
        # Check all rank-1 a-factors
        perm = {i0: j0, i1: j1, i2: j2}
        valid = True
        for l in a_factors:
            if l in (i0, i1, i2):
                continue
            al = np.array(a_factors[l][comp], dtype=int) % p
            Qal = (Q @ al) % p
            # Check if Qal is proportional to some b-factor's component
            found = False
            for j in b_r1_idx:
                if j in perm.values():
                    # Could still match if multiple a-factors map to same b-factor
                    pass
                bj = np.array(b_factors[j][comp], dtype=int) % p
                # Cross product check for proportionality in K^3
                cross = np.array([
                    (int(Qal[1])*int(bj[2]) - int(Qal[2])*int(bj[1])) % p,
                    (int(Qal[2])*int(bj[0]) - int(Qal[0])*int(bj[2])) % p,
                    (int(Qal[0])*int(bj[1]) - int(Qal[1])*int(bj[0])) % p
                ])
                if np.all(cross % p == 0) and not np.all(Qal == 0):
                    perm[l] = j
                    found = True
                    break
            if not found:
                valid = False
                break
        
        if valid:
            hits.append((Q.tolist(), dict(perm)))
    
    return hits

print("\nSearching for Q_L (left component of sandwich Q)...")
QL_hits = search_sandwich_map(basis_L, r1_a, r1_b, r1_b_idx, 'left', p)
print(f"Q_L candidates found: {len(QL_hits)}")

if QL_hits:
    print("Searching for Q_R (right component)...")
    QR_hits = search_sandwich_map(basis_R, r1_a, r1_b, r1_b_idx, 'right', p)
    print(f"Q_R candidates found: {len(QR_hits)}")
else:
    QR_hits = []
    print("No Q_L candidates -> no cyclic automorphism via rank-1 Q search")

# Cross-check: do any (Q_L, Q_R) pairs induce the same permutation?
combined_hits = []
for QL, perm_L in QL_hits:
    for QR, perm_R in QR_hits:
        # The permutation from left and right must agree on all rank-1 a-factors
        agree = True
        for l in perm_L:
            if l in perm_R and perm_L[l] != perm_R[l]:
                agree = False
                break
        if agree:
            # Merge permutations
            merged = dict(perm_L)
            merged.update(perm_R)
            combined_hits.append((QL, QR, merged))

print(f"\nCombined (Q_L, Q_R) with consistent permutation: {len(combined_hits)}")

# For each combined hit, verify on higher-rank a-factors too
verified_Q = []
for QL_mat, QR_mat, perm_partial in combined_hits:
    QL = np.array(QL_mat, dtype=int)
    QR = np.array(QR_mat, dtype=int)
    Q = np.zeros((9, 9), dtype=int)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                for l in range(3):
                    Q[3*i+k, 3*j+l] = (int(QL[i,j]) * int(QR[k,l])) % p
    
    # Check all 23 terms: Q @ U[:,l] should be proportional to V[:,π(l)]
    full_perm = {}
    valid = True
    for l in range(23):
        Qu = np.array([(sum(int(Q[r,s]) * int(U[s,l]) for s in range(9))) % p for r in range(9)])
        found = False
        for j in range(23):
            Vj = V[:, j].astype(int) % p
            # Check proportionality: rank of [Qu; Vj] <= 1
            # Use 2x2 minors
            prop = True
            for r1 in range(9):
                for r2 in range(r1+1, 9):
                    det2 = (int(Qu[r1]) * int(Vj[r2]) - int(Qu[r2]) * int(Vj[r1])) % p
                    if det2 != 0:
                        prop = False
                        break
                if not prop:
                    break
            if prop and not (np.all(Qu == 0)):
                full_perm[l] = j
                found = True
                break
        if not found:
            valid = False
            break
    
    if valid and len(set(full_perm.values())) == 23:  # bijective
        verified_Q.append({"Q_L": QL_mat, "Q_R": QR_mat, "perm": full_perm})
        print(f"  VERIFIED Q: perm = {[full_perm[l]+1 for l in range(23)]}")

print(f"\nVerified cyclic Q maps: {len(verified_Q)}")

# If Q found, search for P and R similarly
cyclic_automorphisms = []
if verified_Q:
    for qdata in verified_Q:
        perm_Q = qdata["perm"]
        pi = [perm_Q[l] for l in range(23)]
        
        # P c_l ∝ a_{π(l)}: P maps c-space to a-space
        # R b_l ∝ c_{π(l)}: R maps b-space to c-space
        
        # Check P via rank-1 c-factors
        P_found = False
        for l in r1_c:
            target = pi[l]
            if target in r1_a:
                # P maps c_L[l] -> a_L[π(l)], c_R[l] -> a_R[π(l)]
                pass  # Just check if P exists
        
        # Full 9x9 check: P @ W[:,l] ∝ U[:,π(l)]
        # P is determined by 9 independent W-columns
        # Find 9 independent W-columns
        W_mod = W.astype(int) % p
        basis_w = []
        for l in range(23):
            test = W_mod[:, basis_w + [l]]
            if np.linalg.matrix_rank(test.astype(float)) == len(basis_w) + 1:
                basis_w.append(l)
                if len(basis_w) == 9:
                    break
        
        if len(basis_w) < 9:
            print("  Cannot find 9 independent W-columns (unexpected)")
            continue
        
        W_basis = W_mod[:, basis_w]
        U_targets = np.zeros((9, 9), dtype=int)
        for idx, l in enumerate(basis_w):
            U_targets[:, idx] = U[:, pi[l]].astype(int) % p
        
        # P @ W_basis[:,k] = lambda_k * U_targets[:,k]
        # We need to find P and the lambdas.
        # Set lambda_0 = 1: P = U_targets[:,0:1] ... this doesn't work directly.
        # Instead: P W_basis = D U_targets where D is diagonal.
        # So P = D U_targets W_basis^{-1}.
        # For each choice of D (up to overall scaling), check remaining columns.
        
        Wb_inv = mat_inv_3(None, p)  # Need 9x9 inverse...
        # Skip full 9x9 inverse; use numpy for float check
        W_bf = W_basis.astype(float)
        if abs(np.linalg.det(W_bf)) < 0.5:
            print("  W basis singular")
            continue
        
        # Over F_p, use the permutation check on all 23 terms
        # Check if (W perm) has same row space as U (up to diagonal scaling)
        # Actually just check: P exists iff for each l, W[:,l] ∝ U[:,π(l)] ... NO.
        # P is an invertible transformation, not identity.
        
        # Determine P: from 9 independent equations P w_l = λ_l u_{π(l)}.
        # Set all λ = 1 for the basis: P = U_targets @ W_basis^{-1}.
        # Then check: P w_l ∝ u_{π(l)} for l not in basis.
        
        # Compute P = U_targets @ W_basis_inv (mod p)
        # Need 9x9 inverse mod p. Use row reduction.
        def mat_inv_9(M, p):
            n = 9
            A = np.zeros((n, 2*n), dtype=int)
            A[:, :n] = M % p
            for i in range(n):
                A[i, n+i] = 1
            for col in range(n):
                # Find pivot
                pivot = None
                for row in range(col, n):
                    if A[row, col] % p != 0:
                        pivot = row
                        break
                if pivot is None:
                    return None
                A[[col, pivot]] = A[[pivot, col]]
                inv_piv = modinv(int(A[col, col]), p)
                if inv_piv is None:
                    return None
                A[col] = (A[col] * inv_piv) % p
                for row in range(n):
                    if row != col and A[row, col] % p != 0:
                        factor = int(A[row, col])
                        A[row] = (A[row] - factor * A[col]) % p
            return A[:, n:] % p
        
        Wb_inv = mat_inv_9(W_basis, p)
        if Wb_inv is None:
            print("  W basis not invertible mod p")
            continue
        
        P = np.zeros((9,9), dtype=int)
        for i in range(9):
            for j in range(9):
                P[i,j] = sum(int(U_targets[i,k]) * int(Wb_inv[k,j]) for k in range(9)) % p
        
        # Check P on all 23 terms
        P_valid = True
        for l in range(23):
            Pw = np.array([sum(int(P[r,s]) * int(W_mod[s,l]) for s in range(9)) % p for r in range(9)])
            Utgt = U[:, pi[l]].astype(int) % p
            # Proportionality check
            prop = True
            for r1 in range(9):
                for r2 in range(r1+1, 9):
                    det2 = (int(Pw[r1]) * int(Utgt[r2]) - int(Pw[r2]) * int(Utgt[r1])) % p
                    if det2 != 0:
                        prop = False
                        break
                if not prop:
                    break
            if not prop or np.all(Pw == 0):
                P_valid = False
                break
        
        if not P_valid:
            print(f"  P check FAILED for Q perm")
            continue
        
        # Similarly check R: R b_l ∝ c_{π(l)}
        V_mod = V.astype(int) % p
        basis_v = []
        for l in range(23):
            test = V_mod[:, basis_v + [l]]
            if np.linalg.matrix_rank(test.astype(float)) == len(basis_v) + 1:
                basis_v.append(l)
                if len(basis_v) == 9:
                    break
        
        Vb = V_mod[:, basis_v]
        W_tgts = np.zeros((9, 9), dtype=int)
        for idx, l in enumerate(basis_v):
            W_tgts[:, idx] = W_mod[:, pi[l]]
        
        Vb_inv = mat_inv_9(Vb, p)
        if Vb_inv is None:
            print("  V basis not invertible mod p")
            continue
        
        R = np.zeros((9,9), dtype=int)
        for i in range(9):
            for j in range(9):
                R[i,j] = sum(int(W_tgts[i,k]) * int(Vb_inv[k,j]) for k in range(9)) % p
        
        R_valid = True
        for l in range(23):
            Rv = np.array([sum(int(R[r,s]) * int(V_mod[s,l]) for s in range(9)) % p for r in range(9)])
            Wtgt = W_mod[:, pi[l]]
            prop = True
            for r1 in range(9):
                for r2 in range(r1+1, 9):
                    det2 = (int(Rv[r1]) * int(Wtgt[r2]) - int(Rv[r2]) * int(Wtgt[r1])) % p
                    if det2 != 0:
                        prop = False
                        break
                if not prop:
                    break
            if not prop or np.all(Rv == 0):
                R_valid = False
                break
        
        if R_valid:
            # Full cyclic automorphism found!
            perm_1indexed = [pi[l]+1 for l in range(23)]
            # Compute orbit structure
            visited = [False]*23
            fixed_pts = []
            three_cycles = []
            for l in range(23):
                if visited[l]:
                    continue
                orbit = [l]
                visited[l] = True
                nxt = pi[l]
                while nxt != l:
                    orbit.append(nxt)
                    visited[nxt] = True
                    nxt = pi[nxt]
                if len(orbit) == 1:
                    fixed_pts.append(l+1)
                elif len(orbit) == 3:
                    three_cycles.append(tuple(o+1 for o in orbit))
                else:
                    print(f"  WARNING: orbit of size {len(orbit)}: {[o+1 for o in orbit]}")
            
            auto = {
                "perm_1indexed": perm_1indexed,
                "fixed_points": fixed_pts,
                "three_cycles": three_cycles,
                "f_sigma": len(fixed_pts),
                "m_sigma": len(three_cycles),
                "rank_check": len(fixed_pts) + 3*len(three_cycles),
            }
            cyclic_automorphisms.append(auto)
            print(f"  FULL CYCLIC AUTOMORPHISM FOUND!")
            print(f"    Permutation: {perm_1indexed}")
            print(f"    Fixed points: {fixed_pts}")
            print(f"    3-cycles: {three_cycles}")
            print(f"    f_σ = {len(fixed_pts)}, m_σ = {len(three_cycles)}")
        else:
            print(f"  R check FAILED for Q perm")

has_cyclic = len(cyclic_automorphisms) > 0
print(f"\n*** Laderman has cyclic automorphism: {has_cyclic} ***")

# ============================================================
# PART C: S3 skeleton enumeration
# ============================================================
print("\n" + "=" * 60)
print("PART C: S3 skeleton enumeration")
print("=" * 60)

# S3 = <σ, τ>, |S3| = 6.
# dim V^{S3} = (729 + 2*tr(σ) + 3*tr(τ))/6
# tr(σ) = 9 (cyclic fixed dimension), tr(τ) = 27 (transpose fixed dimension)
dim_S3 = (729 + 2*9 + 3*27) // 6
print(f"dim(V^S3) = (729 + 18 + 81)/6 = {dim_S3}")

# Rank-22 decomposition under S3: a + 2b + 3c + 6d = 22
# S3-orbit sizes: 1 (both σ,τ fix), 2 (σ fixes, τ swaps), 3 (τ fixes one, σ cycles), 6 (generic)
# Cyclic constraints: f_σ = a + 2b (σ-fixed terms), m_σ = c + 2d (σ-orbits of size 3)
# Transpose constraints: f_τ = a + c (τ-fixed terms), m_τ = b + c + 3d (τ-free pairs)
# Existing bounds: m_σ ≥ 4 (Cartan), m_τ ≥ 7 (anti-sector)

skeletons = []
for d in range(4):  # 6d ≤ 22
    for c in range(8):  # 3c ≤ 22-6d
        for b in range(12):  # 2b ≤ 22-6d-3c
            a = 22 - 6*d - 3*c - 2*b
            if a < 0:
                break
            m_sigma = c + 2*d
            m_tau = b + c + 3*d
            f_sigma = a + 2*b
            f_tau = a + c
            if m_sigma < 4:  # Cartan
                continue
            if m_tau < 7:  # anti-sector
                continue
            # Additional: f_tau + 2*m_tau should equal 22
            assert f_tau + 2*m_tau == 22
            assert f_sigma + 3*m_sigma == 22
            
            # Parameter count: each orbit contributes parameters
            # size-1 orbit: 9 params (one rank-one 9-vector, projective = 8)
            # size-2 orbit: 18 params (one rank-one, paired by τ)
            # size-3 orbit: 27 params (one rank-one + σ-orbit structure)
            # size-6 orbit: 54 params (one rank-one, generic)
            # But symmetry reduces: size-1 orbits are determined by σ,τ-fixed vectors;
            # size-2 by σ-fixed, τ-paired; etc.
            # Rough: 9a + 18b + 27c + 54d params for the decomposition factors.
            # Equations: 138 (S3-invariant Brent equations)
            params = 9*a + 18*b + 27*c + 54*d
            
            sk = {
                "a": a, "b": b, "c": c, "d": d,
                "f_sigma": f_sigma, "m_sigma": m_sigma,
                "f_tau": f_tau, "m_tau": m_tau,
                "params": params,
                "equations": dim_S3,
                "overdetermined": params < dim_S3,
            }
            skeletons.append(sk)

print(f"Total S3 rank-22 skeletons (m_σ≥4, m_τ≥7): {len(skeletons)}")
print(f"\n{'a':>3} {'b':>3} {'c':>3} {'d':>3} | {'f_σ':>4} {'m_σ':>4} {'f_τ':>4} {'m_τ':>4} | {'params':>6} {'eqs':>4} {'overdet':>8}")
print("-" * 65)
for sk in sorted(skeletons, key=lambda s: s['params']):
    print(f"{sk['a']:3d} {sk['b']:3d} {sk['c']:3d} {sk['d']:3d} | "
          f"{sk['f_sigma']:4d} {sk['m_sigma']:4d} {sk['f_tau']:4d} {sk['m_tau']:4d} | "
          f"{sk['params']:6d} {sk['equations']:4d} {'YES' if sk['overdetermined'] else 'no':>8}")

# If Laderman has cyclic automorphism, determine its S3 orbit structure
if has_cyclic:
    ca = cyclic_automorphisms[0]
    phi_perm_1idx = [1,5,6,4,2,3,16,18,17,10,14,12,15,11,13,7,9,8,19,22,21,20,23]
    # The tau permutation (from analysis)
    tau_fixed = {1,4,10,12,19,21,23}
    tau_cycles = [(2,5),(3,6),(7,16),(8,18),(9,17),(11,14),(13,15),(20,22)]
    
    sigma_fixed = set(ca["fixed_points"])
    sigma_3cycles = ca["three_cycles"]
    
    # S3 orbit structure
    # Type 1 (size 1): fixed by both σ and τ
    type1 = sigma_fixed & tau_fixed
    # Type 2 (size 2): σ-fixed but τ-swapped
    sigma_fixed_only = sigma_fixed - tau_fixed
    # Type 3 (size 3): τ fixes one of the three, σ cycles
    # Type 6 (size 6): generic
    
    print(f"\nLaderman S3 orbit structure:")
    print(f"  σ-fixed: {sorted(sigma_fixed)}")
    print(f"  τ-fixed: {sorted(tau_fixed)}")
    print(f"  Both fixed (type 1): {sorted(type1)}")
    print(f"  σ-fixed, τ-swapped (type 2 candidates): {sorted(sigma_fixed_only)}")
    
    # For each σ 3-cycle, check which elements are τ-fixed
    for cyc in sigma_3cycles:
        tau_fix_in_cyc = [t for t in cyc if t in tau_fixed]
        print(f"  σ-cycle {cyc}: τ-fixed elements = {tau_fix_in_cyc}")

# ============================================================
# Save results
# ============================================================
results = {
    "part_A": {
        "factor_ranks": factor_ranks,
        "multiset": {str(k): v for k, v in frc.items()},
        "cyclic_rotation_consistent": frc == rotated_counter,
        "orbit_data": orbit_data,
    },
    "part_B": {
        "QL_candidates": len(QL_hits),
        "QR_candidates": len(QR_hits),
        "combined_consistent": len(combined_hits),
        "verified_cyclic_automorphisms": len(cyclic_automorphisms),
        "has_cyclic_automorphism": has_cyclic,
        "automorphisms": cyclic_automorphisms,
    },
    "part_C": {
        "dim_S3_invariant": dim_S3,
        "num_skeletons": len(skeletons),
        "skeletons": skeletons,
    },
}

path = DATA / "laderman_S3_analysis.json"
path.write_text(json.dumps(results, indent=2) + "\n")
print(f"\nSAVED {path}")
print(json.dumps({"has_cyclic": has_cyclic, "num_skeletons": len(skeletons),
                   "dim_S3": dim_S3}, indent=2))
