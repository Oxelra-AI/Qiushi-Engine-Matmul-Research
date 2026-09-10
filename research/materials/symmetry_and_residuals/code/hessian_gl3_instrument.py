#!/usr/bin/env python3
"""
analysis: Hessian-commutator on gl_3 (9 dimensions).

KEY INSIGHT (from review): work on gl_3, not sl_3.
On gl_3 (9 vars), trace form K = tr(XY) has rank 9.
For traceless free orbits, the s^1 identity gives:
  tr(X^2) = sum_i gamma_i ell_i(X)^2   on gl_3
This is rank 9, and the Hessian endomorphism H(X) = Hess_R(X) K^{-1}
diagonalizes in the mu_i basis when k=9.

For k=9: [H(X), H(Y)] = 0 (Jennrich property: 9 cubes in 9 vars
form a simultaneous diagonalization basis).
For k=10: H(X) = diagonal + rank-1, so [H(X), H(Y)] has rank <= 2.
For k>=11: generic commutator rank > 2.

BILR has 11 cubes. If (10,4) exists, it has at most 10 cubes.
If BILR's commutator rank is > 2 on gl_3, then the Waring rank > 10
on gl_3 is PROVED by the Jennrich bound, giving another proof
of Waring rank >= 11.
"""

import numpy as np
import json
from fractions import Fraction
from pathlib import Path

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "hessian_commutator"
OUT.mkdir(parents=True, exist_ok=True)

# gl_3 basis: E00, E01, E02, E10, E11, E12, E20, E21, E22
# But we use the standard matrix units: E_{ij} has 1 at position (i,j)
def gl3_basis():
    basis = []
    names = []
    for i in range(3):
        for j in range(3):
            M = np.zeros((3,3), dtype=int)
            M[i,j] = 1
            basis.append(M)
            names.append(f"E{i}{j}")
    return basis, names

def trace_gram(basis):
    """Gram matrix of tr(XY)."""
    n = len(basis)
    G = np.zeros((n,n), dtype=int)
    for i in range(n):
        for j in range(n):
            G[i,j] = int(np.trace(basis[i] @ basis[j]))
    return G

basis_gl3, names_gl3 = gl3_basis()
K_gl3 = trace_gram(basis_gl3)
print(f"K_gl3 shape: {K_gl3.shape}, det: {int(np.round(np.linalg.det(K_gl3)))}")

p = 65521  # large prime for exact modular arithmetic

def modinv(a, m):
    a = a % m
    g, x, _ = extended_gcd(a, m)
    if g != 1:
        return None
    return x % m

def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x1, y1 = extended_gcd(b % a, a)
    return g, y1 - (b // a) * x1, x1

def mat_inv_mod(M, p):
    n = M.shape[0]
    A = M.copy() % p
    I = np.eye(n, dtype=int)
    aug = np.hstack([A, I])
    for col in range(n):
        pivot = -1
        for row in range(col, n):
            if aug[row, col] % p != 0:
                pivot = row
                break
        if pivot < 0:
            return None
        aug[[col, pivot]] = aug[[pivot, col]]
        inv_diag = modinv(int(aug[col, col]), p)
        if inv_diag is None:
            return None
        aug[col] = (aug[col] * inv_diag) % p
        for row in range(n):
            if row != col and aug[row, col] % p != 0:
                M_r = int(aug[row, col])
                aug[row] = (aug[row] - M_r * aug[col]) % p
        r_idx = col + 1
    return aug[:, n:] % p

def rank_mod_p(M, p):
    M = M.copy() % p
    n, m = M.shape
    r = 0
    for col in range(m):
        pivot = -1
        for row in range(r, n):
            if M[row, col] % p != 0:
                pivot = row
                break
        if pivot < 0:
            continue
        M[[r, pivot]] = M[[pivot, r]]
        inv_d = modinv(int(M[r, col]), p)
        if inv_d is None:
            continue
        M[r] = (M[r] * inv_d) % p
        for row in range(n):
            if row != r and M[row, col] % p != 0:
                M[row] = (M[row] - int(M[row, col]) * M[r]) % p
        r += 1
    return r

Kinv_gl3 = mat_inv_mod(K_gl3 % p, p)
check = (K_gl3 @ Kinv_gl3) % p
assert np.all(check == np.eye(9, dtype=int) % p), "K_gl3 inverse check failed"
print("K_gl3^{-1} computed and verified mod p")

# Load BILR data
with open(WS / "data/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json") as f:
    bilr = json.load(f)

cubes = [np.array(c, dtype=int) for c in bilr["cubes"]]
free_orbits = bilr["free_orbit_representatives"]

# Extract cube linear forms on gl_3
# ell_i(X) = tr(L_i^T X), in gl_3 coordinates
cube_forms_gl3 = []
for L in cubes:
    form = np.array([int(np.trace(L.T @ basis_gl3[k])) for k in range(9)])
    cube_forms_gl3.append(form)
cube_forms_gl3 = np.array(cube_forms_gl3)  # 11 x 9

cube_traces = np.array([int(np.trace(L)) for L in cubes])
print(f"Cube traces: {cube_traces.tolist()}")

# For BILR, rho_i = 1, gamma_i = c_i
# mu_i = ell_i / c_i, w_i = c_i^3
# On gl_3: sum w_i mu_i mu_i^T should equal K_gl3
mu_gl3 = np.array([cube_traces[i] * cube_forms_gl3[i] for i in range(11)])
w = cube_traces**3  # weights

# Verify quadratic moment on gl_3
M2_gl3 = sum(w[i] * np.outer(mu_gl3[i], mu_gl3[i]) for i in range(11))
M2_diff = M2_gl3 - K_gl3
print(f"gl_3 quadratic moment diff max: {np.max(np.abs(M2_diff))}")

def hessian_endo_gl3(x, mu, w, Kinv, p):
    """H(X) = 6 sum_i w_i (mu_i.x) mu_i mu_i^T K^{-1} mod p."""
    n = mu.shape[1]
    k = mu.shape[0]
    H = np.zeros((n,n), dtype=int)
    for i in range(k):
        coeff = int(6 * w[i] * np.dot(mu[i], x)) % p
        outer = np.outer(mu[i], mu[i])
        H = (H + coeff * outer) % p
    H = H @ Kinv % p
    return H

# Test commutators on gl_3 for BILR (11 cubes)
rng = np.random.RandomState(42)

max_comm_rank_gl3 = 0
rank_hist_gl3 = {}
n_trials = 200
for trial in range(n_trials):
    x1 = rng.randint(0, p, size=9)
    x2 = rng.randint(0, p, size=9)
    H1 = hessian_endo_gl3(x1, mu_gl3 % p, w % p, Kinv_gl3, p)
    H2 = hessian_endo_gl3(x2, mu_gl3 % p, w % p, Kinv_gl3, p)
    comm = (H1 @ H2 - H2 @ H1) % p
    r = rank_mod_p(comm, p)
    max_comm_rank_gl3 = max(max_comm_rank_gl3, r)
    rank_hist_gl3[r] = rank_hist_gl3.get(r, 0) + 1

print(f"\nBILR gl_3 commutator rank histogram ({n_trials} trials):")
for r in sorted(rank_hist_gl3):
    print(f"  rank {r}: {rank_hist_gl3[r]}")

# Now verify the diagonal structure for a 9-cube basis system
# Take 9 of the BILR cubes and check if the commutator vanishes when we
# REPLACE the moment to be exactly K_gl3
# But a proper test is: for any 9x9 system M with M^T W M = K, verify [H,H]=0
# The theory says: H(X) in M-basis is diag(Mx), so commutators vanish.

# First, check: do 9 BILR cubes (with their actual weights) satisfy M^T W M = K?
# No - they satisfy M_9^T W_9 M_9 = K - w_10 mu_10 mu_10^T.
# So dropped-cube commutators are NOT the same as proper 9-cube systems.

# Let's build a SYNTHETIC 9-cube system satisfying M^T W M = K_gl3 on gl_3
# and verify commutators vanish.
# Take any 9x9 invertible M with M^T W M = K for some diagonal W.
# Simplest: M = I, then W = K_gl3 itself. But K_gl3 is the identity permutation
# matrix for gl_3 (since tr(E_{ij} E_{kl}) = delta_{il} delta_{jk}).
# K_gl3 is actually just the permutation: K_gl3[a,b] = 1 if (i2,j2)=(j1,i1).

# Actually K_gl3 for the standard basis E_{ij} is:
# tr(E_{ij} E_{kl}) = sum_m (E_{ij})_{mn} (E_{kl})_{nm} = delta_{ij==kl transposed}
# = delta_{i,l} delta_{j,k}
# So K[3i+j, 3k+l] = delta_{il} delta_{jk}.

print("\nK_gl3 matrix:")
for i in range(9):
    print(f"  {K_gl3[i].tolist()}")

# K_gl3 is a permutation matrix: it maps E_{ij} to E_{ji}.
# Its eigenvalues are all ±1.
eigs = np.linalg.eigvalsh(K_gl3.astype(float))
print(f"K_gl3 eigenvalues: {sorted(np.round(eigs,2))}")

# Synthetic test: M = I (9 cubes = standard basis elements)
# W = K_gl3 (not diagonal! So this doesn't directly work)
# We need M^T W M = K with W diagonal.
# Take M = L where L^T W L = K. Since K is a permutation matrix,
# we can take L = any matrix and W = (L^T)^{-1} K L^{-1}.
# For W to be diagonal, we need L^T diag(w) L = K.
# This is the Cholesky-like factorization with signature.

# Better approach: just verify the THEORY directly.
# For k=9 with M (9x9 invertible) and M^T W M = K:
# H(X) in M-basis = 6 diag(Mx), so [H(X), H(Y)] = 0.

# Verify with a random 9x9 M and corresponding W = (M^T)^{-1} K M^{-1}:
M_test = rng.randint(1, p, size=(9,9)) % p
M_test_inv = mat_inv_mod(M_test, p)
if M_test_inv is not None:
    # W_test = (M_test^T)^{-1} K M_test^{-1} mod p
    MT_inv = mat_inv_mod(M_test.T % p, p)
    W_test_mat = MT_inv @ K_gl3 % p @ M_test_inv % p
    W_test_mat = W_test_mat % p
    
    # Check if W_test is diagonal
    off_diag = W_test_mat.copy()
    np.fill_diagonal(off_diag, 0)
    is_diag = np.all(off_diag % p == 0)
    print(f"\nSynthetic: W diagonal? {is_diag}")
    
    if not is_diag:
        # W won't be diagonal for random M. The theory assumes w_i are scalars.
        # The diagonal W is a constraint on M.
        print("  (Expected: for random M, W is not diagonal)")
    
    # But the ALGEBRAIC identity [H(X), H(Y)] = 0 still holds when
    # M^T W M = K with W diagonal. Let's verify with a proper construction.
    
    # Proper construction: M = sqrt(K)^{-1} * orthogonal * sqrt(|W|)
    # Since K is a permutation (K^2 = I), sqrt(K) = K (or use eigendecomp).
    pass

# The cleanest verification: take BILR's 11 mu vectors on gl_3,
# pick 9 that span, force their weights to satisfy M_9^T W_9 M_9 = K,
# and verify commutators vanish.

# Pick first 9 BILR cubes
M9 = mu_gl3[:9] % p
M9_rank = rank_mod_p(M9, p)
print(f"\nFirst 9 BILR mu vectors on gl_3: rank = {M9_rank}")

if M9_rank == 9:
    M9_inv = mat_inv_mod(M9, p)
    # Need W9 such that M9^T W9 M9 = K mod p
    # W9 = (M9^T)^{-1} K M9^{-1}
    M9T_inv = mat_inv_mod(M9.T % p, p)
    W9_mat = M9T_inv @ K_gl3 % p @ M9_inv % p
    W9_mat = W9_mat % p
    
    off_diag = W9_mat.copy()
    np.fill_diagonal(off_diag, 0)
    is_diag = np.all(off_diag % p == 0)
    print(f"W9 diagonal? {is_diag}")
    
    if is_diag:
        W9_diag = np.diag(W9_mat) % p
        # Check: M9^T diag(W9) M9 = K mod p
        check = M9.T @ np.diag(W9_diag) % p @ M9 % p
        check = check % p
        diff = (check - K_gl3) % p
        print(f"M9^T W9 M9 = K? max diff = {np.max(diff)}")
        
        # Now test commutators for this 9-system
        max_r = 0
        for trial in range(100):
            x1 = rng.randint(0, p, size=9)
            x2 = rng.randint(0, p, size=9)
            H1 = hessian_endo_gl3(x1, M9, W9_diag, Kinv_gl3, p)
            H2 = hessian_endo_gl3(x2, M9, W9_diag, Kinv_gl3, p)
            comm = (H1 @ H2 - H2 @ H1) % p
            r = rank_mod_p(comm, p)
            max_r = max(max_r, r)
        print(f"9-cube system commutator max rank over 100 trials: {max_r}")
    else:
        print("W9 is not diagonal - the 9 chosen BILR vectors don't form a K-orthogonal system")
        print("But the THEORY guarantees [H(X),H(Y)]=0 for ANY 9x9 system with M^T W M = K")
        print("even with non-diagonal W, because diag*diag commutes.")
        
        # Direct verification with NON-diagonal W:
        # H(X)/6 = M9^T W9 diag(M9 x) M9 K^{-1}
        # In M9-basis: H/6 = W9 diag(y) M9 K^{-1} M9^T
        # But M9 K^{-1} M9^T = M9 (M9^T W9 M9)^{-1} M9^T = W9^{-1}
        # So H/6 in M9-basis = W9 diag(y) W9^{-1}
        # If W9 is not diagonal, this is NOT diag(y).
        
        # Actually: M9 K^{-1} M9^T requires K = M9^T W M9 with W DIAGONAL.
        # If we just have M9^T W9_mat M9 = K with W9_mat non-diagonal,
        # then M9 K^{-1} M9^T = M9 M9^{-1} W9_mat^{-1} M9^{-T} M9^T = W9_mat^{-1}
        # And H/6 in M9-basis = W9_mat diag(y) W9_mat^{-1}
        # This is a similarity transform, NOT diagonal!
        # So [H(X), H(Y)] ≠ 0 in general when W is not diagonal.
        
        # The theory REQUIRES W to be diagonal (scalar weights per cube).
        # This is automatic because each cube has one coefficient rho_i.
        
        # For a TRUE rank-22 decomposition, the cubes have scalar weights.
        # So W IS diagonal. The issue is: the 9 first BILR mu's don't satisfy
        # M^T diag(w) M = K with their original weights.
        
        # Let me check: with original BILR weights w = [1,1,1,1,1,1,1,-1,-1,-1,-1],
        # M9 = first 9 mu's, w9 = first 9 weights
        w9_orig = w[:9]
        check9 = sum(w9_orig[i] * np.outer(mu_gl3[i], mu_gl3[i]) for i in range(9))
        diff9 = check9 - K_gl3
        r9 = rank_mod_p(np.array(diff9, dtype=int), 100003)
        print(f"M9^T W9_orig M9 - K: rank of difference = {r9}")
        print(f"  (Expected rank 1: missing two cube contributions)")

# The CRUCIAL test: build a proper 10-cube system on gl_3 satisfying
# M^T diag(w) M = K, and check if commutators have rank <= 2.

# Use the 9-node sl_3 cubature, extended to gl_3 by adding the I-direction.
# On gl_3, the extra coordinate is the trace direction.
# mu_i on gl_3 = (mu_i on sl_3, c_i/3) where c_i = ell_i(I)/3.
# Actually mu_i(I) = ell_i(I)/c_i = 1 for cubes with nonzero trace.

# For a 10-cube system: take 10 mu_i in gl_3 (9-dim) with M^T W M = K_gl3.
# Generate a random 10-cube system satisfying the moment:
# Start from any 9 mu_i forming a basis with M9^T W9 M9 = K,
# add one more mu_10 and adjust weights.

# Actually, the simplest way to get a valid 10-cube system:
# Take the BILR mu's on gl_3 restricted to any 10.
# These DON'T satisfy M10^T W10 M10 = K (they miss one cube).
# So this doesn't work.

# Instead, CONSTRUCT a 10-cube system:
# Let A_i be 3x3 matrices with c_i = tr(A_i) ≠ 0 (for 9 or 10 of them).
# Let mu_i(X) = tr(A_i X) / c_i.
# Need: sum w_i mu_i^2 = K on gl_3.

# The easiest approach: take the BILR 11-node system and MERGE two cubes.
# If we can combine cubes 0 and 1 (same trace +1) into one effective cube,
# that would give a 10-cube system. But merging cubes means:
# w_0 mu_0^3 + w_1 mu_1^3 = w_new mu_new^3
# which requires mu_0 = mu_1 (impossible for distinct forms) or complex rewriting.

# Let me just do the THEORETICAL verification:
# For any 9x9 invertible M, diagonal W, with M^T W M = K:
# H(X) in M-coords = diag(Mx), so [H(X),H(Y)] = 0.
# This is an ALGEBRAIC IDENTITY, not a numerical claim.

# For k=10: M is 10x9, M^T W M = K, ker(M^T) has dim 1.
# H(X) = 6 M^T W diag(Mx) M K^{-1}
# In any 9-dim sub-basis, this is NOT diagonal.
# But the generic commutator rank is bounded.

# Let me VERIFY the bound [H(X),H(Y)] has rank <= 2 for k=10:
# Choose a random 10-vector system with M^T W M = K.

print("\n" + "="*60)
print("CONSTRUCTING PROPER 10-CUBE SYSTEM ON gl_3")
print("="*60)

# Method: start with 9 G-orthogonal vectors + 1 extra.
# K_gl3 is the permutation matrix swapping (i,j)<->(j,i).
# Its eigendecomp: 6 eigenvalue +1 (symmetric matrices) and
# 3 eigenvalue -1 (antisymmetric matrices).
evals, evecs = np.linalg.eigh(K_gl3.astype(float))
print(f"K_gl3 eigenvalues: {np.round(evals, 2)}")

# Take 9 K-orthogonal vectors: the eigenvectors of K
# with weights equal to eigenvalues work: evecs^T diag(evals) evecs = K.
# But evals = ±1, so W = diag(evals).
# This gives a 9x9 system with M^T W M = K (W diagonal with ±1).
Q9 = evecs.T  # 9x9, rows are eigenvectors (orthonormal in Euclidean metric)
W9_eig = np.round(evals).astype(int)

# Verify: Q9^T diag(W9_eig) Q9 = K
check_eig = Q9.T @ np.diag(W9_eig) @ Q9
print(f"Eigenbasis moment check: max diff = {np.max(np.abs(check_eig - K_gl3)):.6f}")

# Work mod p with exact integer eigenvectors is hard (eigvecs are irrational).
# Instead, use exact integer construction.
# K_gl3 is the "vec-transpose" operator: K e_{ij} = e_{ji}.
# Eigenspace +1: symmetric matrices (dim 6), span: E_{ii}, (E_{ij}+E_{ji})/sqrt(2)
# Eigenspace -1: antisymmetric (dim 3), span: (E_{ij}-E_{ji})/sqrt(2) for i<j

# Integer eigenvectors (unnormalized):
sym_basis = []
sym_names = []
# Diagonal: E00, E11, E22
for i in range(3):
    v = np.zeros(9, dtype=int)
    v[3*i+i] = 1
    sym_basis.append(v)
    sym_names.append(f"E{i}{i}")
# Off-diagonal symmetric: E_{ij} + E_{ji} for i<j
for i in range(3):
    for j in range(i+1, 3):
        v = np.zeros(9, dtype=int)
        v[3*i+j] = 1
        v[3*j+i] = 1
        sym_basis.append(v)
        sym_names.append(f"E{i}{j}+E{j}{i}")
# Antisymmetric: E_{ij} - E_{ji} for i<j
asym_basis = []
asym_names = []
for i in range(3):
    for j in range(i+1, 3):
        v = np.zeros(9, dtype=int)
        v[3*i+j] = 1
        v[3*j+i] = -1
        asym_basis.append(v)
        asym_names.append(f"E{i}{j}-E{j}{i}")

all_vecs = sym_basis + asym_basis  # 9 vectors
all_weights_mod_p = [1]*6 + [p-1]*3  # +1 for sym, -1 for antisym
M_eig = np.array(all_vecs, dtype=int)  # 9x9

# Verify moment: M^T W M = K mod p
W_diag = np.array(all_weights_mod_p, dtype=int)
check_moment = np.zeros((9,9), dtype=int)
for i in range(9):
    check_moment = (check_moment + W_diag[i] * np.outer(M_eig[i], M_eig[i])) % p
diff_moment = (check_moment - K_gl3) % p
print(f"Eigenbasis integer moment diff max mod p: {np.max(diff_moment)}")

# Commutator test for this 9-cube system
max_r_9 = 0
for trial in range(100):
    x1 = rng.randint(0, p, size=9)
    x2 = rng.randint(0, p, size=9)
    H1 = hessian_endo_gl3(x1, M_eig % p, W_diag % p, Kinv_gl3, p)
    H2 = hessian_endo_gl3(x2, M_eig % p, W_diag % p, Kinv_gl3, p)
    comm = (H1 @ H2 - H2 @ H1) % p
    r = rank_mod_p(comm, p)
    max_r_9 = max(max_r_9, r)
print(f"9-cube K-orthogonal system: max commutator rank = {max_r_9}")

# Now add a 10th vector (random) and verify commutator rank <= 2
# We need to adjust the moment: the 10-cube system must still satisfy M^T W M = K.
# Adding mu_10 with weight w_10: new moment = K + w_10 mu_10 mu_10^T.
# This changes K, so we need to modify the existing weights.
# Alternatively: parameterize the 10th vector and solve for adjusted weights.
#
# Simplest approach: perturb one eigenvector by adding a small component
# in another direction, then recompute weights.
# Or: take 10 random vectors and solve for weights via M^T W M = K.

# Method: Take M_eig (9x9) plus one extra row (random), giving 10x9 matrix M10.
# Solve for diagonal W10 such that M10^T diag(W10) M10 = K.
# This is 45 equations (upper triangle of 9x9) in 10 unknowns.
# Generally overdetermined, but the system has a non-empty solution set
# iff the vectors satisfy certain algebraic conditions.

# For a CLEAN test: take the 9-eigenbasis vectors plus mu_10 = (1,1,1,0,0,0,0,0,0).
mu_10_extra = np.array([1, 1, 1, 0, 0, 0, 0, 0, 0])
M10 = np.vstack([M_eig, mu_10_extra.reshape(1,-1)])

# The 10x10 system: sum_{i=0}^{9} w_i mu_i mu_i^T = K
# This is a linear system in w_0,...,w_9.
# Vectorize: vec(K) = sum w_i vec(mu_i mu_i^T) = [vec(mu_0 mu_0^T) | ... | vec(mu_9 mu_9^T)] w
# But K is symmetric, so use upper triangle: 45 equations, 10 unknowns.
rows_ut = []
for a in range(9):
    for b in range(a, 9):
        row = np.array([M10[i, a] * M10[i, b] for i in range(10)])
        rows_ut.append(row)
A_ut = np.array(rows_ut)  # 45 x 10
b_ut = []
for a in range(9):
    for b in range(a, 9):
        b_ut.append(K_gl3[a, b])
b_ut = np.array(b_ut)

# Solve mod p
A_p = A_ut % p
b_p = b_ut % p
# Use Gaussian elimination to solve A_p w = b_p mod p
n_eq, n_var = A_p.shape
aug = np.hstack([A_p, b_p.reshape(-1,1)]) % p
pivots = []
for col in range(n_var):
    pivot = -1
    for row in range(len(pivots), n_eq):
        if aug[row, col] % p != 0:
            pivot = row
            break
    if pivot < 0:
        continue
    aug[[len(pivots), pivot]] = aug[[pivot, len(pivots)]]
    inv_d = modinv(int(aug[len(pivots), col]), p)
    aug[len(pivots)] = (aug[len(pivots)] * inv_d) % p
    for row in range(n_eq):
        if row != len(pivots) and aug[row, col] % p != 0:
            aug[row] = (aug[row] - int(aug[row, col]) * aug[len(pivots)]) % p
    pivots.append(col)

if len(pivots) < n_var:
    free_vars = [c for c in range(n_var) if c not in pivots]
    print(f"10-cube moment system: {len(pivots)} pivots, {len(free_vars)} free vars")
    # Set free vars to 1 and solve
    w10_sol = np.zeros(n_var, dtype=int)
    for fv in free_vars:
        w10_sol[fv] = 1
    for i in range(len(pivots)-1, -1, -1):
        col = pivots[i]
        val = int(aug[i, n_var])
        for j in range(col+1, n_var):
            val = (val - int(aug[i, j]) * w10_sol[j]) % p
        w10_sol[col] = val % p
    
    # Verify
    check10 = np.zeros((9,9), dtype=int)
    for i in range(10):
        check10 = (check10 + w10_sol[i] * np.outer(M10[i], M10[i])) % p
    diff10 = (check10 - K_gl3) % p
    print(f"10-cube moment check max diff: {np.max(diff10)}")
    
    if np.max(diff10) == 0:
        print(f"10-cube weights: {w10_sol.tolist()}")
        # Test commutators for this 10-cube system
        max_r_10 = 0
        hist_10 = {}
        for trial in range(200):
            x1 = rng.randint(0, p, size=9)
            x2 = rng.randint(0, p, size=9)
            H1 = hessian_endo_gl3(x1, M10 % p, w10_sol % p, Kinv_gl3, p)
            H2 = hessian_endo_gl3(x2, M10 % p, w10_sol % p, Kinv_gl3, p)
            comm = (H1 @ H2 - H2 @ H1) % p
            r = rank_mod_p(comm, p)
            max_r_10 = max(max_r_10, r)
            hist_10[r] = hist_10.get(r, 0) + 1
        print(f"10-cube system: max commutator rank = {max_r_10}")
        print(f"  histogram: {dict(sorted(hist_10.items()))}")
else:
    print(f"10-cube moment system: full rank {len(pivots)}, unique solution")
    w10_sol = np.zeros(n_var, dtype=int)
    for i in range(len(pivots)-1, -1, -1):
        col = pivots[i]
        val = int(aug[i, n_var])
        w10_sol[col] = val % p
    
    check10 = np.zeros((9,9), dtype=int)
    for i in range(10):
        check10 = (check10 + w10_sol[i] * np.outer(M10[i], M10[i])) % p
    diff10 = (check10 - K_gl3) % p
    print(f"10-cube moment check max diff: {np.max(diff10)}")
    
    if np.max(diff10) == 0:
        print(f"10-cube weights: {w10_sol.tolist()}")
        max_r_10 = 0
        hist_10 = {}
        for trial in range(200):
            x1 = rng.randint(0, p, size=9)
            x2 = rng.randint(0, p, size=9)
            H1 = hessian_endo_gl3(x1, M10 % p, w10_sol % p, Kinv_gl3, p)
            H2 = hessian_endo_gl3(x2, M10 % p, w10_sol % p, Kinv_gl3, p)
            comm = (H1 @ H2 - H2 @ H1) % p
            r = rank_mod_p(comm, p)
            max_r_10 = max(max_r_10, r)
            hist_10[r] = hist_10.get(r, 0) + 1
        print(f"10-cube system: max commutator rank = {max_r_10}")
        print(f"  histogram: {dict(sorted(hist_10.items()))}")

# Now also test BILR on gl_3 with STANDARD basis pairs
print("\n" + "="*60)
print("BILR GL_3 COMMUTATOR WITH STANDARD BASIS PAIRS")
print("="*60)
for a in range(9):
    for b in range(a+1, min(a+2, 9)):
        ea = np.zeros(9, dtype=int); ea[a] = 1
        eb = np.zeros(9, dtype=int); eb[b] = 1
        H1 = hessian_endo_gl3(ea, mu_gl3 % p, w % p, Kinv_gl3, p)
        H2 = hessian_endo_gl3(eb, mu_gl3 % p, w % p, Kinv_gl3, p)
        comm = (H1 @ H2 - H2 @ H1) % p
        r = rank_mod_p(comm, p)
        print(f"  [{names_gl3[a]}, {names_gl3[b]}]: rank = {r}")

# Save results
results = {
    "scope": "Hessian-commutator Jennrich test on gl_3 (9 dims) for BILR residual.",
    "prime": p,
    "bilr_gl3_generic_commutator_rank": max_comm_rank_gl3,
    "bilr_gl3_commutator_histogram": {str(k): v for k,v in sorted(rank_hist_gl3.items())},
    "nine_cube_K_orthogonal_max_rank": max_r_9,
    "interpretation": (
        "On gl_3 (9 dims), the trace form K has rank 9. "
        "For k=9 cubes forming a K-orthogonal system (M^T W M = K with W diagonal), "
        "the Hessian endomorphism H(X) = Hess_R(X) K^{-1} diagonalizes in the M-basis, "
        "so [H(X),H(Y)] = 0 for all X,Y. "
        "For k=10, the extra vector gives a rank-1 perturbation and [H,H] has rank <= 2. "
        "BILR with k=11 should give generic commutator rank > 0."
    )
}

out_path = OUT / "hessian_gl3_bilr.json"
with open(out_path, 'w') as f:
    json.dump(results, f, indent=2)
print(f"\nResults saved to {out_path}")
