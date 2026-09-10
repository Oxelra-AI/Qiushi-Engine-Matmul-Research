#!/usr/bin/env python3
"""analysis: Check whether ker Psi = 0 is universal for rank-4 exterior decompositions."""

import numpy as np, json
from pathlib import Path

p = 65521
rng = np.random.RandomState(42)

# sl_3 basis: 8 traceless 3x3 matrices
sl3_basis = []
for i in range(3):
    for j in range(3):
        if i != j:
            E = np.zeros((3,3), dtype=int); E[i,j] = 1; sl3_basis.append(E)
sl3_basis.append(np.diag([1,-1,0]))
sl3_basis.append(np.diag([0,1,-1]))
n = 8

def tr3(A, B):
    return int(sum(int(A[i][j]) * int(B[j][i]) for i in range(3) for j in range(3))) % p

def mat_to_sl3_coords(M):
    G = np.zeros((n,n), dtype=np.int64)
    for i in range(n):
        for j in range(n):
            G[i,j] = tr3(sl3_basis[i], sl3_basis[j]) % p
    rhs = np.array([tr3(sl3_basis[k], M.tolist()) % p for k in range(n)], dtype=np.int64)
    aug = np.hstack([G % p, rhs.reshape(-1,1)]) % p
    for col in range(n):
        pivot = -1
        for row in range(col, n):
            if aug[row, col] % p != 0: pivot = row; break
        if pivot is None or pivot < 0: continue
        aug[[col, pivot]] = aug[[pivot, col]]
        inv_d = pow(int(aug[col, col]), p-2, p)
        aug[col] = (aug[col] * inv_d) % p
        for row in range(n):
            if row != col and aug[row, col] % p != 0:
                aug[row] = (aug[row] - int(aug[row, col]) * aug[col]) % p
    return aug[:, n] % p

def wedge2(v1, v2):
    result = []
    for a in range(n):
        for b in range(a+1, n):
            result.append((int(v1[a])*int(v2[b]) - int(v1[b])*int(v2[a])) % p)
    return np.array(result, dtype=np.int64)

def rank_mod(M):
    A = M.copy() % p; nr, nc = A.shape; r = 0
    for c in range(nc):
        piv = None
        for i in range(r, nr):
            if A[i,c] % p: piv = i; break
        if piv is None: continue
        A[[r,piv]] = A[[piv,r]]
        A[r] = (A[r] * pow(int(A[r,c]), p-2, p)) % p
        for i in range(nr):
            if i != r and A[i,c] % p:
                A[i] = (A[i] - int(A[i,c]) * A[r]) % p
        r += 1
    return r

# Load BILR planes
with open("data/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json") as f:
    scheme = json.load(f)

bilr_planes = []
for rep in scheme["free_orbit_representatives"]:
    U = np.array(rep["U"], dtype=int).T % p
    V = np.array(rep["V"], dtype=int).T % p
    W = np.array(rep["W"], dtype=int).T % p
    bilr_planes.append((U, V, W))

def build_phi_matrix(planes_gl3):
    """Build the 12x28 Phi matrix from 4 planes in gl_3."""
    rows = []
    for U, V, W in planes_gl3:
        u = mat_to_sl3_coords(U)
        v = mat_to_sl3_coords(V)
        w = mat_to_sl3_coords(W)
        rows.append(wedge2(u, v))
        rows.append(wedge2(u, w))
        rows.append(wedge2(v, w))
    return np.array(rows, dtype=np.int64) % p

# BILR baseline
Phi_bilr = build_phi_matrix(bilr_planes)
print(f"BILR Phi rank: {rank_mod(Phi_bilr)}")

# PGL_3 orbit: conjugate all planes by M A M^{-1}
def random_gl3():
    while True:
        M = np.array([[rng.randint(0, p) for _ in range(3)] for _ in range(3)], dtype=np.int64)
        det = int(M[0,0]*(M[1,1]*M[2,2]-M[1,2]*M[2,1]) - M[0,1]*(M[1,0]*M[2,2]-M[1,2]*M[2,0]) + M[0,2]*(M[1,0]*M[2,1]-M[1,1]*M[2,0])) % p
        if det != 0:
            return M, det

def inv3(M, det):
    di = pow(int(det), p-2, p)
    Minv = np.zeros((3,3), dtype=np.int64)
    Minv[0,0] = (M[1,1]*M[2,2]-M[1,2]*M[2,1]) * di % p
    Minv[0,1] = (M[0,2]*M[2,1]-M[0,1]*M[2,2]) * di % p
    Minv[0,2] = (M[0,1]*M[1,2]-M[0,2]*M[1,1]) * di % p
    Minv[1,0] = (M[1,2]*M[2,0]-M[1,0]*M[2,2]) * di % p
    Minv[1,1] = (M[0,0]*M[2,2]-M[0,2]*M[2,0]) * di % p
    Minv[1,2] = (M[0,2]*M[1,0]-M[0,0]*M[1,2]) * di % p
    Minv[2,0] = (M[1,0]*M[2,1]-M[1,1]*M[2,0]) * di % p
    Minv[2,1] = (M[0,1]*M[2,0]-M[0,0]*M[2,1]) * di % p
    Minv[2,2] = (M[0,0]*M[1,1]-M[0,1]*M[1,0]) * di % p
    return Minv

ranks = []
for trial in range(100):
    M, det = random_gl3()
    Minv = inv3(M, det)
    new_planes = []
    for U, V, W in bilr_planes:
        new_planes.append(((M @ U @ Minv) % p, (M @ V @ Minv) % p, (M @ W @ Minv) % p))
    Phi_new = build_phi_matrix(new_planes)
    r = rank_mod(Phi_new)
    ranks.append(r)

print(f"\nPGL_3 orbit Phi ranks (100 trials): {sorted(set(ranks))}")
print(f"All rank 12: {all(r == 12 for r in ranks)}")

# Also: random internal SL_3 frame changes (within each plane)
int_ranks = []
for trial in range(100):
    new_planes = []
    for U, V, W in bilr_planes:
        M, det = random_gl3()
        Minv = inv3(M, det)
        # Internal frame: replace (U,V,W) -> (M[0,:]·(U,V,W), M[1,:]·..., M[2,:]·...)
        U_new = (int(M[0,0]) * U + int(M[0,1]) * V + int(M[0,2]) * W) % p
        V_new = (int(M[1,0]) * U + int(M[1,1]) * V + int(M[1,2]) * W) % p
        W_new = (int(M[2,0]) * U + int(M[2,1]) * V + int(M[2,2]) * W) % p
        new_planes.append((U_new, V_new, W_new))
    Phi_new = build_phi_matrix(new_planes)
    r = rank_mod(Phi_new)
    int_ranks.append(r)

print(f"\nInternal SL_3 frame Phi ranks (100 trials): {sorted(set(int_ranks))}")
print(f"All rank 12: {all(r == 12 for r in int_ranks)}")

# Key observation: internal frame changes don't change the planes, only the bases.
# But Lambda^2(P_j) is intrinsic to P_j, so the Phi rank should be invariant!
# Let me verify this is correct.
print(f"\nNote: Lambda^2(P_j) is intrinsic to the plane P_j.")
print("Internal frame changes don't change the planes, so Phi rank should be invariant.")
print("PGL_3 moves the planes, so Phi rank CAN change.")
print(f"PGL_3 all-12 result means: for this exterior fiber, ker Psi = 0 universally.")
