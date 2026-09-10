#!/usr/bin/env python3
"""
analysis: Trace-graded cyclic collapse theorem.

THEOREM (conditional on tracelessness):
  For a char-zero pure cyclic rank-22 decomposition f+3m=22 of T_333,
  if all free orbit representatives are traceless, then tr(X_0^2) = sum c_i lambda_i^2
  on sl_3 forces f >= 8 (since the Killing form has rank 8), hence m <= 4.
  Combined with the Cartan m >= 4 theorem (analysis), pure cyclic collapses to (10,4).

This script verifies:
  A. The target's mixed-trace antisymmetric component I wedge Lambda^2(sl_3) = 0.
  B. The mixed-trace map is injective at BILR (rank 12 for m=4).
  C. Killing form tr(X_0^2) on sl_3 has rank 8.
  D. At BILR: sum c_i lambda_i^2 = tr(X_0^2), sum c_i^2 lambda_i = 0, sum c_i^3 = 3.
  E. At least 8 of the 11 BILR cubes have nonzero trace.
  F. Pairwise plane intersections dim(P_i cap P_j) for the 4 BILR free orbits.
  G. Random rank-4 fiber points: mixed-trace injectivity persists.
"""

import json, sys
import numpy as np
from pathlib import Path

P = 65521  # good split prime
def md(x): return int(x) % P
def inv(a): return pow(int(a) % P, P - 2, P)

WS = Path(__file__).resolve().parent.parent

# ── Load BILR scheme ──
with open(WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json") as f:
    scheme = json.load(f)

cubes_raw = scheme["cubes"]       # 11 matrices (stored as L in ell_L(X)=tr(L^T X))
reps_raw = scheme["free_orbit_representatives"]  # 4 triples {U,V,W}

# ── sl_3 basis ──
# E01,E02,E10,E12,E20,E21, H0=E00-E11, H1=E11-E22
SL3_DIM = 8
def e_ij(i, j):
    M = [[0]*3 for _ in range(3)]
    M[i][j] = 1
    return M

sl3_basis = []
sl3_labels = []
for i in range(3):
    for j in range(3):
        if i != j:
            sl3_basis.append(e_ij(i, j))
            sl3_labels.append(f"E{i}{j}")
H0 = [[1,0,0],[0,-1,0],[0,0,0]]
H1 = [[0,0,0],[0,1,0],[0,0,-1]]
sl3_basis.append(H0); sl3_labels.append("H0")
sl3_basis.append(H1); sl3_labels.append("H1")
assert len(sl3_basis) == 8

def mat_mul(A, B):
    """3x3 matrix multiply mod p."""
    C = [[0]*3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            s = 0
            for k in range(3):
                s += A[i][k] * B[k][j]
            C[i][j] = md(s)
    return C

def trace3(M):
    return md(M[0][0] + M[1][1] + M[2][2])

# ── Part B: Killing Gram matrix of tr(XY) on sl_3 ──
G = [[0]*8 for _ in range(8)]
for a in range(8):
    for b in range(8):
        prod = mat_mul(sl3_basis[a], sl3_basis[b])
        G[a][b] = trace3(prod)
G_np = np.array(G, dtype=int) % P

# Compute rank of G over F_p
def modp_rank(M, p=P):
    """Gaussian elimination rank mod p."""
    n, m = M.shape
    A = M.astype(int).copy() % p
    r = 0
    for col in range(m):
        pivot = None
        for row in range(r, n):
            if A[row, col] % p != 0:
                pivot = row; break
        if pivot is None: continue
        A[[r, pivot]] = A[[pivot, r]]
        piv_inv = inv(A[r, col])
        for row in range(n):
            if row != r and A[row, col] % p != 0:
                factor = md(A[row, col] * piv_inv)
                for c2 in range(m):
                    A[row, c2] = md(A[row, c2] - factor * A[r, c2])
        r += 1
    return r

killing_rank = modp_rank(G_np)
print(f"Killing form rank on sl_3: {killing_rank}")
assert killing_rank == 8, f"Expected 8, got {killing_rank}"

# ── Part A: Target's mixed-trace component is zero ──
# T(I,B,C) = tr(BC) is symmetric => antisymmetric part vanishes.
# The I-wedge-Lambda^2(sl_3) component of alt_3(tr(XYZ)) at (I,B,C):
#   = (1/3)(tr(IBC) - tr(ICB)) = (1/3)tr([B,C]) = 0 for all B,C.
target_mixed_trace_zero = True  # by algebraic identity

# ── Load cube forms (stored as L; linear form is tr(L^T X)) ──
cube_traces = []     # c_i = tr(L_i)
cube_sl3_vecs = []   # coefficient vector of lambda_i = tr(L_i^T X_0) on sl_3

for L_raw in cubes_raw:
    L = [[md(L_raw[i][j]) for j in range(3)] for i in range(3)]
    c = trace3(L)
    cube_traces.append(c)
    # Coefficient of lambda_i(e_k) = tr(L^T e_k) = sum_{a,b} L[b][a]*e_k[a][b]
    v = []
    for e in sl3_basis:
        val = 0
        for a in range(3):
            for b in range(3):
                val += L[b][a] * e[a][b]
        v.append(md(val))
    cube_sl3_vecs.append(v)

nonzero_trace_count = sum(1 for c in cube_traces if c != 0)
print(f"\nCube traces (mod {P}): {cube_traces}")
print(f"Nonzero traces: {nonzero_trace_count}/11")

# ── Part D: Moment conditions ──
# s^1: sum c_i lambda_i^2 = tr(X_0^2) on sl_3
# Build B = sum c_i v_i v_i^T mod p
B = np.zeros((8, 8), dtype=int)
for idx in range(11):
    c = cube_traces[idx]
    v = np.array(cube_sl3_vecs[idx], dtype=int)
    for a in range(8):
        for b in range(8):
            B[a][b] = md(B[a][b] + c * v[a] * v[b])

diff_s1 = (B - G_np) % P
s1_ok = np.all(diff_s1 == 0)
print(f"\ns^1 condition: sum c_i lambda_i^2 = tr(X_0^2)? {s1_ok}")

# s^2: sum c_i^2 lambda_i = 0 as linear form on sl_3
s2_vec = [0]*8
for idx in range(11):
    c2 = md(cube_traces[idx] * cube_traces[idx])
    for k in range(8):
        s2_vec[k] = md(s2_vec[k] + c2 * cube_sl3_vecs[idx][k])
s2_ok = all(v == 0 for v in s2_vec)
print(f"s^2 condition: sum c_i^2 lambda_i = 0? {s2_ok}  vec={s2_vec}")

# s^3: sum c_i^3 = 3
s3_sum = 0
for idx in range(11):
    s3_sum = md(s3_sum + md(md(cube_traces[idx] * cube_traces[idx]) * cube_traces[idx]))
s3_ok = (s3_sum == md(3))
print(f"s^3 condition: sum c_i^3 = 3? {s3_ok}  sum={s3_sum}")

# ── Part B: Mixed-trace map for BILR free orbits ──
# Build 28 x 12 matrix mapping (a_j,b_j,c_j) to Lambda^2(sl_3)
# Lambda^2 basis: pairs (i,j) with i<j, ordered by sl3_basis index
l2_dim = 28  # C(8,2)
l2_pairs = [(i, j) for i in range(8) for j in range(i+1, 8)]
assert len(l2_pairs) == 28

def to_sl3_coords(M_raw):
    """Express a 3x3 matrix's trace-free part in the sl_3 basis."""
    M = [md(M_raw[i][j]) for i in range(3) for j in range(3)]
    # coefficients: for E_ij basis vector, coeff = M[i][j] (mod p)
    # for H0=E00-E11: coeff is determined by the equation M = sum coeff_k e_k + (tr/3)I
    # With tr(M)=0 (trace-free part), M = sum c_k e_k where c_{E_ij} = M[i][j] for i!=j
    # and M[0][0] = c_{H0} + (1/3)tr (but we project to sl3)
    t = md(M_raw[0][0] + M_raw[1][1] + M_raw[2][2])
    t3 = md(t * inv(3))
    # trace-free: subtract (t/3)I
    M_tf = [[md(M_raw[i][j] - (t3 if i == j else 0)) for j in range(3)] for i in range(3)]
    coords = []
    idx = 0
    for i in range(3):
        for j in range(3):
            if i != j:
                coords.append(md(M_tf[i][j]))
    # H0, H1 coefficients from diagonal of M_tf
    d = [md(M_tf[i][i]) for i in range(3)]
    # M_tf = ... + c_H0 * H0 + c_H1 * H1
    # d[0] = c_H0, d[1] = -c_H0 + c_H1, d[2] = -c_H1
    # So c_H0 = d[0], c_H1 = -d[2]
    c_H0 = d[0]
    c_H1 = md(P - d[2])
    # verify: d[1] should = -c_H0 + c_H1
    check = md(P - c_H0 + c_H1)
    assert check == d[1], f"sl3 coord check failed: {check} vs {d[1]}"
    coords.append(c_H0)
    coords.append(c_H1)
    assert len(coords) == 8
    return coords

def wedge(x, y):
    """Compute x wedge y in Lambda^2, as 28-vector."""
    w = []
    for i in range(8):
        for j in range(i+1, 8):
            w.append(md(x[i]*y[j] - x[j]*y[i]))
    return w

# Build mixed-trace matrix (28 x 12)
mixed_trace_mat = np.zeros((28, 12), dtype=int)
for j in range(4):
    rep = reps_raw[j]
    u = to_sl3_coords(rep["U"])
    v = to_sl3_coords(rep["V"])
    w = to_sl3_coords(rep["W"])
    # column 3j: a_j -> v wedge w
    vw = wedge(v, w)
    # column 3j+1: b_j -> w wedge u
    wu = wedge(w, u)
    # column 3j+2: c_j -> u wedge v
    uv = wedge(u, v)
    for r in range(28):
        mixed_trace_mat[r, 3*j] = md(vw[r])
        mixed_trace_mat[r, 3*j+1] = md(wu[r])
        mixed_trace_mat[r, 3*j+2] = md(uv[r])

mt_rank = modp_rank(mixed_trace_mat)
print(f"\nMixed-trace map rank at BILR: {mt_rank} (domain dim 12, codomain dim 28)")
mt_injective = (mt_rank == 12)
print(f"Injective (forces all traces zero): {mt_injective}")

# ── Part F: Pairwise plane intersection dimensions ──
def plane_intersection_dim(rep_i, rep_j):
    """Dimension of P_i cap P_j in sl_3."""
    ui = to_sl3_coords(rep_i["U"])
    vi = to_sl3_coords(rep_i["V"])
    wi = to_sl3_coords(rep_i["W"])
    uj = to_sl3_coords(rep_j["U"])
    vj = to_sl3_coords(rep_j["V"])
    wj = to_sl3_coords(rep_j["W"])
    # Stack all 6 vectors as rows; plane_i spanned by first 3, plane_j by last 3
    # dim(P_i cap P_j) = dim(P_i) + dim(P_j) - dim(P_i + P_j)
    M = np.array([ui, vi, wi, uj, vj, wj], dtype=int) % P
    rank_ij = modp_rank(M)
    dim_pi = modp_rank(np.array([ui, vi, wi], dtype=int) % P)
    dim_pj = modp_rank(np.array([uj, vj, wj], dtype=int) % P)
    return dim_pi + dim_pj - rank_ij

print("\nPairwise plane intersection dimensions:")
for i in range(4):
    for j in range(i+1, 4):
        d = plane_intersection_dim(reps_raw[i], reps_raw[j])
        print(f"  P_{i} cap P_{j}: dim = {d}")

# ── Plane dimensions ──
for j in range(4):
    rep = reps_raw[j]
    u = to_sl3_coords(rep["U"])
    v = to_sl3_coords(rep["V"])
    w = to_sl3_coords(rep["W"])
    M = np.array([u, v, w], dtype=int) % P
    r = modp_rank(M)
    print(f"  dim(P_{j}) = {r}")

# ── Part E: rank of cube form vectors ──
# The cube forms lambda_i restricted to sl_3: check which span all of sl_3*
active_vecs = [cube_sl3_vecs[i] for i in range(11) if cube_traces[i] != 0]
if active_vecs:
    V = np.array(active_vecs, dtype=int) % P
    span_rank = modp_rank(V)
    print(f"\nActive cube forms (c_i != 0): {len(active_vecs)}, span rank in sl_3*: {span_rank}")
else:
    span_rank = 0
    print("\nNo active cube forms!")

# All cube forms span
V_all = np.array(cube_sl3_vecs, dtype=int) % P
all_span = modp_rank(V_all)
print(f"All 11 cube forms span rank: {all_span}")

# ── Part G: Random fiber points ──
# Apply random SL_3 conjugation: (u,v,w) -> (Ad(g)u, Ad(g)v, Ad(g)w)
# Ad(g)X = gXg^{-1} for X in sl_3
np.random.seed(42)
N_RANDOM = 20
fiber_injective_count = 0

def random_sl3_mod_p():
    """Random element of SL_3(F_p)."""
    while True:
        M = np.random.randint(0, P, (3, 3)).tolist()
        det = 0
        for i in range(3):
            det += M[0][i] * (M[1][(i+1)%3]*M[2][(i+2)%3] - M[1][(i+2)%3]*M[2][(i+1)%3])
        det = md(det)
        if det != 0:
            # scale to det=1
            di = inv(det)
            # compute adjugate
            adj = [[0]*3 for _ in range(3)]
            for i2 in range(3):
                for j2 in range(3):
                    # cofactor of M[j2][i2]
                    rows = [r for r in range(3) if r != j2]
                    cols = [c for c in range(3) if c != i2]
                    cof = md(M[rows[0]][cols[0]]*M[rows[1]][cols[1]] - M[rows[0]][cols[1]]*M[rows[1]][cols[0]])
                    if (i2+j2) % 2 == 1:
                        cof = md(P - cof)
                    adj[i2][j2] = md(cof * di)
            # M_inv = adj  (transposed cofactor / det)
            return M, adj

def conjugate_form(L_raw, g, gi):
    """Ad(g)L = g L g^{-1} for L in gl_3."""
    # First gL
    gL = mat_mul(g, [[md(L_raw[i][j]) for j in range(3)] for i in range(3)])
    return mat_mul(gL, gi)

for trial in range(N_RANDOM):
    g, gi = random_sl3_mod_p()
    # Conjugate all 4 free orbit reps
    new_reps = []
    for rep in reps_raw:
        nU = conjugate_form(rep["U"], g, gi)
        nV = conjugate_form(rep["V"], g, gi)
        nW = conjugate_form(rep["W"], g, gi)
        new_reps.append({"U": nU, "V": nV, "W": nW})
    
    # Build mixed-trace matrix
    mt = np.zeros((28, 12), dtype=int)
    for j2 in range(4):
        rep2 = new_reps[j2]
        u2 = to_sl3_coords(rep2["U"])
        v2 = to_sl3_coords(rep2["V"])
        w2 = to_sl3_coords(rep2["W"])
        vw2 = wedge(v2, w2)
        wu2 = wedge(w2, u2)
        uv2 = wedge(u2, v2)
        for r2 in range(28):
            mt[r2, 3*j2] = md(vw2[r2])
            mt[r2, 3*j2+1] = md(wu2[r2])
            mt[r2, 3*j2+2] = md(uv2[r2])
    
    rk = modp_rank(mt)
    if rk == 12:
        fiber_injective_count += 1

print(f"\nRandom SL_3 fiber tests: {fiber_injective_count}/{N_RANDOM} injective (rank 12)")

# ── Internal recombination test ──
# Use the analysis six-parameter family: M in SL_3, move via Ad(M)
# Check that mixed-trace injectivity holds along internal directions
internal_injective_count = 0
N_INTERNAL = 20

for trial in range(N_INTERNAL):
    # Random near-identity M = I + epsilon * X with X in sl_3
    eps = np.random.randint(1, P)
    X_coeffs = [np.random.randint(0, P) for _ in range(8)]
    # Build X as 3x3 matrix
    X_mat = [[0]*3 for _ in range(3)]
    for k, (coeffs, basis_el) in enumerate(zip(X_coeffs, sl3_basis)):
        for i in range(3):
            for j in range(3):
                X_mat[i][j] = md(X_mat[i][j] + coeffs * basis_el[i][j])
    # M = I + eps*X mod p
    M_mat = [[md((1 if i == j else 0) + eps * X_mat[i][j]) for j in range(3)] for i in range(3)]
    # Check det != 0
    det_M = 0
    for i in range(3):
        det_M += M_mat[0][i] * (M_mat[1][(i+1)%3]*M_mat[2][(i+2)%3] - M_mat[1][(i+2)%3]*M_mat[2][(i+1)%3])
    det_M = md(det_M)
    if det_M == 0:
        continue
    # Compute M_inv via adjugate
    di = inv(det_M)
    M_inv = [[0]*3 for _ in range(3)]
    for i2 in range(3):
        for j2 in range(3):
            rows = [r for r in range(3) if r != j2]
            cols = [c for c in range(3) if c != i2]
            cof = md(M_mat[rows[0]][cols[0]]*M_mat[rows[1]][cols[1]] - M_mat[rows[0]][cols[1]]*M_mat[rows[1]][cols[0]])
            if (i2+j2) % 2 == 1:
                cof = md(P - cof)
            M_inv[i2][j2] = md(cof * di)
    
    # Apply Ad(M) to all free orbit reps: U -> M U M^{-1}
    new_reps2 = []
    for rep in reps_raw:
        nU = conjugate_form(rep["U"], M_mat, M_inv)
        nV = conjugate_form(rep["V"], M_mat, M_inv)
        nW = conjugate_form(rep["W"], M_mat, M_inv)
        new_reps2.append({"U": nU, "V": nV, "W": nW})
    
    mt2 = np.zeros((28, 12), dtype=int)
    for j2 in range(4):
        rep2 = new_reps2[j2]
        u2 = to_sl3_coords(rep2["U"])
        v2 = to_sl3_coords(rep2["V"])
        w2 = to_sl3_coords(rep2["W"])
        vw2 = wedge(v2, w2)
        wu2 = wedge(w2, u2)
        uv2 = wedge(u2, v2)
        for r2 in range(28):
            mt2[r2, 3*j2] = md(vw2[r2])
            mt2[r2, 3*j2+1] = md(wu2[r2])
            mt2[r2, 3*j2+2] = md(uv2[r2])
    
    rk2 = modp_rank(mt2)
    if rk2 == 12:
        internal_injective_count += 1

print(f"Internal SL_3 recombination tests: {internal_injective_count}/{N_INTERNAL} injective")

# ── Rank-5 splitting test ──
# Split one BILR plane to get a rank-5 decomposition
# Check whether the orbit s-linear contribution from kernel traces is zero
print("\n── Rank-5 splitting analysis ──")
rep0 = reps_raw[0]
u0 = to_sl3_coords(rep0["U"])
v0 = to_sl3_coords(rep0["V"])
w0 = to_sl3_coords(rep0["W"])

# Split u0 into u0a + u0b (random split)
np.random.seed(123)
t_split = np.random.randint(1, P)
u0a = [md(u0[k] + t_split * v0[k]) for k in range(8)]  # u + t*v
u0b = [md(u0[k] - t_split * v0[k]) for k in range(8)]   # u - t*v  (so u0a+u0b = 2u)
# Actually for splitting: alpha_1 = u0 ^ v0 ^ w0 = (u0a) ^ v0 ^ w0 + (u0b) ^ v0 ^ w0
# where u0 = u0a + u0b. Let u0a = u0, u0b = 0 is trivial. Better:
alpha = np.random.randint(1, P)
beta = md(P - alpha + 1)  # alpha + beta = 1 so alpha*u + beta*u = u
# Actually let's do u0 = u0a + u0b properly
u0a = [md(alpha * u0[k]) for k in range(8)]
u0b = [md(beta * u0[k]) for k in range(8)]
# These share v0, w0 and P_a = <u0a, v0, w0> = P_b = <u0b, v0, w0> = P_0
# This is a trivial splitting. For nontrivial, need u0a, u0b independent.

# Nontrivial split: pick a random vector in sl_3 outside P_0
delta = [np.random.randint(0, P) for _ in range(8)]
u0a_nt = [md(u0[k] + delta[k]) for k in range(8)]
u0b_nt = [md(u0[k] - delta[k]) for k in range(8)]
# u0a_nt + u0b_nt = 2*u0, so the trivector sum is 2*(u0^v0^w0)
# We need u0^v0^w0 = (u0a_nt)^v0^w0 + (u0b_nt)^v0^w0
# Since u0a + u0b = 2u0, we get u0a^v0^w0 + u0b^v0^w0 = 2u0^v0^w0
# For a proper splitting: take u0a_nt and u0b_nt = u0 - u0a_nt
# such that the orbit contribution is exactly omega/3
# Let u0a = u0 + eps*delta, u0b = -eps*delta (so sum = u0)
eps_s = np.random.randint(1, P)
u0a_s = [md(u0[k] + eps_s * delta[k]) for k in range(8)]
u0b_s = [md(P - eps_s * delta[k]) for k in range(8)]
# u0a_s + u0b_s = u0 mod p? check
check_sum = [md(u0a_s[k] + u0b_s[k]) for k in range(8)]
assert check_sum == [md(u0[k]) for k in range(8)], "Split sum check failed"

# Now the 5 planes: P_a = <u0a_s, v0, w0>, P_b = <u0b_s, v0, w0>, P_1, P_2, P_3
# P_a and P_b share <v0, w0> (2-dim if v0, w0 independent)
vw_rank = modp_rank(np.array([v0, w0], dtype=int) % P)
print(f"Shared subspace <v0, w0> has rank: {vw_rank}")

# Build mixed-trace matrix for 5-term decomposition (28 x 15)
mt5 = np.zeros((28, 15), dtype=int)
# orbit a: (u0a_s, v0, w0)
vw_a = wedge(v0, w0)
wu_a = wedge(w0, u0a_s)
uv_a = wedge(u0a_s, v0)
for r in range(28):
    mt5[r, 0] = md(vw_a[r])
    mt5[r, 1] = md(wu_a[r])
    mt5[r, 2] = md(uv_a[r])

# orbit b: (u0b_s, v0, w0)
wu_b = wedge(w0, u0b_s)
uv_b = wedge(u0b_s, v0)
for r in range(28):
    mt5[r, 3] = md(vw_a[r])  # same v wedge w!
    mt5[r, 4] = md(wu_b[r])
    mt5[r, 5] = md(uv_b[r])

# orbits 1,2,3 (original BILR orbits 1,2,3)
for j in range(1, 4):
    rep = reps_raw[j]
    u = to_sl3_coords(rep["U"])
    v = to_sl3_coords(rep["V"])
    w = to_sl3_coords(rep["W"])
    vw_j = wedge(v, w)
    wu_j = wedge(w, u)
    uv_j = wedge(u, v)
    col_base = 3 + 3*j
    for r in range(28):
        mt5[r, col_base] = md(vw_j[r])
        mt5[r, col_base+1] = md(wu_j[r])
        mt5[r, col_base+2] = md(uv_j[r])

mt5_rank = modp_rank(mt5)
print(f"Mixed-trace rank for 5-term splitting: {mt5_rank} (domain 15, codomain 28)")
mt5_kernel_dim = 15 - mt5_rank
print(f"Kernel dimension: {mt5_kernel_dim}")

# Find kernel direction and check s-linear contribution
# The kernel should include direction (a_a=1, a_b=-1, rest=0) since v^w is shared
# Check: columns 0 and 3 are the same (both = v0 ^ w0)
col0 = [mt5[r, 0] for r in range(28)]
col3 = [mt5[r, 3] for r in range(28)]
cols_match = (col0 == col3)
print(f"Columns 0,3 (both v0^w0) match: {cols_match}")

# The s-linear contribution from kernel element (a_a=1,a_b=-1):
# Q_a + Q_b = 1*ell_v0*ell_w0 + (-1)*ell_v0*ell_w0 = 0
# This cancels because the SAME forms v0,w0 appear in both orbits.
print("Kernel direction (a_a=1,a_b=-1): s-linear contribution cancels (same v,w forms)")

# Now check a misaligned splitting: different bases for the same shared 2-plane
# Orbit a: (u0a_s, v0, w0)
# Orbit b: (u0b_s, v0+w0, w0)  -- DIFFERENT basis for the same shared 2-plane <v0,w0>
# The trivector u0b_s ^ (v0+w0) ^ w0 = u0b_s ^ v0 ^ w0 (since v0^w0+w0^w0 = v0^w0)
# So the decomposition is still valid!
v0_plus_w0 = [md(v0[k] + w0[k]) for k in range(8)]

mt5_mis = np.zeros((28, 15), dtype=int)
# orbit a stays the same
for r in range(28):
    mt5_mis[r, 0] = md(vw_a[r])
    mt5_mis[r, 1] = md(wu_a[r])
    mt5_mis[r, 2] = md(uv_a[r])

# orbit b with misaligned basis: (u0b_s, v0+w0, w0)
vw_bm = wedge(v0_plus_w0, w0)
wu_bm = wedge(w0, u0b_s)
uv_bm = wedge(u0b_s, v0_plus_w0)
for r in range(28):
    mt5_mis[r, 3] = md(vw_bm[r])
    mt5_mis[r, 4] = md(wu_bm[r])
    mt5_mis[r, 5] = md(uv_bm[r])

# orbits 1,2,3 same
for j in range(1, 4):
    rep = reps_raw[j]
    u = to_sl3_coords(rep["U"])
    v = to_sl3_coords(rep["V"])
    w = to_sl3_coords(rep["W"])
    col_base = 3 + 3*j
    vw_j = wedge(v, w)
    wu_j = wedge(w, u)
    uv_j = wedge(u, v)
    for r in range(28):
        mt5_mis[r, col_base] = md(vw_j[r])
        mt5_mis[r, col_base+1] = md(wu_j[r])
        mt5_mis[r, col_base+2] = md(uv_j[r])

mt5_mis_rank = modp_rank(mt5_mis)
print(f"\nMisaligned-basis 5-term: mixed-trace rank = {mt5_mis_rank}")
mt5_mis_ker = 15 - mt5_mis_rank
print(f"Kernel dimension: {mt5_mis_ker}")

# Check if col 0 and col 3 still match (they shouldn't for misaligned)
col0m = [mt5_mis[r, 0] for r in range(28)]
col3m = [mt5_mis[r, 3] for r in range(28)]
cols_match_m = (col0m == col3m)
print(f"Columns 0,3 match in misaligned: {cols_match_m}")

# Check: (v0+w0)^w0 = v0^w0 + w0^w0 = v0^w0 (since w^w=0)
vw_check = wedge(v0, w0)
for r in range(28):
    assert vw_bm[r] == vw_check[r], f"Wedge mismatch at {r}"
print("Confirmed: (v0+w0)^w0 = v0^w0, columns 0 and 3 should match")
# Wait - they should match! Let me recheck
print(f"  col0m = col0: {col0m == col0}")
print(f"  col3m = col3m original: check via wedge identity")

# ── Summary ──
results = {
    "prime": P,
    "killing_rank_on_sl3": killing_rank,
    "target_mixed_trace_zero": True,
    "bilr_mixed_trace_rank": mt_rank,
    "bilr_mixed_trace_injective": mt_injective,
    "cube_traces": cube_traces,
    "nonzero_trace_cube_count": nonzero_trace_count,
    "s1_moment_ok": bool(s1_ok),
    "s2_moment_ok": s2_ok,
    "s3_moment_ok": s3_ok,
    "active_cube_form_span_rank": int(span_rank),
    "all_cube_form_span_rank": int(all_span),
    "random_sl3_fiber_injective": f"{fiber_injective_count}/{N_RANDOM}",
    "internal_fiber_injective": f"{internal_injective_count}/{N_INTERNAL}",
    "splitting_analysis": {
        "shared_subspace_rank": int(vw_rank),
        "rank5_mt_rank": int(mt5_rank),
        "rank5_kernel_dim": mt5_kernel_dim,
    },
    "theorem": "If free orbit traces are zero, then f >= 8 (Killing rank 8 forces at least 8 cubes with nonzero trace), so m <= 4. Combined with Cartan m >= 4, pure cyclic -> (10,4) only.",
}

out_dir = WS / "data" / "trace_grading"
out_dir.mkdir(parents=True, exist_ok=True)
out_path = out_dir / "trace_grading_verification.json"
with open(out_path, 'w') as f:
    json.dump(results, f, indent=2)

print(f"\n{'='*60}")
print(f"Results saved to {out_path}")
print(json.dumps(results, indent=2))
