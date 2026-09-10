#!/usr/bin/env python3
"""
analysis: Eigen-coordinate block decomposition of the Z4-invariant residual cubic.

Ad(a₀) on gl₃ has eigenvalues +1(×3), -1(×2), i(×2), -i(×2).
Z₄-invariant cubics in gl₃* decompose into five character blocks:
  p³ (10 dims), pq² (9), pzw (12), qz² (6), qw² (6)  → total 43
  H_W = p³+pq² = 19,  off_W = pzw+qz²+qw² = 24

Key property: size-4 cube orbits contribute to all blocks;
size-2 orbits contribute only to H_W; fixed cubes only to p³.

The qz² block of the residual is a 2×3 matrix in V_{-1}⊗Sym²(V_i).
For two size-4 orbits, rank-2 of this matrix gives a pencil of binary
quadrics whose intersection with the Veronese conic determines the
z-components of the two orbits.

Validated against the BILR rank-23 scheme as positive control.
"""
from __future__ import annotations
import itertools, json, sys
from pathlib import Path
import numpy as np

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "eigenblock"
OUT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(WS / "scripts"))

# ──────────────────────────────────────────────
# 1. Setup: a₀, Ad(a₀), primes, basic utilities
# ──────────────────────────────────────────────
a0 = np.array([[0,0,-1],[1,0,-1],[0,1,-1]], dtype=object)

def mat_inv_mod_3(M, p):
    """3×3 matrix inverse mod p using cofactors."""
    m = np.array(M, dtype=object) % p
    det = int((m[0,0]*(m[1,1]*m[2,2]-m[1,2]*m[2,1])
              -m[0,1]*(m[1,0]*m[2,2]-m[1,2]*m[2,0])
              +m[0,2]*(m[1,0]*m[2,1]-m[1,1]*m[2,0])) % p)
    assert det % p != 0, f"singular mod {p}"
    dinv = pow(det, -1, p)
    cof = np.zeros((3,3), dtype=object)
    for i in range(3):
        for j in range(3):
            rows = [r for r in range(3) if r!=i]
            cols = [c for c in range(3) if c!=j]
            minor = (m[rows[0],cols[0]]*m[rows[1],cols[1]]
                    -m[rows[0],cols[1]]*m[rows[1],cols[0]])
            cof[i,j] = ((-1)**(i+j) * minor * dinv) % p
    return cof.T % p

def mat_inv_mod(M, p):
    """General n×n matrix inverse mod p via Gauss-Jordan."""
    n = M.shape[0]
    if n == 3:
        return mat_inv_mod_3(M, p)
    # Augment [M | I]
    aug = [[int(M[i,j]) % p for j in range(n)] + [1 if i==j else 0 for j in range(n)]
           for i in range(n)]
    for col in range(n):
        piv = None
        for i in range(col, n):
            if aug[i][col] % p:
                piv = i; break
        assert piv is not None, f"singular mod {p}"
        aug[col], aug[piv] = aug[piv], aug[col]
        inv = pow(aug[col][col] % p, -1, p)
        aug[col] = [(x * inv) % p for x in aug[col]]
        for i in range(n):
            if i != col and aug[i][col] % p:
                f = aug[i][col] % p
                aug[i] = [(aug[i][j] - f * aug[col][j]) % p for j in range(2*n)]
    result = np.zeros((n, n), dtype=object)
    for i in range(n):
        for j in range(n):
            result[i,j] = aug[i][n+j] % p
    return result

def matmul_mod(A, B, p):
    n1, n2 = A.shape[0], B.shape[1]
    k = A.shape[1]
    C = np.zeros((n1, n2), dtype=object)
    for i in range(n1):
        for j in range(n2):
            s = 0
            for l in range(k):
                s += int(A[i,l]) * int(B[l,j])
            C[i,j] = s % p
    return C

def ad_matrix(g, p):
    """Build 9×9 matrix of X → gXg⁻¹ mod p, row i = vec(g·E_i·g⁻¹)."""
    gi = mat_inv_mod(g, p)
    G = np.array(g, dtype=object) % p
    Gi = np.array(gi, dtype=object) % p
    M = np.zeros((9, 9), dtype=object)
    for k in range(9):
        E = np.zeros((3,3), dtype=object)
        E[k//3, k%3] = 1
        # gEg^{-1}
        tmp = matmul_mod(G, E, p)
        res = matmul_mod(tmp, Gi, p)
        for l in range(9):
            M[l, k] = res[l//3, l%3] % p
    return M

def eigenspaces_mod(M, p, eigenval):
    """Kernel of (M - eigenval*I) mod p."""
    n = M.shape[0]
    A = np.zeros((n, n), dtype=object)
    for i in range(n):
        for j in range(n):
            A[i,j] = (int(M[i,j]) - (eigenval if i==j else 0)) % p
    return kernel_mod(A, p)

def kernel_mod(A, p):
    """Return kernel basis vectors (columns) of A mod p."""
    m, n = A.shape
    B = [[int(A[i,j]) % p for j in range(n)] for i in range(m)]
    pivots = []
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if B[i][c] % p:
                piv = i; break
        if piv is None: continue
        B[r], B[piv] = B[piv], B[r]
        inv = pow(B[r][c] % p, -1, p)
        B[r] = [(x * inv) % p for x in B[r]]
        for i in range(m):
            if i != r and B[i][c] % p:
                f = B[i][c] % p
                B[i] = [(B[i][j] - f * B[r][j]) % p for j in range(n)]
        pivots.append(c)
        r += 1
    free = [c for c in range(n) if c not in pivots]
    vecs = []
    for fc in free:
        v = [0]*n
        v[fc] = 1
        for idx, pc in enumerate(pivots):
            v[pc] = (-B[idx][fc]) % p
        vecs.append(v)
    return np.array(vecs, dtype=object).T if vecs else np.zeros((n,0), dtype=object)

def rank_mod(A, p):
    m, n = A.shape
    B = [[int(A[i,j]) % p for j in range(n)] for i in range(m)]
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if B[i][c] % p:
                piv = i; break
        if piv is None: continue
        B[r], B[piv] = B[piv], B[r]
        inv = pow(B[r][c] % p, -1, p)
        B[r] = [(x*inv) % p for x in B[r]]
        for i in range(m):
            if i != r and B[i][c] % p:
                f = B[i][c] % p
                B[i] = [(B[i][j] - f*B[r][j]) % p for j in range(n)]
        r += 1
    return r

# ──────────────────────────────────────────────
# 2. Find a prime where i = sqrt(-1) exists
# ──────────────────────────────────────────────
def find_sqrt_minus1(p):
    """Find i such that i²≡-1 mod p. p must be ≡1 mod 4."""
    assert p % 4 == 1
    for a in range(2, p):
        c = pow(a, (p-1)//4, p)
        if (c*c) % p == (p-1):
            return c
    return None

P = 65521  # ≡ 1 mod 4
imag_unit = find_sqrt_minus1(P)
print(f"Prime p = {P}, i = {imag_unit}, i² mod p = {(imag_unit*imag_unit)%P}")

# ──────────────────────────────────────────────
# 3. Eigenspaces of Ad(a₀) mod p
# ──────────────────────────────────────────────
Ad = ad_matrix(a0, P)
print(f"\nAd(a₀) eigenvalue verification:")

evals = {
    '+1': 1,
    '-1': P-1,
    'i': imag_unit,
    '-i': (P-imag_unit) % P
}

eigspaces = {}
for name, val in evals.items():
    K = eigenspaces_mod(Ad, P, val)
    eigspaces[name] = K
    print(f"  V_{name}: dim {K.shape[1]}")

assert eigspaces['+1'].shape[1] == 3, "V_+1 should be 3-dim"
assert eigspaces['-1'].shape[1] == 2, "V_-1 should be 2-dim"
assert eigspaces['i'].shape[1] == 2, "V_i should be 2-dim"
assert eigspaces['-i'].shape[1] == 2, "V_-i should be 2-dim"

# Quick check: eigenspaces span gl₃
full = np.hstack([eigspaces[k] for k in ['+1','-1','i','-i']])
assert rank_mod(full, P) == 9, "eigenspaces should span gl₃"
print(f"  Eigenspaces span dimension: {rank_mod(full, P)}")

# Basis: p = V_{+1} cols, q = V_{-1} cols, z = V_i cols, w = V_{-i} cols
basis_p = eigspaces['+1']  # 9×3
basis_q = eigspaces['-1']  # 9×2
basis_z = eigspaces['i']   # 9×2
basis_w = eigspaces['-i']  # 9×2

# Change-of-basis matrix: new_basis columns in old coordinates
change = np.hstack([basis_p, basis_q, basis_z, basis_w])  # 9×9
change_inv = mat_inv_mod(change, P)

# ──────────────────────────────────────────────
# 4. Build the five character blocks
# ──────────────────────────────────────────────
# Index ranges in new basis: p=0..2, q=3..4, z=5..6, w=7..8
# A monomial x_a*x_b*x_c with a,b,c in {p,q,z,w} group coords
# has character (-1)^(#q) * i^(#z) * (-i)^(#w)
# Invariant iff character = 1

# Sym³ monomials in 9 vars (new basis)
MONOS9 = list(itertools.combinations_with_replacement(range(9), 3))

def var_type(idx):
    if idx < 3: return 'p'
    elif idx < 5: return 'q'
    elif idx < 7: return 'z'
    else: return 'w'

def block_label(mono):
    """Classify a monomial by its character block.
    Z₄ action on coordinates uses INVERSE eigenvalues: p→1, q→-1, z→-i, w→i.
    Character of monomial = (-1)^(nq+nz) · i^(nz+nw).
    Invariant iff character = 1."""
    counts = {'p':0, 'q':0, 'z':0, 'w':0}
    for i in mono:
        counts[var_type(i)] += 1
    nq, nz, nw = counts['q'], counts['z'], counts['w']
    # Character = (-1)^(nq+nz) * i^(nz+nw)
    # = 1 iff (nq+nz even and nz+nw ≡ 0 mod 4)
    #      or (nq+nz odd  and nz+nw ≡ 2 mod 4)
    is_inv = False
    if (nq + nz) % 2 == 0 and (nz + nw) % 4 == 0:
        is_inv = True
    if (nq + nz) % 2 == 1 and (nz + nw) % 4 == 2:
        is_inv = True
    if not is_inv:
        return None
    np_ = counts['p']
    if np_==3 and nq==0 and nz==0 and nw==0: return 'p3'
    if np_==1 and nq==2 and nz==0 and nw==0: return 'pq2'
    if np_==1 and nq==0 and nz==1 and nw==1: return 'pzw'
    if np_==0 and nq==1 and nz==2 and nw==0: return 'qz2'
    if np_==0 and nq==1 and nz==0 and nw==2: return 'qw2'
    return None

block_indices = {'p3':[], 'pq2':[], 'pzw':[], 'qz2':[], 'qw2':[]}
for idx, mono in enumerate(MONOS9):
    bl = block_label(mono)
    if bl is not None:
        block_indices[bl].append(idx)

for bl in ['p3','pq2','pzw','qz2','qw2']:
    print(f"  Block {bl}: {len(block_indices[bl])} monomials")

total_inv = sum(len(v) for v in block_indices.values())
print(f"  Total invariant: {total_inv} (expected 43)")
assert total_inv == 43, f"Expected 43 invariant monomials, got {total_inv}"

# ──────────────────────────────────────────────
# 5. Compute BILR residual in eigen-coordinates
# ──────────────────────────────────────────────
# Load BILR scheme
sch = json.loads((WS / "data" / "ballard_z4_cyclic" /
                  "ballard_z4_cyclic_scheme.json").read_text())

# Build T333 as a cubic polynomial in 9 variables (entry coords of X)
# T333 = tr(X^3) in our convention = sum_{a,b,c} T_{abc} x_a x_b x_c
# where T_{abc} = delta_{(a//3, b%3)} * delta_{(b//3, c%3)} * delta_{(c//3, a%3)} ... no
# T333(X) = tr(X³) where X is 3×3, entries x_0...x_8 (row-major)
def tr_X3_coeffs():
    """Coefficient vector of tr(X³) in Sym³(K⁹) monomial basis."""
    # tr(X³) = sum_{i,j,k} X_{ij} X_{jk} X_{ki}
    coeffs = [0] * len(MONOS9)
    mono_to_idx = {m:i for i,m in enumerate(MONOS9)}
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a, b, c = 3*i+j, 3*j+k, 3*k+i
                mono = tuple(sorted([a,b,c]))
                coeffs[mono_to_idx[mono]] += 1
    return np.array(coeffs, dtype=object)

# Cube linear forms from BILR
cubes_flat = []
for cube in sch["cubes"]:
    flat = [cube[i][j] for i in range(3) for j in range(3)]
    cubes_flat.append(flat)

free_reps = []
for rep in sch["free_orbit_representatives"]:
    U = [rep["U"][i][j] for i in range(3) for j in range(3)]
    V = [rep["V"][i][j] for i in range(3) for j in range(3)]
    W = [rep["W"][i][j] for i in range(3) for j in range(3)]
    free_reps.append((U, V, W))

# Residual cubic = tr(X³) - sum of 23 cube terms
# The 11 cubes contribute l³ each; the 4 free orbits each contribute
# l³ + (gl)³ + (g²l)³ + (g³l)³ with l being the _bilinear_ product u⊗v

# Actually, the BILR scheme decomposes T_{333} = sum terms u⊗v⊗w
# The residual cubic is tr(X³) - sum_{11 cubes} l_i³ where l_i = u_i = v_i = w_i

# Compute tr(X³) coefficients in the NEW basis
# If X = sum_i x_i e_i (old basis), new coords y = change_inv @ x
# so x = change @ y. tr(X³) in y-coords:
# We need the change-of-basis for cubic monomials

def cubic_coeffs_in_newbasis(old_coeffs, change_mat, p):
    """Transform Sym³ coefficients from old basis to new basis.
    If old poly = sum c_m * prod x_{m_i}, and x = T*y,
    then new poly = sum c_m * prod (sum T_{m_i,j} y_j) which we expand."""
    T = np.array(change_mat, dtype=object) % p
    n = T.shape[0]
    new_coeffs = [0] * len(MONOS9)
    mono_to_idx = {m:i for i,m in enumerate(MONOS9)}
    for idx, mono in enumerate(MONOS9):
        c = int(old_coeffs[idx]) % p
        if c == 0: continue
        a, b, cc = mono
        # x_a * x_b * x_c = (sum T[a,j]y_j)(sum T[b,k]y_k)(sum T[c,l]y_l)
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    val = (c * int(T[a,j]) * int(T[b,k]) * int(T[cc,l])) % p
                    if val == 0: continue
                    new_mono = tuple(sorted([j,k,l]))
                    new_coeffs[mono_to_idx[new_mono]] = (
                        new_coeffs[mono_to_idx[new_mono]] + val) % p
    return np.array(new_coeffs, dtype=object)

def cube_coeffs(lin_form, p):
    """Sym³ coefficient vector of l³ where l is given in old basis."""
    n = len(lin_form)
    mono_to_idx = {m:i for i,m in enumerate(MONOS9)}
    coeffs = [0] * len(MONOS9)
    for a in range(n):
        for b in range(a, n):
            for c in range(b, n):
                mono = (a, b, c)
                val = int(lin_form[a]) * int(lin_form[b]) * int(lin_form[c])
                # Count multiplicity
                if a == b == c:
                    mult = 1
                elif a == b or b == c:
                    mult = 3
                else:
                    mult = 6
                coeffs[mono_to_idx[mono]] = (coeffs[mono_to_idx[mono]] + val) % p
    return np.array(coeffs, dtype=object)

# Form transformation: l_new = change^T @ l_old (NOT change_inv!).
# x_old = change @ y_new, so l(x) = l^T (change y) = (change^T l)^T y.
change_T = change.T % P  # 9×9, for transforming linear forms

def form_to_newbasis(lin_form_old, p):
    """Transform a linear form from old coords to eigenbasis coords."""
    l_old = np.array(lin_form_old, dtype=object) % p
    l_new = np.zeros(9, dtype=object)
    for i in range(9):
        s = 0
        for j in range(9):
            s += int(change_T[i,j]) * int(l_old[j])
        l_new[i] = s % p
    return l_new

def cube_coeffs_newbasis(lin_form_old, p):
    """l³ in new basis, where l is given in old coordinates."""
    l_new = form_to_newbasis(lin_form_old, p)
    return cube_coeffs(l_new, p)

print("\n" + "="*60)
print("Computing BILR residual in eigen-coordinates")
print("="*60)

# tr(X³) in old basis
trX3_old = tr_X3_coeffs()
# Transform to new basis
trX3_new = cubic_coeffs_in_newbasis(trX3_old, change, P)

# Check: should be Z₄-invariant (only nonzero in invariant blocks)
noninv_nonzero = 0
for idx, mono in enumerate(MONOS9):
    bl = block_label(mono)
    if bl is None and int(trX3_new[idx]) % P != 0:
        noninv_nonzero += 1
print(f"tr(X³) non-invariant nonzero monomials: {noninv_nonzero}")
assert noninv_nonzero == 0, "tr(X³) should be Z₄-invariant"

# Compute cube contributions in new basis
Ad_g = Ad  # Ad(a₀) mod P
def apply_ad_to_form(l_old, p):
    """Ad(a₀)* on linear form: (g*l)(X) = l(g⁻¹Xg), 
    which means the form vector transforms as l -> (Ad(a₀)^T)⁻¹ l = Ad(a₀⁻¹)^T l."""
    # Actually for column action on vectors in gl₃:
    # if X = sum x_i E_i, then g*l should give l(g⁻¹Xg) = (Ad(g⁻¹)^T l)(x)
    # But Ad acts on gl₃ as X->gXg⁻¹, so on the dual l->l∘Ad(g)⁻¹ = Ad(g)^{-T} l
    # For eigenspaces of Ad(g), the dual eigenspaces have the same eigenvalues
    # since Ad(g)^{-T} has eigenvalues that are inverses of Ad(g)^T which are 
    # the same as Ad(g). Actually Ad(g) is not symmetric in general.
    # 
    # Simpler: in our new basis, Ad(a₀) is diagonal with eigenvalues 1,-1,i,-i.
    # On the dual, Ad(a₀)* has eigenvalues 1,-1,-i,i (inverse of transpose).
    # Wait, that's wrong too. Let me just compute directly.
    # l is a linear form on gl₃. The Z₄ action on cubics sends
    # f(X) -> f(Ad(g)^{-1} X) = f(g⁻¹Xg). So on linear forms:
    # (g·l)(X) = l(g⁻¹Xg) = sum_j l_j (Ad(g⁻¹)X)_j
    # = sum_j l_j sum_k Ad(g⁻¹)_{jk} x_k
    # = sum_k (sum_j Ad(g⁻¹)_{jk} l_j) x_k
    # So g·l = Ad(g⁻¹)^T l as a column vector
    pass

# Precompute Ad(a₀⁻¹) = Ad(a₀³) = Ad(a₀)³ mod P
Ad2 = matmul_mod(Ad, Ad, P)
Ad3 = matmul_mod(Ad2, Ad, P)
Ad_inv = Ad3  # a₀⁴ = I, so a₀⁻¹ = a₀³

# g·l = Ad(g⁻¹)^T · l = Ad3^T · l (action on dual/linear forms)
AdT_inv = Ad_inv.T % P

# The BILR scheme: 23 terms = 11 cubes (each l⊗l⊗l) + 4 free Z₃-orbit reps × 3.
# The 4 free reps are already the Z₄ images of the first.
# Evaluation: tr(X³) = sum_{11 cubes} l_i(x)³ + sum_{4 reps} 3·u_j(x)v_j(x)w_j(x)
# Residual = tr(X³) - trilinear = sum_{11 cubes} l_i(x)³

print("\nComputing BILR residual = sum of 11 individual cube l³...")
residual_new = np.zeros(len(MONOS9), dtype=object)
for cf in cubes_flat:
    residual_new = (residual_new + cube_coeffs_newbasis(cf, P)) % P

# Verify: tr(X³) = residual + trilinear
trilinear_total = np.zeros(len(MONOS9), dtype=object)
mono_to_idx = {m:i for i,m in enumerate(MONOS9)}

for j, (U, V, W) in enumerate(free_reps):
    # Each rep contributes 3·u(x)v(x)w(x), NO extra Z₄ rotation
    u_new = form_to_newbasis(U, P)
    v_new = form_to_newbasis(V, P)
    w_new = form_to_newbasis(W, P)
    for a in range(9):
        for b in range(9):
            for c in range(9):
                val = (3 * int(u_new[a]) * int(v_new[b]) * int(w_new[c])) % P
                if val == 0: continue
                mono = tuple(sorted([a,b,c]))
                trilinear_total[mono_to_idx[mono]] = (
                    trilinear_total[mono_to_idx[mono]] + val) % P

check = (trX3_new - trilinear_total - residual_new) % P
check_nonzero = sum(1 for c in check if int(c) % P != 0)
print(f"tr(X³) - trilinear - residual = {check_nonzero} nonzero entries (should be 0)")

# ──────────────────────────────────────────────
# 6. Extract the five blocks of the residual
# ──────────────────────────────────────────────
print("\n" + "="*60)
print("Block decomposition of BILR residual")
print("="*60)

block_coeffs = {}
for bl in ['p3','pq2','pzw','qz2','qw2']:
    vals = [(MONOS9[i], int(residual_new[i]) % P) for i in block_indices[bl]]
    nonzero = [(m, v) for m, v in vals if v != 0]
    block_coeffs[bl] = vals
    print(f"  {bl}: {len(vals)} monomials, {len(nonzero)} nonzero")

# ──────────────────────────────────────────────
# 7. Extract qz² block as 2×3 matrix
# ──────────────────────────────────────────────
# qz² block monomials: q_i * z_j * z_k where q∈{3,4}, z∈{5,6}
# In V_{-1} ⊗ Sym²(V_i): rows indexed by q_idx (0,1), cols by sym2_z (00,01,11)
# Monomial (3,5,5) -> q0*z0^2 : row 0, col 0
# Monomial (3,5,6) -> q0*z0*z1 : row 0, col 1
# Monomial (3,6,6) -> q0*z1^2 : row 0, col 2
# Monomial (4,5,5) -> q1*z0^2 : row 1, col 0
# Monomial (4,5,6) -> q1*z0*z1 : row 1, col 1
# Monomial (4,6,6) -> q1*z1^2 : row 1, col 2

qz2_mono_map = {
    (3,5,5): (0,0), (3,5,6): (0,1), (3,6,6): (0,2),
    (4,5,5): (1,0), (4,5,6): (1,1), (4,6,6): (1,2),
}

qz2_matrix = np.zeros((2,3), dtype=object)
for mono, (r, c) in qz2_mono_map.items():
    idx = mono_to_idx[mono]
    qz2_matrix[r, c] = int(residual_new[idx]) % P

print(f"\nqz² block as 2×3 matrix (V_{{-1}} ⊗ Sym²(V_i)):")
print(f"  [{qz2_matrix[0,0]:6d} {qz2_matrix[0,1]:6d} {qz2_matrix[0,2]:6d}]")
print(f"  [{qz2_matrix[1,0]:6d} {qz2_matrix[1,1]:6d} {qz2_matrix[1,2]:6d}]")
print(f"  rank mod {P}: {rank_mod(qz2_matrix, P)}")

# Similarly for qw² block
qw2_mono_map = {
    (3,7,7): (0,0), (3,7,8): (0,1), (3,8,8): (0,2),
    (4,7,7): (1,0), (4,7,8): (1,1), (4,8,8): (1,2),
}

qw2_matrix = np.zeros((2,3), dtype=object)
for mono, (r, c) in qw2_mono_map.items():
    idx = mono_to_idx[mono]
    qw2_matrix[r, c] = int(residual_new[idx]) % P

print(f"\nqw² block as 2×3 matrix (V_{{-1}} ⊗ Sym²(V_{{-i}})):")
print(f"  [{qw2_matrix[0,0]:6d} {qw2_matrix[0,1]:6d} {qw2_matrix[0,2]:6d}]")
print(f"  [{qw2_matrix[1,0]:6d} {qw2_matrix[1,1]:6d} {qw2_matrix[1,2]:6d}]")
print(f"  rank mod {P}: {rank_mod(qw2_matrix, P)}")

# ──────────────────────────────────────────────
# 8. Pencil-conic intersection for qz² block
# ──────────────────────────────────────────────
# The qz² block = sum over size-4 orbits of 3 * q_j ⊗ z_j²
# where q_j ∈ V_{-1} (2d), z_j ∈ V_i (2d), z_j² ∈ Sym²(V_i) (3d).
# For 2 size-4 orbits: qz² = 3(q₁⊗z₁² + q₂⊗z₂²) 
# This has rank 2 iff q₁,q₂ linearly independent AND z₁²,z₂² linearly independent.
# The row space is a pencil of binary quadrics in P(Sym²(V_i)) = P².
# The Veronese (conic of perfect squares) is {[a²:ab:b²]} in P².
# A generic pencil meets the conic in exactly 2 points (Bezout: deg 1 line ∩ deg 2 curve).

print(f"\n{'='*60}")
print("Pencil-conic intersection to recover size-4 orbit z-components")
print("="*60)

# Row space of qz² matrix (2×3 mod P) is the pencil.
# A point [s:t:u] in the row space satisfies [s,t,u] = α·row0 + β·row1
# for some [α:β] ∈ P¹.
# The point is on the Veronese iff s*u = t²/4 (i.e., the quadratic su-t²=0 
# in the coordinates of z₀² : z₀z₁ : z₁²).
# Wait: Sym²(V_i) with basis z₀², z₀z₁, z₁². A square of (az₀ + bz₁)
# is a²z₀² + 2ab z₀z₁ + b²z₁². But in the monomial basis, 
# (az₀+bz₁)³ restricted to the z² part... hmm.

# Actually the coefficient of the monomial z_0^2 in l³ (where l = ...+ γ₀z₀ + γ₁z₁ +...)
# is: look at the qz² contribution from one size-4 orbit form l.
# Proj_inv(l³) restricted to the qz² block:
# The relevant terms are those with exactly 1 q and 2 z.
# From l = p + q + z + w (components), l³ has cross terms 
# with character (-1)^1 · i^2 = (-1)(-1) = 1. ✓
# The qz² part of l³ = q·z² specifically (unsymmetrized):
# 3·q_coeff * z_coeff² (coefficient with multiplicity 3 from trinomial)
# Wait: for a monomial like q₀z₀z₁, the coefficient in l³ is:
# We need exactly 1 factor from q and 2 from z.
# From (q₀f₃ + q₁f₄)·(z₀f₅ + z₁f₆)² expanded:
# = (q₀f₃+q₁f₄)(z₀²f₅² + 2z₀z₁f₅f₆ + z₁²f₆²)
# But in a CUBIC l³, this cross-term has multiplicity 3 (choose which of 3 factors provides q)

# So the qz² block of Proj_inv(l³) = 4^{-1} sum_k (g^k l)³ restricted to qz²
# For a size-4 orbit, sum_k (g^k l)³ restricted to qz² = 4 × (qz² part of l³)
# because the character is 1 for the qz² block, so Proj_inv acts as identity.

# Actually: sum_k character^k = 4 for invariant block, 0 otherwise.
# The qz² monomial q_a z_b z_c has eigenvalue (+1) under the full Z₄ sum:
# sum_k (-1)^k · (i)^k · (i)^k = sum_k (-1)^k · (-1)^k = sum_k 1 = 4
# Wait: the character of q_a z_b z_c is (-1)^1 · i^2 · (-i)^0 = (-1)(-1) = 1 ✓
# So under Z₄ averaging, the qz² part is preserved with factor 4/4 = 1.

# The qz² part of l³ (with l having q-part q and z-part z):
# Multinomial: 3! / (1!·2!) · q · z² = 3 q·z²
# More precisely: coefficient of q_a z_b z_c in l³:
#   if b=c: 3·q_a·z_b² (from 3 ways to pick which l-factor provides q)
#   if b≠c: 6·q_a·z_b·z_c (from 3·2 ways)
# In our Sym³ convention with monomials z_b z_c counted once:
#   coefficient of sorted monomial (a,b,c) with a in q-range, b,c in z-range:
#   For (q_a, z_b, z_c) with b=c: multiplicity already handled in Sym³ → coeff = 3q_a z_b²
#   For (q_a, z_b, z_c) with b<c: multiplicity → coeff = 6 q_a z_b z_c
# But in our enumeration, the monomial (3,5,5) means q₀·z₀·z₀, 
# and its Sym³ multiplicity is 3 (choose which position gets the q).

# For the Veronese question: given the 2×3 matrix M where
# M[i,j] = coefficient of q_i · sym2_z_j
# and the orbit contribution is 3·(q_i · z²_j) per orbit,
# we need to find z such that z² (properly encoded) matches a row of M.

# The encoding: z = (z₀, z₁), then z² = (z₀², z₀z₁, z₁²)
# But in our monomial convention:
# (3,5,5) coeff = q₀·z₀² with mult 3 in l³
# (3,5,6) coeff = q₀·z₀·z₁ with mult 6 in l³ (b≠c)
# (3,6,6) coeff = q₀·z₁² with mult 3 in l³

# So the actual matrix entry for the qz² block is:
# M[0,0] = 3·q₀·z₀² (summed over size-4 orbits, times Proj_inv factor)
# M[0,1] = 6·q₀·z₀·z₁ (has double counting from symmetry)
# M[0,2] = 3·q₀·z₁²

# For 2 size-4 orbits with forms l₁, l₂:
# M[i,j] = sum_r 3·(q_r)_i · (z_r²)_j 
# where (z²)_0 = z₀², (z²)_1 = 2z₀z₁, (z²)_2 = z₁²
# Hmm, I need to be careful about the factor of 2 on the mixed term.

# Let me define φ: Sym²(V_i) -> K³ as:
# φ(z²) = [z₀², 2z₀z₁, z₁²] for z = z₀e₅ + z₁e₆
# Then the (a²:ab:b²) Veronese becomes the image of (a,b) -> (a², ab, b²)
# under the map that uses the HALF-integer basis for Sym².
# 
# Actually in the monomial basis with the multinomial coefficient:
# The qz² block of the orbit sum of l is:
#   (q₀, q₁) ⊗ (3z₀², 6z₀z₁, 3z₁²) = 3 · (q₀,q₁) ⊗ (z₀², 2z₀z₁, z₁²)
# 
# So the matrix is M = 3·sum_r qr ⊗ [zr₀², 2zr₀zr₁, zr₁²]
# The Veronese in the coordinates (s:t:u) where s=z₀², t=2z₀z₁, u=z₁²
# is: s·u = t²/4 → 4su = t²

# For the pencil-conic intersection:
# Points on the pencil: [s,t,u] = α·row0 + β·row1
# On the Veronese: 4su = t²
# This gives a quadratic in (α:β).

r0 = [int(qz2_matrix[0,j]) % P for j in range(3)]
r1 = [int(qz2_matrix[1,j]) % P for j in range(3)]

# Quadratic: 4(α·r0[0]+β·r1[0])(α·r0[2]+β·r1[2]) = (α·r0[1]+β·r1[1])²
# Expand: 4(r0[0]r0[2]α² + (r0[0]r1[2]+r1[0]r0[2])αβ + r1[0]r1[2]β²)
#        = r0[1]²α² + 2r0[1]r1[1]αβ + r1[1]²β²
# Quadratic in (α:β):
# (4r0[0]r0[2] - r0[1]²)α² + (4(r0[0]r1[2]+r1[0]r0[2]) - 2r0[1]r1[1])αβ 
#   + (4r1[0]r1[2] - r1[1]²)β² = 0

A_coeff = (4*r0[0]*r0[2] - r0[1]*r0[1]) % P
B_coeff = (4*(r0[0]*r1[2] + r1[0]*r0[2]) - 2*r0[1]*r1[1]) % P
C_coeff = (4*r1[0]*r1[2] - r1[1]*r1[1]) % P

disc = (B_coeff*B_coeff - 4*A_coeff*C_coeff) % P
print(f"\nPencil-conic quadratic: {A_coeff}α² + {B_coeff}αβ + {C_coeff}β² = 0")
print(f"Discriminant = {disc}")

# Find square root of discriminant mod P
def sqrt_mod(n, p):
    n = n % p
    if n == 0: return 0
    # Tonelli-Shanks
    if pow(n, (p-1)//2, p) != 1:
        return None  # not a QR
    Q, S = p-1, 0
    while Q % 2 == 0:
        Q //= 2; S += 1
    if S == 1:
        return pow(n, (p+1)//4, p)
    z = 2
    while pow(z, (p-1)//2, p) != p-1:
        z += 1
    M = S; c = pow(z, Q, p); t = pow(n, Q, p); R = pow(n, (Q+1)//2, p)
    while True:
        if t == 1: return R
        i = 1; tmp = (t*t) % p
        while tmp != 1:
            tmp = (tmp*tmp) % p; i += 1
        b = pow(c, pow(2, M-i-1, p-1), p)
        M = i; c = (b*b) % p; t = (t*c) % p; R = (R*b) % p

sq_disc = sqrt_mod(disc, P)
if sq_disc is not None:
    print(f"sqrt(disc) mod {P} = {sq_disc}")
    # Solutions: α/β = (-B ± sqrt(disc)) / (2A) 
    if A_coeff % P != 0:
        inv_2A = pow(2*A_coeff % P, -1, P)
        ab_ratio_1 = ((-B_coeff + sq_disc) * inv_2A) % P
        ab_ratio_2 = ((-B_coeff - sq_disc) * inv_2A) % P
        print(f"Solution 1: α/β = {ab_ratio_1}")
        print(f"Solution 2: α/β = {ab_ratio_2}")
        
        # For each solution, get z² vector and extract z
        for sol_idx, ratio in enumerate([ab_ratio_1, ab_ratio_2]):
            # α = ratio, β = 1
            s = (ratio * r0[0] + r1[0]) % P
            t = (ratio * r0[1] + r1[1]) % P
            u = (ratio * r0[2] + r1[2]) % P
            # Veronese check: 4su = t²
            check_val = (4*s*u - t*t) % P
            print(f"\n  Solution {sol_idx+1}: z² = [{s}, {t}, {u}]")
            print(f"  Veronese check 4su-t² = {check_val}")
            # Extract z = (z0, z1): z0² = s, 2z0z1 = t, z1² = u
            z0_sq = s
            z1_sq = u
            z0 = sqrt_mod(z0_sq, P)
            z1 = sqrt_mod(z1_sq, P)
            if z0 is not None and z1 is not None:
                # Check 2z0z1 = t
                for sg0 in [z0, P-z0]:
                    for sg1 in [z1, P-z1]:
                        if (2*sg0*sg1) % P == t:
                            print(f"  z = ({sg0}, {sg1}), check 2z0z1={t}: ✓")
                            break
else:
    print(f"Discriminant is NOT a QR mod {P} — solution requires quadratic extension")

# ──────────────────────────────────────────────
# 9. Verify by checking BILR cube forms in eigenbasis
# ──────────────────────────────────────────────
print(f"\n{'='*60}")
print("Validation: BILR cube forms in eigenbasis")
print("="*60)

# Classify each BILR cube by orbit type
for j, cf in enumerate(cubes_flat):
    l_old = np.array(cf, dtype=object) % P
    l_new = form_to_newbasis(cf, P)
    
    p_part = [int(l_new[i]) % P for i in range(3)]
    q_part = [int(l_new[i]) % P for i in range(3,5)]
    z_part = [int(l_new[i]) % P for i in range(5,7)]
    w_part = [int(l_new[i]) % P for i in range(7,9)]
    
    has_z = any(x != 0 for x in z_part)
    has_w = any(x != 0 for x in w_part)
    has_q = any(x != 0 for x in q_part)
    
    if has_z or has_w:
        orbit = 4
    elif has_q:
        orbit = 2
    else:
        orbit = 1
    
    # For size-4 orbits, print z and q parts
    if orbit >= 2:
        print(f"  Cube {j:2d}: orbit={orbit}, p={p_part}, q={q_part}, z={z_part}, w={w_part}")

# ──────────────────────────────────────────────
# 10. Save results
# ──────────────────────────────────────────────
results = {
    "prime": P,
    "imag_unit": int(imag_unit),
    "eigenspace_dims": {k: int(v.shape[1]) for k, v in eigspaces.items()},
    "block_dims": {k: len(v) for k, v in block_indices.items()},
    "total_invariant_dim": total_inv,
    "residual_non_invariant_nonzero": int(noninv_nonzero),
    "decomposition_check_nonzero": int(check_nonzero),
    "qz2_matrix": [[int(qz2_matrix[i,j]) for j in range(3)] for i in range(2)],
    "qz2_rank": int(rank_mod(qz2_matrix, P)),
    "qw2_matrix": [[int(qw2_matrix[i,j]) for j in range(3)] for i in range(2)],
    "qw2_rank": int(rank_mod(qw2_matrix, P)),
    "pencil_conic_quadratic": {
        "A": int(A_coeff), "B": int(B_coeff), "C": int(C_coeff),
        "discriminant": int(disc),
        "sqrt_disc": int(sq_disc) if sq_disc is not None else None,
    },
}
(OUT / "eigenblock_decomposition.json").write_text(json.dumps(results, indent=2) + '\n')
print(f"\nSaved {OUT / 'eigenblock_decomposition.json'}")
