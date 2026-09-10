#!/usr/bin/env python3
"""
analysis: Diagonal-basis block solve for the Z4-equivariant rank-22 problem.

Diagonalize a0 on K^3 over Z[i] (modulo large prime p = 1 mod 4).
Use the tr(LM) pairing in the diagonal basis so that the Z4 action
is simply diagonal multiplication with eigenvalues mu_b/mu_a on n_ab.

The five invariant cubic blocks of tr(X^3):
  p^3: n11^3 + n22^3 + n33^3
  pq^2: 3(n22+n33)*n23*n32
  pzw: 3(n11+n22)*n12*n21 + 3(n11+n33)*n13*n31
  qz^2: 3*n32*n21*n13
  qw^2: 3*n23*n12*n31

where p={n11,n22,n33}, q={n23,n32}, z={n21,n13}, w={n12,n31}.

For a size-4 cube orbit with representative l:
  qz^2 contribution = 12 * l_q (x) l_z^2  (Veronese of z-part)
  qw^2 contribution = 12 * l_q (x) l_w^2

The target qz^2 = [[0,0,0],[0,3,0]] is rank-1 with a hyperbolic
quadric z1*z2, NOT on the Veronese conic.  Two size-4 orbits must
manufacture this via a secant of the conic.
"""
import json, sys, os
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent  # workspace/
OUT = WS / "data" / "diagonal_block"
OUT.mkdir(parents=True, exist_ok=True)

# ── Prime and imaginary unit ──
P = 65521
# Find i such that i^2 = -1 mod P
def sqrt_neg1(p):
    for x in range(2, p):
        if pow(x, (p-1)//4, p) != 1 and pow(x, (p-1)//2, p) == p-1:
            r = pow(x, (p-1)//4, p)
            if (r*r) % p == p-1:
                return r
    return None

II = sqrt_neg1(P)
assert (II*II) % P == P-1, "i^2 != -1"
print(f"p={P}, i={II}, i^2 mod p = {(II*II)%P}")

def inv(a, p=P):
    return pow(a % p, p-2, p) % p

def neg(a, p=P):
    return (-a) % p

# ── a0 in original basis ──
a0 = [[0,0,-1],[1,0,-1],[0,1,-1]]

# Eigenvalues: mu1=-1, mu2=i, mu3=-i
mu = [P-1, II, neg(II)]  # [-1, i, -i] mod P
print(f"Eigenvalues: {[x if x < P//2 else x-P for x in mu]}")

# Eigenvectors: v1=(1,0,1), v2=(i,1+i,1), v3=(-i,1-i,1)
# Change-of-basis P_mat: columns are eigenvectors
P_mat = [
    [1, II, neg(II)],
    [0, (1+II)%P, (1+neg(II))%P],
    [1, 1, 1]
]

def mat_mul(A, B, p=P):
    n = len(A)
    m = len(B[0])
    k = len(B)
    C = [[0]*m for _ in range(n)]
    for i in range(n):
        for j in range(m):
            s = 0
            for l in range(k):
                s += A[i][l] * B[l][j]
            C[i][j] = s % p
    return C

def mat_inv3(M, p=P):
    """Invert 3x3 matrix mod p."""
    a,b,c = M[0]
    d,e,f = M[1]
    g,h,k_ = M[2]
    det = (a*(e*k_-f*h) - b*(d*k_-f*g) + c*(d*h-e*g)) % p
    di = inv(det, p)
    adj = [
        [(e*k_-f*h)%p, (c*h-b*k_)%p, (b*f-c*e)%p],
        [(f*g-d*k_)%p, (a*k_-c*g)%p, (c*d-a*f)%p],
        [(d*h-e*g)%p, (b*g-a*h)%p, (a*e-b*d)%p]
    ]
    return [[(adj[i][j]*di)%p for j in range(3)] for i in range(3)]

def mat_T(M):
    """Transpose."""
    n = len(M)
    return [[M[j][i] for j in range(n)] for i in range(n)]

# Verify P_mat diagonalizes a0
P_inv = mat_inv3(P_mat)
D_check = mat_mul(mat_mul(P_inv, a0), P_mat)
for i in range(3):
    assert D_check[i][i] % P == mu[i], f"Diag entry {i} wrong: {D_check[i][i]%P} != {mu[i]}"
    for j in range(3):
        if i != j:
            assert D_check[i][j] % P == 0, f"Off-diag ({i},{j}) nonzero: {D_check[i][j]%P}"
print("Diagonalization verified: P^{-1} a0 P = diag(-1,i,-i)")

# ── Variable classification ──
# n_{ab} = X_{ab} in diagonal basis, eigenvalue mu_b/mu_a
# p = {(0,0),(1,1),(2,2)} eig 1
# q = {(1,2),(2,1)} eig -1  [mu_2/mu_1=i/(-1)=-i? No...]
# Wait, let me recompute:
# n_{ab} eigenvalue = mu_b/mu_a
# (1,2): mu_2/mu_1 = i/(-1) = -i  -> w type!
# (2,1): mu_1/mu_2 = (-1)/i = i   -> z type!
# Hmm, let me use the labeling exactly.
# mu1=-1, mu2=i, mu3=-i
# n_{21}: mu_1/mu_2 = (-1)/i = (-1)(-i)/(i(-i)) = i/1 = i  -> z
# n_{13}: mu_3/mu_1 = (-i)/(-1) = i  -> z
# n_{12}: mu_2/mu_1 = i/(-1) = -i  -> w
# n_{31}: mu_1/mu_3 = (-1)/(-i) = -i  -> w
# n_{23}: mu_3/mu_2 = (-i)/i = -1  -> q
# n_{32}: mu_2/mu_3 = i/(-i) = -1  -> q

# Indices in the 9-vector [n00,n01,n02, n10,n11,n12, n20,n21,n22]
# = [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
# Mapping (a,b) to index: 3*a+b

# But let's use the (a,b) indexing directly.
# p-vars: (0,0),(1,1),(2,2)
# q-vars: (1,2),(2,1)  -- Wait, (1,2) has mu_2/mu_1 = i/(-1) = -i, not -1.

# Let me recompute carefully with mu = [-1, i, -i]
# mu_b/mu_a for all (a,b):
eig_table = {}
for a in range(3):
    for b in range(3):
        e = (mu[b] * inv(mu[a])) % P
        eig_table[(a,b)] = e

print("\nEigenvalue table (mu_b/mu_a):")
for a in range(3):
    row = []
    for b in range(3):
        e = eig_table[(a,b)]
        if e == 1: row.append("+1")
        elif e == P-1: row.append("-1")
        elif e == II: row.append("+i")
        elif e == (P-II)%P: row.append("-i")
        else: row.append(str(e))
    print(f"  a={a}: {row}")

# Classify
p_vars = [(a,b) for a in range(3) for b in range(3) if eig_table[(a,b)] == 1]
q_vars = [(a,b) for a in range(3) for b in range(3) if eig_table[(a,b)] == P-1]
z_vars = [(a,b) for a in range(3) for b in range(3) if eig_table[(a,b)] == II]
w_vars = [(a,b) for a in range(3) for b in range(3) if eig_table[(a,b)] == (P-II)%P]

print(f"\np-vars (eig +1): {p_vars}")
print(f"q-vars (eig -1): {q_vars}")
print(f"z-vars (eig +i): {z_vars}")
print(f"w-vars (eig -i): {w_vars}")
print(f"Counts: p={len(p_vars)}, q={len(q_vars)}, z={len(z_vars)}, w={len(w_vars)}")

# ── tr(X^3) blocks ──
# tr(X^3) = sum_{a,b,c} X_{ab}X_{bc}X_{ca}
# Each monomial n_{ab}*n_{bc}*n_{ca} has total eigenvalue
# (mu_b/mu_a)(mu_c/mu_b)(mu_a/mu_c) = 1, as expected.

# Verify the explicit block formulas by direct computation.
# Represent tr(X^3) as a dictionary {(sorted monomial indices): coefficient}
from collections import defaultdict

def mono_key(indices):
    """Canonical key for a symmetric monomial in 9 variables indexed by (a,b)."""
    return tuple(sorted(indices))

trX3_coeffs = defaultdict(int)
for a in range(3):
    for b in range(3):
        for c in range(3):
            key = mono_key([(a,b),(b,c),(c,a)])
            trX3_coeffs[key] += 1

# Classify each monomial into blocks
def var_type(ab):
    e = eig_table[ab]
    if e == 1: return 'p'
    if e == P-1: return 'q'
    if e == II: return 'z'
    if e == (P-II)%P: return 'w'
    return '?'

def mono_block(indices):
    types = sorted([var_type(v) for v in indices])
    return ''.join(types)

block_counts = defaultdict(int)
for key, coeff in trX3_coeffs.items():
    blk = mono_block(list(key))
    block_counts[blk] += coeff

print("\ntr(X^3) block structure (monomial-type: total coefficient sum):")
for blk in sorted(block_counts.keys()):
    print(f"  {blk}: {block_counts[blk]}")

# Verify the analytic formulas
# qz^2: 3*n_{32}*n_{21}*n_{13} -- but which indices?
# Wait, the review says qz^2 = 3*n32*n21*n13 where:
# n32 = X_{32} is a q-var (eig mu_2/mu_3 = i/(-i) = -1 ✓)
# n21 = X_{21} is a z-var (eig mu_1/mu_2 = (-1)/i = i ✓)
# n13 = X_{13} is a z-var (eig mu_3/mu_1 = (-i)/(-1) = i ✓)
# But wait, (2,1) means row=2, col=1 in 0-indexed, which is the (3,2) entry
# in 1-indexed notation!

# Actually, with 0-indexed: mu = [mu_0, mu_1, mu_2] = [-1, i, -i]
# (a,b) = (2,1): mu_1/mu_2 = i/(-i) = -1 -> q-var!
# That doesn't match. Let me recheck.

# With 0-indexed eigenvalues mu_0=-1, mu_1=i, mu_2=-i:
# n_{(2,1)}: eig = mu_1/mu_2 = i/(-i) = i*i/(i*(-i)) ... 
# mu_1 = i, mu_2 = -i.  mu_1/mu_2 = i/(-i).
# To compute i/(-i): i * (-i)^{-1} = i * (i) = i^2 = -1.
# So (2,1) has eigenvalue -1 -> q type!

# Hmm, this contradicts the z-var = {n21, n13}!
# The issue is indexing: the review uses 1-indexed eigenvalues
# mu_1=-1, mu_2=i, mu_3=-i. So n_{21} in their notation is the
# (2,1) entry with 1-indexing = (1,0) in 0-indexing.

# With 1-indexed: n_{ab} has eigenvalue mu_b/mu_a.
# n_{21}: mu_1/mu_2 = (-1)/i = i (z-type). ✓
# In 0-indexed, this is (a,b) = (1,0): mu_0/mu_1 = (-1)/i = i. ✓

# So I need to be careful: the notation is 1-indexed.
# In my 0-indexed code:
# z-vars: (1,0) [=n_{21} in 1-idx] and (0,2) [=n_{13} in 1-idx]
# w-vars: (0,1) [=n_{12}] and (2,0) [=n_{31}]
# q-vars: (1,2) [=n_{23}] and (2,1) [=n_{32}]

# Let me verify:
# (1,0): mu_0/mu_1 = (-1)/i = i -> z ✓
# (0,2): mu_2/mu_0 = (-i)/(-1) = i -> z ✓
# (0,1): mu_1/mu_0 = i/(-1) = -i -> w ✓
# (2,0): mu_0/mu_2 = (-1)/(-i) = -i -> w ✓
# (1,2): mu_2/mu_1 = (-i)/i = -1 -> q ✓
# (2,1): mu_1/mu_2 = i/(-i) = -1 -> q ✓

# OK so in 0-indexed code, the groups are:
# p: (0,0),(1,1),(2,2)
# q: (1,2),(2,1)  -- corresponding to n_{23},n_{32} in 1-idx
# z: (1,0),(0,2)  -- corresponding to n_{21},n_{13}
# w: (0,1),(2,0)  -- corresponding to n_{12},n_{31}

# This matches the eigenvalue table. Let me verify q:
assert var_type((1,2)) == 'q' and var_type((2,1)) == 'q'
assert var_type((1,0)) == 'z' and var_type((0,2)) == 'z'
assert var_type((0,1)) == 'w' and var_type((2,0)) == 'w'
print("\n0-indexed variable groups:")
print(f"  p: {[(a,b) for a,b in p_vars]}")
print(f"  q: {[(a,b) for a,b in q_vars]} (n23,n32 in 1-idx)")
print(f"  z: {[(a,b) for a,b in z_vars]} (n21,n13 in 1-idx)")
print(f"  w: {[(a,b) for a,b in w_vars]} (n12,n31 in 1-idx)")

# ── Verify tr(X^3) analytic block formulas ──
# In 0-indexed, the formulas become:
# qz^2: 3 * n_{(2,1)} * n_{(1,0)} * n_{(0,2)}  [= 3*q2*z1*z2]
# Check: (a,b,c) = (2,1,0) gives n_{21}*n_{10}*n_{02} ✓
# And cyclically (1,0,2) and (0,2,1) also give the same monomial.

qz2_key = mono_key([(2,1),(1,0),(0,2)])
qz2_coeff = trX3_coeffs[qz2_key]
print(f"\nqz^2 monomial n_{{21}}*n_{{10}}*n_{{02}}: coefficient = {qz2_coeff}")

# qw^2: 3 * n_{(1,2)} * n_{(0,1)} * n_{(2,0)}  [= 3*q1*w1*w2]
qw2_key = mono_key([(1,2),(0,1),(2,0)])
qw2_coeff = trX3_coeffs[qw2_key]
print(f"qw^2 monomial n_{{12}}*n_{{01}}*n_{{20}}: coefficient = {qw2_coeff}")

# Verify that qz^2 and qw^2 blocks have ONLY these terms
qz2_monomials = {k:v for k,v in trX3_coeffs.items() if mono_block(list(k)) == 'qzz'}
qw2_monomials = {k:v for k,v in trX3_coeffs.items() if mono_block(list(k)) == 'qww'}
print(f"All qzz monomials: {dict(qz2_monomials)}")
print(f"All qww monomials: {dict(qw2_monomials)}")

# qz^2 as 2x3 matrix: rows = q-vars [(1,2),(2,1)], cols = Sym^2(z-vars)
# z-vars in order: z1=(1,0), z2=(0,2)
# Sym^2 basis: z1^2, z1*z2, z2^2
q_order = [(1,2), (2,1)]  # q1, q2
z_order = [(1,0), (0,2)]  # z1, z2
w_order = [(0,1), (2,0)]  # w1, w2

# Sym^2(z) monomials: (z1,z1), (z1,z2), (z2,z2)
sym2_z = [((1,0),(1,0)), ((1,0),(0,2)), ((0,2),(0,2))]
sym2_w = [((0,1),(0,1)), ((0,1),(2,0)), ((2,0),(2,0))]

def qz2_matrix_entry(qi, sj):
    """Coefficient of q_var[qi] * sym2_z[sj] in tr(X^3)."""
    q = q_order[qi]
    if sj == 0:  # z1^2
        key = mono_key([q, z_order[0], z_order[0]])
    elif sj == 1:  # z1*z2
        key = mono_key([q, z_order[0], z_order[1]])
    else:  # z2^2
        key = mono_key([q, z_order[1], z_order[1]])
    return trX3_coeffs.get(key, 0)

qz2_mat = [[qz2_matrix_entry(i,j) for j in range(3)] for i in range(2)]
print(f"\nTarget qz^2 matrix: {qz2_mat}")
# Expected: [[0,0,0],[0,3,0]] with the BILR-matching labeling

def qw2_matrix_entry(qi, sj):
    q = q_order[qi]
    if sj == 0:
        key = mono_key([q, w_order[0], w_order[0]])
    elif sj == 1:
        key = mono_key([q, w_order[0], w_order[1]])
    else:
        key = mono_key([q, w_order[1], w_order[1]])
    return trX3_coeffs.get(key, 0)

qw2_mat = [[qw2_matrix_entry(i,j) for j in range(3)] for i in range(2)]
print(f"Target qw^2 matrix: {qw2_mat}")
# Expected: [[0,3,0],[0,0,0]]

# ── Load BILR scheme and transform to diagonal basis ──
scheme = json.loads((WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json").read_text())
cubes_orig = scheme["cubes"]  # 11 matrices, each 3x3
free_reps = scheme["free_orbit_representatives"]  # 4 dicts with U,V,W

print(f"\nLoaded: {len(cubes_orig)} cubes, {len(free_reps)} free orbit reps")

# Transform form: L' = P^{-1} L^T P  (from tr(L^T M) to tr(L'M') pairing)
P_inv_T = mat_T(P_inv)

def transform_form(L_orig):
    """Given 3x3 matrix L in original basis (packed Euclidean pairing tr(L^T X)),
    compute L' = P^{-1} L^T P in diagonal basis (tr(L' X') pairing)."""
    LT = mat_T(L_orig)
    return mat_mul(mat_mul(P_inv, LT), P_mat)

# Transform cubes
cubes_diag = []
for L in cubes_orig:
    Ld = transform_form(L)
    cubes_diag.append(Ld)

# Extract form components in (p,q,z,w) ordering
# Form l(X') = tr(L' X') = sum L'_{ab} X'_{ba}
# Coefficient of X'_{ba} = n_{ba} is L'_{ab}
def form_components(Ld):
    """Extract (p1,p2,p3, q1,q2, z1,z2, w1,w2) from L' matrix.
    p: coeff of n_{00},n_{11},n_{22} -> L'_{00},L'_{11},L'_{22}
    q: coeff of n_{12},n_{21} -> L'_{21},L'_{12}  [q1=coeff(n_{12}), q2=coeff(n_{21})]
    z: coeff of n_{10},n_{02} -> L'_{01},L'_{20}
    w: coeff of n_{01},n_{20} -> L'_{10},L'_{02}
    """
    return {
        'p': [Ld[0][0]%P, Ld[1][1]%P, Ld[2][2]%P],
        'q': [Ld[2][1]%P, Ld[1][2]%P],   # coeff of q-vars (1,2),(2,1)
        'z': [Ld[0][1]%P, Ld[2][0]%P],   # coeff of z-vars (1,0),(0,2)
        'w': [Ld[1][0]%P, Ld[0][2]%P],   # coeff of w-vars (0,1),(2,0)
    }

# ── Verify cube orbit structure ──
# Under g, form eigenvalues: p->1, q->-1, z->i, w->-i
# But the COEFFICIENT eigenvalue of L'_{ab} is mu_a/mu_b
# g acts on forms: (g*l) has L'_{ab} -> (mu_a/mu_b) L'_{ab}
# So: p-coeffs (L'_{00},L'_{11},L'_{22}) have eig 1
#     q-coeffs: L'_{21} has eig mu_2/mu_1 = -i??? 
# Wait, I need to be more careful.

# The form components as defined above:
# q1 = L'_{21} = coeff of n_{12}. n_{12} has var-eig mu_2/mu_1 = -i (wait that's w-type!)

# I think I'm mixing up the notation. Let me redo.

# q-vars are (1,2) and (2,1) in 0-indexed.
# (1,2) has eigenvalue mu_2/mu_1 = (-i)/i = -1 -> q ✓
# (2,1) has eigenvalue mu_1/mu_2 = i/(-i) = -1 -> q ✓

# Coefficient of n_{(1,2)} = X'_{(1,2)} in l(X') = tr(L'X') = Σ L'_{ab}X'_{ba}
# We need X'_{ba} = X'_{(1,2)}, so (b,a) = (1,2), hence L'_{ab} = L'_{21}.
# So coeff of n_{(1,2)} is L'_{21}. And L'_{21} has coeff-eigenvalue mu_2/mu_1.
# mu_2/mu_1 = i/(-1)... wait, 0-indexed: mu_0=-1, mu_1=i, mu_2=-i.
# L'_{21} has coeff-eig mu_2/mu_1 = (-i)/i = -1. And n_{(1,2)} has var-eig
# mu_2/mu_1 = (-i)/i = -1. Same eigenvalue! Both are q-type. ✓

# Let me redo the extraction:
# coeff of n_{ab} = X'_{ab} is L'_{ba} (since tr(L'X') = Σ L'_{cd}X'_{dc})
# So: coeff(n_{ab}) = L'_{ba}

# q-vars: n_{(1,2)}, n_{(2,1)}
# coeff(n_{(1,2)}) = L'_{(2,1)} -> q1
# coeff(n_{(2,1)}) = L'_{(1,2)} -> q2

# z-vars: n_{(1,0)}, n_{(0,2)}
# coeff(n_{(1,0)}) = L'_{(0,1)} -> z1
# coeff(n_{(0,2)}) = L'_{(2,0)} -> z2

# w-vars: n_{(0,1)}, n_{(2,0)}
# coeff(n_{(0,1)}) = L'_{(1,0)} -> w1
# coeff(n_{(2,0)}) = L'_{(0,2)} -> w2

def form_components_v2(Ld):
    """Correct extraction: coeff of n_{(a,b)} = L'_{(b,a)}."""
    return {
        'p': [Ld[0][0]%P, Ld[1][1]%P, Ld[2][2]%P],
        'q': [Ld[2][1]%P, Ld[1][2]%P],   # coeff of n_{(1,2)}, n_{(2,1)}
        'z': [Ld[0][1]%P, Ld[2][0]%P],   # coeff of n_{(1,0)}, n_{(0,2)}
        'w': [Ld[1][0]%P, Ld[0][2]%P],   # coeff of n_{(0,1)}, n_{(2,0)}
    }

# These are the same as before since L'_{(b,a)} for:
# q: L'_{(2,1)}, L'_{(1,2)} -- same!
# z: L'_{(0,1)}, L'_{(2,0)} -- same!
# w: L'_{(1,0)}, L'_{(0,2)} -- same!

# Verify cube 0 orbit type
print("\n── Cube eigenblock components (first 4 cubes) ──")
for j in range(min(4, len(cubes_diag))):
    fc = form_components_v2(cubes_diag[j])
    print(f"Cube {j}: p={fc['p']}, q={fc['q']}, z={fc['z']}, w={fc['w']}")

# Check Z4 orbit structure: g acts on form by multiplying
# p-coeffs by 1, q-coeffs by -1, z-coeffs by ?, w-coeffs by ?
# The coeff-eigenvalue of L'_{ba} (= coeff of n_{ab}) is mu_b/mu_a
# (same as the variable eigenvalue of n_{ab}).
# Under g, the coefficient L'_{ba} maps to (mu_b/mu_a)*L'_{ba}.
# So the form component mapped to the VARIABLE n_{ab} has eigenvalue mu_b/mu_a.

# For q-vars: eigenvalue -1. Under g, q-comp -> -1 * q-comp.
# For z-vars (1,0),(0,2): eigenvalue i. Under g, z-comp -> i * z-comp.
# For w-vars (0,1),(2,0): eigenvalue -i. Under g, w-comp -> -i * w-comp.

# So g acts on form vector as: p->p, q->(-1)q, z->i*z, w->(-i)*w

# Verify orbit structure of cubes by checking g-action
def apply_g_to_form(fc):
    """Apply Z4 generator to form components."""
    return {
        'p': fc['p'][:],
        'q': [(P-x)%P for x in fc['q']],  # multiply by -1
        'z': [(II*x)%P for x in fc['z']],  # multiply by i
        'w': [((P-II)*x)%P for x in fc['w']],  # multiply by -i
    }

def forms_equal(fc1, fc2):
    return all(fc1[k] == fc2[k] for k in ['p','q','z','w'])

def forms_proportional(fc1, fc2):
    """Check if fc2 = lambda*fc1 for some lambda."""
    all_coords_1 = fc1['p'] + fc1['q'] + fc1['z'] + fc1['w']
    all_coords_2 = fc2['p'] + fc2['q'] + fc2['z'] + fc2['w']
    lam = None
    for a, b in zip(all_coords_1, all_coords_2):
        if a != 0:
            l = (b * inv(a)) % P
            if lam is None:
                lam = l
            elif l != lam:
                return False, 0
        elif b != 0:
            return False, 0
    return True, lam if lam is not None else 0

# Find orbits
cube_fcs = [form_components_v2(cubes_diag[j]) for j in range(11)]
visited = [False]*11
orbits = []
for j in range(11):
    if visited[j]:
        continue
    orbit = [j]
    visited[j] = True
    cur = cube_fcs[j]
    for step in range(1, 4):
        cur = apply_g_to_form(cur)
        # Find matching cube
        found = False
        for k in range(11):
            if not visited[k]:
                prop, lam = forms_proportional(cur, cube_fcs[k])
                if prop and lam != 0:
                    orbit.append(k)
                    visited[k] = True
                    found = True
                    break
        if not found:
            break
    orbits.append(orbit)

print(f"\nZ4 cube orbits: {orbits}")
print(f"Orbit sizes: {[len(o) for o in orbits]}")

# ── Compute residual cubic blocks ──
# The residual = sum of 11 cubes' cubics.
# For each cube l, its qz^2 contribution is:
# 3 * [q1;q2] tensor [z1^2, 2*z1*z2, z2^2]

# For a size-4 orbit sum, the qz^2 contribution is:
# 12 * [q1;q2] tensor [z1^2, 2*z1*z2, z2^2]

# Total residual qz^2 = sum over all 11 cubes' qz^2 contributions
def cube_qz2_matrix(fc):
    """qz^2 contribution of l^3: 3 * q_vec tensor z_sq_vec."""
    q = fc['q']  # [q1, q2]
    z = fc['z']  # [z1, z2]
    z_sq = [(z[0]*z[0])%P, (2*z[0]*z[1])%P, (z[1]*z[1])%P]
    mat = [[(3*q[i]*z_sq[j])%P for j in range(3)] for i in range(2)]
    return mat

def cube_qw2_matrix(fc):
    """qw^2 contribution: 3 * q_vec tensor w_sq_vec."""
    q = fc['q']
    w = fc['w']
    w_sq = [(w[0]*w[0])%P, (2*w[0]*w[1])%P, (w[1]*w[1])%P]
    return [[(3*q[i]*w_sq[j])%P for j in range(3)] for i in range(2)]

# Sum over all 11 cubes
residual_qz2 = [[0]*3 for _ in range(2)]
residual_qw2 = [[0]*3 for _ in range(2)]
for j in range(11):
    m1 = cube_qz2_matrix(cube_fcs[j])
    m2 = cube_qw2_matrix(cube_fcs[j])
    for i in range(2):
        for k in range(3):
            residual_qz2[i][k] = (residual_qz2[i][k] + m1[i][k]) % P
            residual_qw2[i][k] = (residual_qw2[i][k] + m2[i][k]) % P

print(f"\nResidual qz^2 (sum of 11 cubes): {residual_qz2}")
print(f"Residual qw^2 (sum of 11 cubes): {residual_qw2}")
print(f"Target  qz^2: {qz2_mat}")
print(f"Target  qw^2: {qw2_mat}")

# The residual should equal (target - free_orbit_contribution)
# But we can also check: the residual should be decomposable
# into orbit contributions from the known cube orbits.

# For each size-4 orbit, the contribution is 12*q⊗z^2
# For each size-2 orbit: 2*(3*q⊗z^2 + 3*(-q)⊗z^2) = 0 (q-part cancels!)
# Wait: size-2 orbit has g^2*l = l (period 2), so q->(-1)^2*q=q.
# Hmm, for a size-2 orbit, the cube l has l_z=l_w=0.
# So its qz^2 = 3*q⊗(0)^2 = 0. ✓

# For fixed cubes: q=z=w=0, so qz^2 = 0. ✓

# So residual qz^2 = sum over size-4 orbits of 12*q⊗z^2
for orb in orbits:
    if len(orb) == 4:
        rep_fc = cube_fcs[orb[0]]
        contrib = [[(12*rep_fc['q'][i]*((rep_fc['z'][0]**2 if j==0 else 
                     2*rep_fc['z'][0]*rep_fc['z'][1] if j==1 else 
                     rep_fc['z'][1]**2))%P) % P for j in range(3)] for i in range(2)]
        print(f"  Size-4 orbit {orb}: qz^2 = {contrib}")

# ── Check: does residual_qz2 match target? ──
# It should, because residual = tr(X^3) - free_orbit
# And tr(X^3) has qz^2 = target, and free_orbit's qz^2 is computed separately.
# But residual IS the cubes, so residual_qz2 should equal target - free_qz2.
# Alternatively, since tr(X^3) = residual + free_orbit, we have:
# target_qz2 = residual_qz2 + free_orbit_qz2

# Let me also compute the free orbit's qz^2 contribution
# Free orbit: 3 * sum_{k=0}^3 A_k(X)*B_k(X)*C_k(X)
# where (A_k,B_k,C_k) = (g^k A, g^k B, g^k C)

# Transform free orbit representatives
# The JSON gives 4 reps; the first one is the fundamental rep,
# others are Z4 images.
A0 = transform_form(free_reps[0]["U"])
B0 = transform_form(free_reps[0]["V"])
W0 = transform_form(free_reps[0]["W"])

A0_fc = form_components_v2(A0)
B0_fc = form_components_v2(B0)
W0_fc = form_components_v2(W0)

print(f"\nFree orbit rep 0:")
print(f"  A: p={A0_fc['p']}, q={A0_fc['q']}, z={A0_fc['z']}, w={A0_fc['w']}")
print(f"  B: p={B0_fc['p']}, q={B0_fc['q']}, z={B0_fc['z']}, w={B0_fc['w']}")
print(f"  C: p={W0_fc['p']}, q={W0_fc['q']}, z={W0_fc['z']}, w={W0_fc['w']}")

# Compute free orbit qz^2 = 12*[A_q⊗(B_z⊙C_z) + B_q⊗(A_z⊙C_z) + C_q⊗(A_z⊙B_z)]
def sym_prod(u, v, p=P):
    """Symmetric product u⊙v in Sym^2(K^2): (u1v1, u1v2+u2v1, u2v2)."""
    return [(u[0]*v[0])%p, (u[0]*v[1]+u[1]*v[0])%p, (u[1]*v[1])%p]

def outer_q_sym2z(q_vec, sym2, p=P):
    """q ⊗ sym2z as 2x3 matrix."""
    return [[(q_vec[i]*sym2[j])%p for j in range(3)] for i in range(2)]

def mat_add_2x3(A, B, p=P):
    return [[(A[i][j]+B[i][j])%p for j in range(3)] for i in range(2)]

free_qz2_per_term = mat_add_2x3(
    mat_add_2x3(
        outer_q_sym2z(A0_fc['q'], sym_prod(B0_fc['z'], W0_fc['z'])),
        outer_q_sym2z(B0_fc['q'], sym_prod(A0_fc['z'], W0_fc['z']))
    ),
    outer_q_sym2z(W0_fc['q'], sym_prod(A0_fc['z'], B0_fc['z']))
)

# Total: 12 * this
free_qz2 = [[(12*free_qz2_per_term[i][j])%P for j in range(3)] for i in range(2)]

print(f"\nFree orbit qz^2 contribution: {free_qz2}")

# Check: target = residual + free
check_qz2 = [[(residual_qz2[i][j] + free_qz2[i][j])%P for j in range(3)] for i in range(2)]
print(f"Residual + Free = {check_qz2}")
print(f"Target          = {qz2_mat}")
assert check_qz2 == qz2_mat, "qz^2 decomposition FAILED"
print("qz^2 check PASSED ✓")

# Same for qw^2
free_qw2_per_term = mat_add_2x3(
    mat_add_2x3(
        outer_q_sym2z(A0_fc['q'], sym_prod(B0_fc['w'], W0_fc['w'])),
        outer_q_sym2z(B0_fc['q'], sym_prod(A0_fc['w'], W0_fc['w']))
    ),
    outer_q_sym2z(W0_fc['q'], sym_prod(A0_fc['w'], B0_fc['w']))
)
free_qw2 = [[(12*free_qw2_per_term[i][j])%P for j in range(3)] for i in range(2)]
check_qw2 = [[(residual_qw2[i][j] + free_qw2[i][j])%P for j in range(3)] for i in range(2)]
print(f"\nResidual + Free qw^2 = {check_qw2}")
print(f"Target qw^2          = {qw2_mat}")
assert check_qw2 == qw2_mat, "qw^2 decomposition FAILED"
print("qw^2 check PASSED ✓")

# ── Pencil-conic recovery of size-4 orbit forms ──
# Residual qz^2 = 12*(l1_q⊗l1_z^2 + l2_q⊗l2_z^2)
# This is a 2x3 matrix of rank at most 2.
# Each l_z^2 lies on the Veronese conic [t^2:2ts:s^2].
# The rowspace is a pencil of binary quadrics; intersecting
# with the conic gives the two points.

print("\n" + "="*60)
print("Pencil-conic extraction from residual qz^2")
print("="*60)

# Residual qz^2 matrix
R = residual_qz2
print(f"R = {R}")

# Check rank
def rank_2x3(M, p=P):
    """Rank of 2x3 matrix mod p."""
    for i in range(2):
        for j in range(3):
            if M[i][j] % p != 0:
                # Found nonzero entry
                r, c = i, j
                # Eliminate other row
                other = 1 - r
                if M[other][c] % p != 0:
                    factor = (M[other][c] * inv(M[r][c], p)) % p
                    row = [(M[other][k] - factor*M[r][k]) % p for k in range(3)]
                    if any(x % p != 0 for x in row):
                        return 2
                    return 1
                else:
                    return 1 if any(M[other][k]%p != 0 for k in range(3)) else 1
    return 0

rk = rank_2x3(R)
print(f"Rank of residual qz^2: {rk}")

# For the conic intersection:
# Row 0: R[0] = alpha * [z1^2, 2z1z2, z2^2]_1
# Row 1: R[1] = beta  * [z1^2, 2z1z2, z2^2]_2
# A point [a,b,c] on the conic satisfies a*c = (b/2)^2, i.e., 4ac = b^2.

# The rowspace of R is a pencil of quadrics: lambda*R[0] + mu*R[1].
# A quadric [A,B,C] is a square iff B^2 = 4AC (on the Veronese).
# So we solve: (lambda*R[0][1]+mu*R[1][1])^2 = 4*(lambda*R[0][0]+mu*R[1][0])*(lambda*R[0][2]+mu*R[1][2])

# Set mu=1, solve for lambda (or vice versa for projective completeness):
# Let r0 = R[0], r1 = R[1].
# (lambda*r0[1]+r1[1])^2 = 4*(lambda*r0[0]+r1[0])*(lambda*r0[2]+r1[2])

# Expand:
# lambda^2*r0[1]^2 + 2*lambda*r0[1]*r1[1] + r1[1]^2
# = 4*(lambda^2*r0[0]*r0[2] + lambda*(r0[0]*r1[2]+r1[0]*r0[2]) + r1[0]*r1[2])

# Quadratic in lambda:
# (r0[1]^2 - 4*r0[0]*r0[2]) * lambda^2
# + (2*r0[1]*r1[1] - 4*r0[0]*r1[2] - 4*r1[0]*r0[2]) * lambda
# + (r1[1]^2 - 4*r1[0]*r1[2])
# = 0

r0 = R[0]
r1 = R[1]
A_coeff = (r0[1]*r0[1] - 4*r0[0]*r0[2]) % P
B_coeff = (2*r0[1]*r1[1] - 4*r0[0]*r1[2] - 4*r1[0]*r0[2]) % P
C_coeff = (r1[1]*r1[1] - 4*r1[0]*r1[2]) % P

print(f"\nConic-pencil quadratic: {A_coeff}*λ² + {B_coeff}*λ + {C_coeff} = 0")
disc = (B_coeff*B_coeff - 4*A_coeff*C_coeff) % P
print(f"Discriminant = {disc}")

# Check if disc is QR
def is_qr(x, p=P):
    if x % p == 0: return True
    return pow(x, (p-1)//2, p) == 1

def sqrt_mod(x, p=P):
    """Tonelli-Shanks square root mod p."""
    if x % p == 0: return 0
    if not is_qr(x, p): return None
    if p % 4 == 3: return pow(x, (p+1)//4, p)
    # Tonelli-Shanks
    q, s = p-1, 0
    while q % 2 == 0:
        q //= 2; s += 1
    z = 2
    while is_qr(z, p):
        z += 1
    M, c, t, R_ = s, pow(z, q, p), pow(x, q, p), pow(x, (q+1)//2, p)
    while True:
        if t == 1: return R_
        i = 1
        tmp = (t*t) % p
        while tmp != 1:
            tmp = (tmp*tmp) % p; i += 1
        b = pow(c, 1 << (M-i-1), p)
        M, c, t, R_ = i, (b*b)%p, (t*b*b)%p, (R_*b)%p

if disc == 0:
    print("Discriminant = 0: double root")
    lam1 = lam2 = (P - B_coeff) * inv(2*A_coeff) % P
elif is_qr(disc):
    sd = sqrt_mod(disc)
    print(f"Discriminant is QR, sqrt = {sd}")
    inv2A = inv(2*A_coeff)
    lam1 = ((P - B_coeff + sd) * inv2A) % P
    lam2 = ((P - B_coeff - sd) * inv2A) % P
    print(f"Lambda solutions: {lam1}, {lam2}")
else:
    print("Discriminant is NOT QR — roots in F_{p^2}")
    lam1 = lam2 = None

if lam1 is not None:
    # Recover z-squared vectors
    z_sq_1 = [(lam1*r0[j] + r1[j]) % P for j in range(3)]
    z_sq_2 = [(lam2*r0[j] + r1[j]) % P for j in range(3)]
    print(f"\nz-squared vector 1: {z_sq_1}")
    print(f"z-squared vector 2: {z_sq_2}")
    
    # Verify on conic: 4*a*c = b^2
    for idx, zs in enumerate([z_sq_1, z_sq_2]):
        check = (4*zs[0]*zs[2] - zs[1]*zs[1]) % P
        print(f"  z_sq_{idx+1} on conic: {check == 0}")
    
    # Extract z1:z2 ratio from z_sq = [z1^2, 2z1z2, z2^2]
    # If z2 != 0: z1/z2 from z1z2/z2^2 = z1/z2 (if z2^2 != 0)
    for idx, zs in enumerate([z_sq_1, z_sq_2]):
        if zs[2] != 0:
            # z1*z2 / z2^2 = z1/z2
            ratio = (zs[1] * inv(2*zs[2])) % P  # z1z2/(2*z2^2) ... 
            # Actually z_sq = [z1^2, 2z1z2, z2^2]
            # z1/z2 = z1^2/(z1*z2) = zs[0] / (zs[1]/2)
            # Or: sqrt(zs[0]/zs[2]) if possible
            r = (zs[0] * inv(zs[2])) % P  # z1^2/z2^2
            sr = sqrt_mod(r)
            if sr is not None:
                print(f"  z_{idx+1}: z1/z2 = {sr} or {P-sr}")
            else:
                print(f"  z_{idx+1}: z1^2/z2^2 = {r}, NOT a QR -> in F_{{p^2}}")
        elif zs[0] != 0:
            print(f"  z_{idx+1}: z2 = 0, z = [1:0]")
        else:
            print(f"  z_{idx+1}: degenerate")

    # Match against known BILR size-4 orbit z-components
    print("\nBILR size-4 orbit z-components:")
    for orb in orbits:
        if len(orb) == 4:
            rep = cube_fcs[orb[0]]
            z = rep['z']
            z_sq_known = [(z[0]*z[0])%P, (2*z[0]*z[1])%P, (z[1]*z[1])%P]
            print(f"  Orbit {orb}: z={z}, z^2={z_sq_known}")
            # Check projective match
            for idx, zs in enumerate([z_sq_1, z_sq_2]):
                if all(x==0 for x in zs): continue
                for k in range(3):
                    if z_sq_known[k] != 0:
                        ratio = (zs[k] * inv(z_sq_known[k])) % P
                        consistent = all(
                            (zs[j] - ratio*z_sq_known[j])%P == 0 for j in range(3)
                        )
                        if consistent:
                            print(f"    -> matches conic point {idx+1} with factor {ratio}")
                        break

# Save results
results = {
    "prime": P, "imag_unit": II,
    "eigenvalues": [int(x) for x in mu],
    "variable_groups": {
        "p": [list(x) for x in p_vars],
        "q": [list(x) for x in q_vars],
        "z": [list(x) for x in z_vars],
        "w": [list(x) for x in w_vars],
    },
    "target_qz2": qz2_mat,
    "target_qw2": qw2_mat,
    "residual_qz2": [[int(x) for x in row] for row in residual_qz2],
    "residual_qw2": [[int(x) for x in row] for row in residual_qw2],
    "free_orbit_qz2": [[int(x) for x in row] for row in free_qz2],
    "cube_orbits": orbits,
    "cube_orbit_sizes": [len(o) for o in orbits],
    "qz2_conic_discriminant": int(disc),
    "qz2_conic_discriminant_is_QR": is_qr(disc),
}

(OUT / "diagonal_block_analysis.json").write_text(json.dumps(results, indent=2)+'\n')
print(f"\nSaved {OUT/'diagonal_block_analysis.json'}")
