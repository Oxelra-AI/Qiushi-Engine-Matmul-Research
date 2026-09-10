#!/usr/bin/env python3
"""
analysis: Reconstruct the BILR S_{2fix-Z_3} (f,m)=(2,7) rank-23 scheme,
verify it, compute the residual cubic, its annihilator, catalecticant rank,
and Koszul-Young flattening rank. Then check if the annihilator can grow
by one dimension (i.e., whether (1,7) rank-22 is first-order feasible).

Reference: Ballard-Ikenmeyer-Landsberg-Ryder, JPAA 2018, Section 2.4.
"""
import sys, json, itertools
import numpy as np
from pathlib import Path

OUT = Path('data/bilr_27')
OUT.mkdir(parents=True, exist_ok=True)

# ── 1. Build T_{333} ──────────────────────────────────────────────────
def build_T333():
    """Build the 3x3 matrix multiplication tensor in row-major convention."""
    T = np.zeros((9,9,9), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a = 3*i + j  # E_{ij}
                b = 3*j + k  # E_{jk}
                c = 3*k + i  # E_{ki}
                T[a,b,c] = 1
    return T

# ── 2. BILR S_{2fix-Z_3} scheme ──────────────────────────────────────
def build_bilr_27_scheme():
    """
    BILR Section 2.4: 2 cubes + 7 free Z_3 orbits = 23 terms.
    Each 3x3 matrix is row-major vectorized to a 9-vector.
    """
    def mat2vec(M):
        return np.array(M, dtype=np.int64).flatten()

    cubes = [
        mat2vec([[1,0,0],[0,0,1],[0,0,1]]),
        mat2vec([[0,0,0],[0,1,-1],[0,0,0]]),
    ]

    # 7 free cyclic orbits: (U, V, W) triples
    orbits = [
        (mat2vec([[0,1,0],[0,0,1],[0,0,0]]),
         mat2vec([[0,0,0],[0,1,-1],[0,1,-1]]),
         mat2vec([[0,0,0],[1,0,-1],[0,0,0]])),

        (mat2vec([[0,-1,1],[0,0,0],[0,0,0]]),
         mat2vec([[0,0,0],[0,0,0],[0,0,1]]),
         mat2vec([[0,0,0],[0,0,0],[1,0,0]])),

        (mat2vec([[1,0,0],[1,0,0],[0,0,0]]),
         mat2vec([[0,-1,1],[0,0,0],[0,0,0]]),
         mat2vec([[0,0,0],[0,0,0],[0,1,0]])),

        (mat2vec([[1,0,0],[0,0,1],[0,0,0]]),
         mat2vec([[0,1,0],[0,0,1],[0,0,1]]),
         mat2vec([[0,0,0],[1,0,-1],[0,1,-1]])),

        (mat2vec([[1,0,0],[0,0,0],[0,0,0]]),
         mat2vec([[0,0,1],[0,0,1],[0,0,1]]),
         mat2vec([[0,0,0],[0,0,0],[1,-1,0]])),

        (mat2vec([[0,0,0],[0,0,1],[0,0,0]]),
         mat2vec([[0,1,0],[0,1,0],[0,1,0]]),
         mat2vec([[0,0,0],[-1,1,0],[0,0,0]])),

        (mat2vec([[0,0,0],[0,0,1],[0,0,1]]),
         mat2vec([[1,0,0],[1,0,0],[1,0,0]]),
         mat2vec([[-1,1,0],[0,0,0],[0,0,0]])),
    ]
    return cubes, orbits

def expand_scheme(cubes, orbits):
    """Expand cyclic scheme into (U, V, W) factor lists for all 23 terms."""
    Us, Vs, Ws = [], [], []
    for c in cubes:
        Us.append(c); Vs.append(c); Ws.append(c)
    for U, V, W in orbits:
        # term 1: U⊗V⊗W
        Us.append(U); Vs.append(V); Ws.append(W)
        # term 2: V⊗W⊗U  (cyclic shift of factors)
        Us.append(V); Vs.append(W); Ws.append(U)
        # term 3: W⊗U⊗V
        Us.append(W); Vs.append(U); Ws.append(V)
    return np.array(Us), np.array(Vs), np.array(Ws)

def verify_brent(T, Us, Vs, Ws):
    """Check all 729 Brent identities."""
    recon = np.zeros_like(T)
    for i in range(len(Us)):
        recon += np.einsum('a,b,c->abc', Us[i], Vs[i], Ws[i])
    return int(np.max(np.abs(recon - T))), recon

# ── 3. Cubic polynomial infrastructure ────────────────────────────────
def cubic_monomial_index():
    """Enumerate monomials x_i x_j x_k for 0 <= i <= j <= k < 9.
    Returns list of (i,j,k) and dict (i,j,k) -> index."""
    monoms = []
    idx = {}
    for i in range(9):
        for j in range(i, 9):
            for k in range(j, 9):
                idx[(i,j,k)] = len(monoms)
                monoms.append((i,j,k))
    return monoms, idx

def cubic_to_coeffs(cubes_list, orbits_list, is_residual=False):
    """
    Compute the cubic polynomial tr(M^3) - 3*sum_orbits or the residual
    (which should equal sum_cubes^3).

    Returns coefficients in the symmetric monomial basis.
    """
    monoms, idx = cubic_monomial_index()
    n_monoms = len(monoms)  # C(11,3) = 165

    # tr(M^3) = sum_{i,j,k} M_{ij} M_{jk} M_{ki}
    trM3 = np.zeros(n_monoms, dtype=np.float64)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a, b, c = 3*i+j, 3*j+k, 3*k+i
                triple = tuple(sorted([a,b,c]))
                # count multiplicity
                if a == b == c:
                    mult = 1
                elif a == b or b == c or a == c:
                    mult = 3
                else:
                    mult = 6
                trM3[idx[triple]] += 1.0 / mult * mult  # normalize: coefficient * mult = 1
    # Actually, let me redo this more carefully.
    # tr(M^3) = sum_{ijk} x_{ij} x_{jk} x_{ki}
    # As a symmetric polynomial: coeff of x_a x_b x_c in tr(M^3) =
    # number of (i,j,k) permutations mapping to the monomial.
    trM3 = np.zeros(n_monoms, dtype=np.float64)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a, b, c = 3*i+j, 3*j+k, 3*k+i
                triple = tuple(sorted([a,b,c]))
                trM3[idx[triple]] += 1.0

    # Orbit contribution: 3 * l_U(x) * l_V(x) * l_W(x)
    orbit_contrib = np.zeros(n_monoms, dtype=np.float64)
    for U, V, W in orbits_list:
        # l_U * l_V * l_W = sum_{a,b,c} U_a V_b W_c x_a x_b x_c
        for a in range(9):
            if U[a] == 0: continue
            for b in range(9):
                if V[b] == 0: continue
                for c in range(9):
                    if W[c] == 0: continue
                    triple = tuple(sorted([a,b,c]))
                    orbit_contrib[idx[triple]] += U[a] * V[b] * W[c]
    orbit_contrib *= 3.0  # factor of 3 for each orbit

    # Cube contribution: sum l_i^3
    cube_contrib = np.zeros(n_monoms, dtype=np.float64)
    for u in cubes_list:
        for a in range(9):
            if u[a] == 0: continue
            for b in range(a, 9):
                if u[b] == 0: continue
                for c in range(b, 9):
                    if u[c] == 0: continue
                    triple = (a,b,c)
                    if a == b == c:
                        cube_contrib[idx[triple]] += u[a]**3
                    elif a == b:
                        cube_contrib[idx[triple]] += 3 * u[a]**2 * u[c]
                    elif b == c:
                        cube_contrib[idx[triple]] += 3 * u[a] * u[b]**2
                    elif a == c:
                        # shouldn't happen since a <= b <= c
                        pass
                    else:
                        cube_contrib[idx[triple]] += 6 * u[a] * u[b] * u[c]

    residual = trM3 - orbit_contrib
    return trM3, orbit_contrib, cube_contrib, residual, monoms, idx

# ── 4. Catalecticant and annihilator ──────────────────────────────────
def catalecticant(coeffs, monoms, idx):
    """
    Build the 9 x 45 catalecticant matrix Cat_1,2 for a cubic in 9 variables.
    Cat[a, (b,c)] = coeff of x_a x_b x_c in the cubic.
    The quadratic monomials (b,c) with b <= c.
    """
    quad_monoms = []
    quad_idx = {}
    for b in range(9):
        for c in range(b, 9):
            quad_idx[(b,c)] = len(quad_monoms)
            quad_monoms.append((b,c))
    n_quad = len(quad_monoms)  # 45

    Cat = np.zeros((9, n_quad), dtype=np.float64)
    for a in range(9):
        for (b,c), qi in quad_idx.items():
            triple = tuple(sorted([a,b,c]))
            Cat[a, qi] = coeffs[idx[triple]]
    return Cat, quad_monoms

def hessian_slices(coeffs, monoms, idx):
    """
    Compute 9 Hessian slice matrices H_k, each 9x9 symmetric.
    H_k[i,j] = d^3 C / dx_i dx_j dx_k = coefficient of x_i x_j x_k
    (with appropriate multiplicity normalization for the symmetric monomial basis).

    Actually, for our coefficient convention:
    C(x) = sum_{i<=j<=k} c_{ijk} * (multiplicity) * x_i x_j x_k
    where multiplicity accounts for permutations.
    The third partial derivative d^3C/dx_i dx_j dx_k = c_{ijk} * multiplicity
    for the sorted triple. But the Hessian slice H_k[i,j] = d^3C/dx_i dx_j dx_k.
    """
    H = np.zeros((9, 9, 9), dtype=np.float64)
    for (i,j,k), ci in zip(monoms, coeffs):
        # The coefficient c_{ijk} in our basis corresponds to the actual
        # polynomial coefficient times the multinomial coefficient.
        # C(x) = sum c_{ijk} x_i x_j x_k (summing over ALL ordered triples)
        # So c_{ijk} is the coefficient for the ordered triple.
        # In the symmetric basis, the stored coefficient is for unordered triple.
        # Actually, let me reconsider the convention.
        # We stored: coeffs[idx[(i,j,k)]] where (i,j,k) is sorted.
        # This represents the sum over all permutations of (i,j,k).
        # For the third derivative: d^3 C / dx_a dx_b dx_c = 6 * c_{abc} (unsorted)
        # where c_{abc} is the UNSORTED coefficient.
        # In our convention: for sorted (i,j,k), the sum over permutations gives
        # multinomial * c_unsorted = stored value.
        # So c_unsorted = stored / multinomial.
        # The third derivative is 6 * c_unsorted = 6 * stored / multinomial.
        # For H_k[i,j]: this is 6 * c_{ijk_unsorted} = stored value * 6/mult.
        # But actually, we stored the raw sum of contributions, not with multinomial normalization.
        # Let me just directly compute from the definition.
        pass

    # Simpler approach: build the tensor of third derivatives directly
    # from the raw coefficient storage.
    # Our coeffs[idx[(i,j,k)]] = sum of contributions from all instances
    # producing the sorted triple (i,j,k).
    # For tr(M^3), each (i,j,k) triple gives one contribution.
    # The third derivative d^3C/dx_a dx_b dx_c counts the number of
    # ordered triples (a,b,c) that contribute, times the coefficient per instance.

    # Let me just build H from the original formula.
    return H  # placeholder

# ── 5. Better: work modular for exactness ─────────────────────────────
def mod_matrix_rank(M, p):
    """Compute rank of integer matrix M modulo prime p."""
    M_mod = (M % p).astype(np.int64)
    n, m = M_mod.shape
    rank = 0
    used_rows = [False] * n
    for col in range(m):
        pivot = -1
        for row in range(n):
            if not used_rows[row] and M_mod[row, col] % p != 0:
                pivot = row
                break
        if pivot == -1:
            continue
        used_rows[pivot] = True
        rank += 1
        inv_val = pow(int(M_mod[pivot, col]), p-2, p)
        for row in range(n):
            if row != pivot and M_mod[row, col] % p != 0:
                factor = (M_mod[row, col] * inv_val) % p
                M_mod[row] = (M_mod[row] - factor * M_mod[pivot]) % p
    return rank

def build_integer_catalecticant(cubes_vec, orbits_vec):
    """
    Build exact integer catalecticant of the residual cubic C = tr(M^3) - 3*sum orbits.
    Cat_1,2: rows indexed by linear forms (x_a), columns by quadratic forms (x_b x_c).
    Cat[a, (b,c)] = d^3C/dx_a dx_b dx_c (the third partial).

    For tr(M^3) = sum_{ijk} x_{ij} x_{jk} x_{ki}:
    d^3(tr(M^3))/dx_a dx_b dx_c = number of (i,j,k) s.t. {3i+j, 3j+k, 3k+i} = {a,b,c} as multiset.

    For 3*l_U*l_V*l_W:
    d^3(3*l_U*l_V*l_W)/dx_a dx_b dx_c = 3 * sum over permutations (p,q,r) of (a,b,c): U_p V_q W_r
    = 3*(U_a V_b W_c + U_a V_c W_b + U_b V_a W_c + U_b V_c W_a + U_c V_a W_b + U_c V_b W_a)
    """
    # Build third derivative tensor D[a,b,c] for the residual
    D = np.zeros((9,9,9), dtype=np.int64)

    # tr(M^3) contribution
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a, b, c = 3*i+j, 3*j+k, 3*k+i
                for p,q,r in itertools.permutations([a,b,c]):
                    D[p,q,r] += 1

    # Orbit contribution: -3 * sum_orbits l_U l_V l_W
    for U, V, W in orbits_vec:
        for a in range(9):
            for b in range(9):
                for c in range(9):
                    val = 3 * (U[a]*V[b]*W[c] + U[a]*V[c]*W[b] +
                               U[b]*V[a]*W[c] + U[b]*V[c]*W[a] +
                               U[c]*V[a]*W[b] + U[c]*V[b]*W[a])
                    D[a,b,c] -= val

    # Catalecticant: Cat[a, idx(b,c)] = D[a,b,c] for b <= c
    # but D should be symmetric in all three indices, so D[a,b,c] = D for any permutation
    quad_list = [(b,c) for b in range(9) for c in range(b,9)]
    Cat = np.zeros((9, len(quad_list)), dtype=np.int64)
    for a in range(9):
        for qi, (b,c) in enumerate(quad_list):
            Cat[a, qi] = D[a,b,c]

    return D, Cat, quad_list

def build_koszul_young_flattening(D):
    """
    Build the Koszul-Young flattening F_P: Lambda^4(V) tensor V* -> Lambda^5(V) tensor V.
    For a cubic C with third-derivative tensor D[a,b,c]:
    F_P maps (e_{i1}^...^e_{i4}) tensor e_j* to sum_k D[j,k,*] acting on the exterior.

    Actually, the correct Koszul-Young flattening for a cubic (d=3) in n=9 variables:
    P = (2,1,1,1,1) Young diagram gives the map
    Lambda^4(V) x V* -> Lambda^5(V) x V
    (or similar; the key property is that a pure cube l^3 has image rank = C(8,4) = 70).

    Concretely: for basis e_0,...,e_8 of V=K^9,
    F maps (e_{i1}^...^e_{i4}, e_j*) to sum_{k=0}^{8} D[j,k,*] * (something involving wedge).

    The actual map from the Landsberg-Ottaviani paper:
    For C(x) = sum D_{abc}/6 x_a x_b x_c,
    (F_C)(w)(e_{i1}^...^e_{ip} tensor e_j) = sum_k (dC/dx_j dx_k)(w) * e_k wedge e_{i1}^...^e_{ip} tensor e_j
    ... this needs careful implementation. Let me use the slice-matrix approach.

    The catalecticant-like flattening: for a cubic C, define the map
    phi: V -> S^2 V* by phi(e_a) = (sum_b D[a,b,c] x_b x_c) / 2.
    This is the 9x45 catalecticant.

    The Koszul-Young flattening is the antisymmetrized version.
    F: Lambda^4 V tensor V* -> Lambda^5 V tensor V
    For (e_{i1}^...^e_{i4}, e_j*), the image is:
    sum_{k} sum_{l} D[j,k,l] * (e_l wedge e_{i1}^...^e_{i4}) tensor e_k

    Wait, I need to be more careful. Let me use the formulation from analysis.
    """
    n = 9
    # Lambda^4(V) has dim C(9,4) = 126
    # V* has dim 9
    # Lambda^5(V) has dim C(9,5) = 126
    # V has dim 9
    # So the flattening is (126*9) x (126*9) = 1134 x 1134

    from itertools import combinations

    basis4 = list(combinations(range(n), 4))
    basis5 = list(combinations(range(n), 5))
    idx4 = {b: i for i, b in enumerate(basis4)}
    idx5 = {b: i for i, b in enumerate(basis5)}

    dim4 = len(basis4)  # 126
    dim5 = len(basis5)  # 126

    # Flattening matrix: rows = (Lambda^5 V) x V, cols = (Lambda^4 V) x V*
    # F[(alpha5, k), (alpha4, j)] = sum_l D[j,k,l] * wedge_coeff(l, alpha4, alpha5)
    # where wedge_coeff(l, alpha4, alpha5) = sign if {l} union alpha4 = alpha5, else 0

    F = np.zeros((dim5 * n, dim4 * n), dtype=np.int64)

    for ci4, alpha4 in enumerate(basis4):
        alpha4_set = set(alpha4)
        for j in range(n):
            col = ci4 * n + j
            for k in range(n):
                for l in range(n):
                    if D[j,k,l] == 0:
                        continue
                    if l in alpha4_set:
                        continue
                    alpha5_list = sorted(list(alpha4) + [l])
                    alpha5_tuple = tuple(alpha5_list)
                    if alpha5_tuple not in idx5:
                        continue
                    ci5 = idx5[alpha5_tuple]
                    # sign of wedge: sign of permutation inserting l into alpha4
                    sign = 1
                    for m_idx, m_val in enumerate(alpha4):
                        if l < m_val:
                            break
                        sign *= -1
                    else:
                        # l is larger than all elements
                        pass
                    # Actually compute sign properly
                    pos = 0
                    for m_val in alpha4:
                        if l > m_val:
                            pos += 1
                    sign = (-1)**pos

                    row = ci5 * n + k
                    F[row, col] += D[j,k,l] * sign

    return F

def main():
    T = build_T333()
    cubes, orbits = build_bilr_27_scheme()
    Us, Vs, Ws = expand_scheme(cubes, orbits)

    # Verify Brent equations
    max_err, _ = verify_brent(T, Us, Vs, Ws)
    print(f"BILR (2,7) Brent max error: {max_err}")
    assert max_err == 0, "Brent verification failed!"

    # Build exact residual third-derivative tensor
    orbit_vecs = list(orbits)
    D_residual, Cat, quad_list = build_integer_catalecticant(cubes, orbit_vecs)

    # Verify residual = sum of 2 cubes
    D_cubes = np.zeros((9,9,9), dtype=np.int64)
    for u in cubes:
        for a in range(9):
            for b in range(9):
                for c in range(9):
                    D_cubes[a,b,c] += 6 * u[a] * u[b] * u[c]

    cube_match = np.max(np.abs(D_residual - D_cubes))
    print(f"Residual = sum of cubes: max diff = {cube_match}")

    # Catalecticant rank (modular)
    primes = [1000003, 65521, 32003]
    cat_ranks = {}
    for p in primes:
        cat_ranks[str(p)] = mod_matrix_rank(Cat.copy(), p)
    print(f"Catalecticant ranks: {cat_ranks}")
    print(f"Cat shape: {Cat.shape}")

    # Annihilator: kernel of Cat^T (left kernel of Cat)
    # Cat is 9 x 45. Left kernel = {a in K^9 : a^T Cat = 0}
    # = kernel of Cat^T (45 x 9)
    ann_dim = 9 - min(cat_ranks.values())
    print(f"Annihilator dimension (9 - cat_rank): {ann_dim}")

    # Compute the actual annihilator directions
    # Use SVD for numerical annihilator
    U_svd, S_svd, Vt_svd = np.linalg.svd(Cat.astype(np.float64))
    tol = 1e-10
    ann_vecs = U_svd[:, S_svd < tol]
    print(f"Numerical annihilator vectors: {ann_vecs.shape[1]}")
    if ann_vecs.shape[1] > 0:
        print(f"Annihilator basis (rows):")
        for i in range(ann_vecs.shape[1]):
            print(f"  {ann_vecs[:, i]}")

    # Verify: each cube direction should NOT be in the annihilator
    for ci, u in enumerate(cubes):
        # u^T Cat should be nonzero
        prod = u.astype(np.float64) @ Cat.astype(np.float64)
        print(f"Cube {ci} catalecticant product norm: {np.linalg.norm(prod):.6f}")

    # ── Koszul-Young flattening rank ──────────────────────────────────
    print("\nBuilding Koszul-Young flattening...")
    F = build_koszul_young_flattening(D_residual)
    print(f"Koszul matrix shape: {F.shape}")
    koszul_ranks = {}
    for p in primes:
        koszul_ranks[str(p)] = mod_matrix_rank(F.copy(), p)
    print(f"Koszul ranks: {koszul_ranks}")

    # ── First-order annihilator perturbation analysis ─────────────────
    # At the BILR (2,7) point, the residual has catalecticant rank 2.
    # Under SL_3 perturbation of the 7 orbits, the catalecticant changes.
    # For (1,7): we need catalecticant rank to drop to 1.
    # Question: is there an infinitesimal SL_3 direction that drops rank by 1?

    # The SL_3 perturbation of orbit s: (U_s, V_s, W_s) -> (U_s + eps*dU_s, ...)
    # where (dU_s, dV_s, dW_s) = (X*U_s, X*V_s, X*W_s) for X in sl_3 (8-dim).
    # Here * means the matrix X acts on the 3x3 matrix U_s by M -> XM - MX
    # (adjoint action on gl_3), restricted to sl_3 = traceless matrices.
    # Actually, the internal SL_3 acts on the three-plane by basis change
    # within the three-plane. So dU = alpha*V + beta*W, dV = ..., etc.
    # But for the orbits living in K^9, the action is:
    # g_s in SL_3 acts: (U_s, V_s, W_s) -> (U_s, V_s, W_s) * g_s
    # meaning the three vectors are right-multiplied by g_s (as column vectors
    # of a 9x3 matrix). The Lie algebra element X in sl_3 gives
    # (dU_s, dV_s, dW_s) = (U_s, V_s, W_s) * X
    # i.e., dU_s = X_{11}*U_s + X_{21}*V_s + X_{31}*W_s, etc.

    # For the derivative of the catalecticant:
    # dCat[a, (b,c)] / d(epsilon) at the BILR point
    # comes from the change in the residual's third derivative tensor:
    # dD[a,b,c] = -3 * d/deps [sum_s (U_s+eps*dU_s)_a (V_s+eps*dV_s)_b (W_s+eps*dW_s)_c + perms]
    #           = -3 * sum_s [dU_s_a V_s_b W_s_c + U_s_a dV_s_b W_s_c + U_s_a V_s_b dW_s_c + perms of (a,b,c)]

    # For the rank to drop from 2 to 1: the 2-dim row space of Cat must collapse.
    # This requires the perturbation dCat to move one of the two independent rows
    # into the span of the other.

    # Let's compute the derivative of Cat for each sl_3 generator and each orbit.
    sl3_basis = []
    for i in range(3):
        for j in range(3):
            M = np.zeros((3,3), dtype=np.int64)
            if i != j:
                M[i,j] = 1
                sl3_basis.append(M.flatten())  # E_{ij} for i != j
    # Diagonal: E_{00}-E_{11}, E_{11}-E_{22}
    for d in range(2):
        M = np.zeros((3,3), dtype=np.int64)
        M[d,d] = 1; M[d+1,d+1] = -1
        sl3_basis.append(M.flatten())
    sl3_basis = [np.array(x, dtype=np.int64) for x in sl3_basis]
    print(f"\nsl_3 basis dimension: {len(sl3_basis)}")

    # For each orbit s and sl_3 generator X, compute dCat
    # Internal SL_3 acts on the three-plane basis (U_s, V_s, W_s).
    # Let the three-plane be spanned by columns of the 9x3 matrix [U_s|V_s|W_s].
    # The sl_3 generator X (as a 3x3 matrix) gives:
    # d[U_s|V_s|W_s] = [U_s|V_s|W_s] * X
    # So dU_s = X[0,0]*U_s + X[1,0]*V_s + X[2,0]*W_s
    #    dV_s = X[0,1]*U_s + X[1,1]*V_s + X[2,1]*W_s
    #    dW_s = X[0,2]*U_s + X[1,2]*V_s + X[2,2]*W_s

    # Row space of Cat at BILR point (numerically)
    Cat_f = Cat.astype(np.float64)
    U_cat, S_cat, Vt_cat = np.linalg.svd(Cat_f, full_matrices=True)
    rank_cat = np.sum(S_cat > 1e-10)
    print(f"Catalecticant SVD rank: {rank_cat}")
    if rank_cat == 2:
        # The row space is spanned by the first 2 left singular vectors
        # For rank to drop to 1, we need some perturbation dCat such that
        # Cat + eps*dCat has rank 1.
        # Equivalently: the 2x45 reduced catalecticant (projected to row space)
        # must become rank 1.
        # At eps=0, the 2x45 matrix has rank 2. For rank to drop:
        # det of all 2x2 minors must vanish. The first-order condition for
        # the 2x2 minor det(Cat_reduced[:, [j,k]]) to vanish is:
        # d/deps det(M + eps dM) = tr(adj(M) dM). At a rank-2 point,
        # this is automatically zero for the vanishing minors, and the condition
        # is on the non-vanishing minors.

        # More concretely: Cat has rows r1, r2 (the 2 independent row vectors).
        # For Cat + eps*dCat to have rank 1: r1 + eps*dr1 must be proportional
        # to r2 + eps*dr2. At first order: dr1 * r2 - dr2 * r1 = 0 (cross product).
        # In 45 dimensions: (dr1 - lambda*dr2) must be proportional to (r2 - lambda*r1)
        # for some lambda. Actually for a 2x45 matrix to have rank <=1:
        # row1 = alpha * row2. At perturbation: r1 + eps*dr1 = alpha * (r2 + eps*dr2).
        # At eps=0: r1 ≠ alpha*r2 (rank 2). So no perturbation makes it rank 1 at first order.
        # Wait, that's wrong. Let me think again.

        # The set {M: rank(M) <= 1} is a closed algebraic variety in the space of 2xm matrices.
        # The tangent cone at a rank-2 point is... well, a rank-2 point is a smooth point of
        # the full matrix space, and the rank-1 variety has codimension 1 (it's the vanishing
        # of all 2x2 minors). Actually no: a 2x45 matrix has rank <=1 iff all 2x2 minors vanish.
        # There are C(45,2) = 990 minors. For a generic rank-2 matrix, this is a codimension-1
        # condition (the variety of rank <=1 has codimension m-1 in the space of 2xm matrices,
        # for m >= 2. So codimension 44.

        # Hmm, codimension 44 in the space of 2x45 matrices. Our perturbation space has
        # dimension 7 * 8 = 56 (7 orbits, 8 sl_3 generators each). So we'd need to check
        # if the 56 perturbation directions can reach the codimension-44 rank-drop variety.

        # Actually, the BILR Cat has integer entries, and we can project the perturbations
        # to the orthogonal complement of the row space. The condition for rank drop is
        # that the perturbation projected to the complement must be zero for BOTH rows.

        # Let me just compute: for each sl_3 direction on each orbit, compute dCat,
        # and check if any linear combination makes the augmented matrix rank 1.

        # Compute all perturbation catalecticants
        dCats = []
        for s, (U, V, W) in enumerate(orbits):
            for xi, X_flat in enumerate(sl3_basis):
                X = X_flat.reshape(3,3)
                # dU = X[0,0]*U + X[1,0]*V + X[2,0]*W
                dU = X[0,0]*U + X[1,0]*V + X[2,0]*W
                dV = X[0,1]*U + X[1,1]*V + X[2,1]*W
                dW = X[0,2]*U + X[1,2]*V + X[2,2]*W

                # dD[a,b,c] = -3 * (dU_a V_b W_c + U_a dV_b W_c + U_a V_b dW_c
                #                   + all permutations of (a,b,c))
                dD = np.zeros((9,9,9), dtype=np.int64)
                for a in range(9):
                    for b in range(9):
                        for c in range(9):
                            val = (dU[a]*V[b]*W[c] + U[a]*dV[b]*W[c] + U[a]*V[b]*dW[c])
                            # symmetrize over (a,b,c) permutations
                            for pa,pb,pc in itertools.permutations([a,b,c]):
                                t = (dU[pa]*V[pb]*W[pc] + U[pa]*dV[pb]*W[pc] + U[pa]*V[pb]*dW[pc])
                                dD[a,b,c] += t
                                break  # only need D[a,b,c], but D is already the full third deriv
                            # Actually, dD should already account for the symmetrization
                            # Let me just accumulate directly
                # Redo more carefully
                dD = np.zeros((9,9,9), dtype=np.int64)
                for a in range(9):
                    for b in range(9):
                        for c in range(9):
                            # The third derivative of -3*l_dU*l_V*l_W is:
                            # -3 * sum over perms of (a,b,c): dU_p * V_q * W_r
                            for pa,pb,pc in itertools.permutations([a,b,c]):
                                dD[a,b,c] -= 3*(dU[pa]*V[pb]*W[pc] +
                                                 U[pa]*dV[pb]*W[pc] +
                                                 U[pa]*V[pb]*dW[pc])

                # Extract catalecticant perturbation
                dCat = np.zeros((9, len(quad_list)), dtype=np.int64)
                for a in range(9):
                    for qi, (b,c) in enumerate(quad_list):
                        dCat[a, qi] = dD[a,b,c]
                dCats.append((s, xi, dCat))

        print(f"Computed {len(dCats)} perturbation catalecticants")

        # Now check: is there a linear combination of dCats such that
        # Cat + eps * sum(alpha_i * dCat_i) has rank <= 1?
        # At first order, this means the perturbation must bring both rows
        # into a 1-dimensional space. More precisely: for a 9x45 rank-2 matrix,
        # rank drop to 1 requires specific conditions.

        # Project Cat to its row space (2D)
        # Row space basis: first 2 right singular vectors
        # Cat_proj = Cat * V^T[:2, :]^T  -> 9x2 matrix
        Cat_proj = Cat_f @ Vt_cat[:2, :].T  # 9x2
        # Each dCat projected similarly
        dCat_projs = []
        for s, xi, dCat in dCats:
            dCat_proj = dCat.astype(np.float64) @ Vt_cat[:2, :].T  # 9x2
            dCat_projs.append(dCat_proj)

        # For Cat + eps*dCat to have rank 1 in the 9x45 space:
        # All 2x2 minors of Cat + eps*dCat must vanish.
        # But Cat has rank 2, so many 2x2 minors are nonzero.
        # The first-order conditions: d/deps [all nonzero 2x2 minors] = 0.
        # There are C(9,2) * C(45,2) = 36 * 990 minors, but most are zero.
        # A better approach: the 9x2 projected matrix Cat_proj + eps*dCat_proj
        # must have rank <= 1.
        # For a 9x2 matrix to have rank <= 1: all 2x2 minors vanish.
        # There are C(9,2) = 36 such minors.

        # At the BILR point, Cat_proj has rank 2.
        # The 36 minors of Cat_proj are mostly nonzero.
        # For Cat_proj + eps*sum(alpha*dCat_proj) to have rank 1 at first order:
        # d/deps [minor_{ij}] = 0 for all nonzero minors {ij}.
        # This gives 36 linear equations in the alpha's (56 variables).
        # If the system has rank 36, there's a 20-dim solution space at first order.
        # But we also need the second-order condition for the zero minors.

        # Actually, let's be more careful. For rank to drop from 2 to 1:
        # all 36 minors of the 9x2 matrix must vanish simultaneously.
        # At eps=0, some minors are nonzero. So at first order, we need
        # all the derivatives of the nonzero minors to vanish. This is
        # a linear condition on the alpha's.

        # Compute the 36 minors of Cat_proj and their derivatives
        nonzero_minors = []
        minor_derivs = []  # each is a vector of length 56 (the alpha's)
        for i in range(9):
            for j in range(i+1, 9):
                # minor = Cat_proj[i,0]*Cat_proj[j,1] - Cat_proj[i,1]*Cat_proj[j,0]
                minor_val = Cat_proj[i,0]*Cat_proj[j,1] - Cat_proj[i,1]*Cat_proj[j,0]
                if abs(minor_val) > 1e-10:
                    nonzero_minors.append((i,j,minor_val))
                    # derivative: d(minor)/d(alpha_k) =
                    # dCat_proj_k[i,0]*Cat_proj[j,1] + Cat_proj[i,0]*dCat_proj_k[j,1]
                    # - dCat_proj_k[i,1]*Cat_proj[j,0] - Cat_proj[i,1]*dCat_proj_k[j,0]
                    deriv = np.zeros(len(dCats))
                    for k, dCp in enumerate(dCat_projs):
                        deriv[k] = (dCp[i,0]*Cat_proj[j,1] + Cat_proj[i,0]*dCp[j,1]
                                   - dCp[i,1]*Cat_proj[j,0] - Cat_proj[i,1]*dCp[j,0])
                    minor_derivs.append(deriv)

        print(f"Nonzero 2x2 minors of projected Cat: {len(nonzero_minors)} / 36")

        if minor_derivs:
            # Stack into matrix: rows = minor constraints, cols = perturbation parameters
            A_first_order = np.array(minor_derivs)  # (n_nonzero x 56)
            print(f"First-order constraint matrix: {A_first_order.shape}")
            rank_fo = np.linalg.matrix_rank(A_first_order, tol=1e-8)
            print(f"First-order constraint rank: {rank_fo}")
            kernel_dim = len(dCats) - rank_fo
            print(f"First-order perturbation kernel dimension: {kernel_dim}")
            print(f"(Dimension of sl_3 perturbations that could drop catalecticant rank at first order)")

            # If kernel_dim = 0, no first-order perturbation can drop the rank.
            # This is a necessary condition for (1,7) feasibility.
            if kernel_dim == 0:
                print("\n*** RESULT: No first-order perturbation drops catalecticant rank ***")
                print("*** (1,7) cyclic rank-22 is FIRST-ORDER INFEASIBLE at the BILR (2,7) point ***")
            else:
                print(f"\n*** There are {kernel_dim} first-order directions that might drop rank ***")
                print("*** (1,7) feasibility needs further investigation ***")

    # ── Save results ──────────────────────────────────────────────────
    results = {
        'scheme': 'BILR S_{2fix-Z_3} (f,m)=(2,7)',
        'brent_errors': int(max_err),
        'residual_equals_sum_cubes': int(cube_match) == 0,
        'catalecticant_shape': list(Cat.shape),
        'catalecticant_ranks_mod_primes': cat_ranks,
        'annihilator_dimension': ann_dim,
        'cube_directions': [u.tolist() for u in cubes],
        'n_orbits': len(orbits),
    }

    # Koszul if computed
    if 'koszul_ranks' in dir():
        results['koszul_ranks_mod_primes'] = koszul_ranks

    out_path = OUT / 'bilr_27_analysis.json'
    out_path.write_text(json.dumps(results, indent=2) + '\n')
    print(f"\nSaved {out_path}")

if __name__ == '__main__':
    main()
