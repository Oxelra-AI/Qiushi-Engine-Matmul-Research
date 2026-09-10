#!/usr/bin/env python3
"""
analysis: Verify that the cyclic quotient trivector omega lives in Lambda^3(sl_3),
compute the GL_8 stabilizer dimension, verify prehomogeneity, and check sigma_3 dimension.

Key claims to verify:
1. omega ∈ Lambda^3(sl_3) ⊂ Lambda^3(K^9)  [ambient correction]
2. Lambda^3(C^8) is prehomogeneous under GL_8  [dense orbit]
3. dim sigma_3(G(3,8)) <= 48 < 56  [secant variety bound]
4. Therefore exterior rank of omega >= 4 over any char-zero field

The trivector omega is the alternating part of tr(ABC) on gl_3 = K^9.
"""
from __future__ import annotations
import numpy as np, itertools, json
from pathlib import Path

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'sl3_trivector'
OUT.mkdir(parents=True, exist_ok=True)

N = 9  # dim gl_3

def idx(a, b):
    return 3*a + b

# ======== Build omega in Lambda^3(K^9) ========

def build_omega_dict():
    """Build omega as dict: sorted 3-tuple -> coefficient."""
    terms = {}
    for a, b, c in itertools.product(range(3), repeat=3):
        i, j, k = idx(a, b), idx(b, c), idx(c, a)
        trip = (i, j, k)
        if len(set(trip)) < 3:
            continue
        s = tuple(sorted(trip))
        # sign of permutation trip -> s
        perm = [s.index(x) for x in trip]
        inv = sum(1 for p in range(3) for q in range(p+1, 3) if perm[p] > perm[q])
        sign = (-1)**inv
        terms[s] = terms.get(s, 0) + sign
    return {k: v for k, v in terms.items() if v}

# ======== Check 1: omega in Lambda^3(sl_3) ========

def check_sl3_membership(omega):
    """
    sl_3 = ker(tr) where tr = sum_i E_{ii}^*.
    If iota_tr(omega) = 0, then omega in Lambda^3(sl_3).
    
    Contraction: iota_{tr}(e_i ^ e_j ^ e_k) = 
      tr(e_i) * (e_j ^ e_k) - tr(e_j) * (e_i ^ e_k) + tr(e_k) * (e_i ^ e_j)
    where tr(e_p) = 1 if p is a diagonal index (0,4,8), else 0.
    """
    diag = {0, 4, 8}  # indices of E_00, E_11, E_22
    
    # Result is a bivector in Lambda^2(K^9)
    bivector = {}  # sorted pair -> coefficient
    
    for (i, j, k), coef in omega.items():
        # iota_tr on e_i ^ e_j ^ e_k (already sorted i<j<k)
        for pos, elem in enumerate([i, j, k]):
            if elem not in diag:
                continue
            # Remove element at position pos, get remaining pair
            remaining = [x for p, x in enumerate([i, j, k]) if p != pos]
            pair = tuple(sorted(remaining))
            # Sign: (-1)^pos for removing from position pos in sorted triple
            sign = (-1)**pos
            bivector[pair] = bivector.get(pair, 0) + coef * sign
    
    nonzero = {k: v for k, v in bivector.items() if v}
    return nonzero

def check_sl3_membership_v2(omega):
    """
    Alternative: express omega in the sl_3 basis.
    sl_3 has basis: {E_ij : i != j} union {E_00 - E_11, E_11 - E_22}
    i.e. 6 off-diagonal + 2 traceless diagonal = 8 basis vectors.
    
    Write omega using only wedge products of sl_3 basis vectors.
    If successful, omega ∈ Lambda^3(sl_3).
    """
    # sl_3 basis in terms of standard E_ij basis (9-dim gl_3):
    # b0 = E_01 = e_1
    # b1 = E_02 = e_2
    # b2 = E_10 = e_3
    # b3 = E_12 = e_5
    # b4 = E_20 = e_6
    # b5 = E_21 = e_7
    # b6 = E_00 - E_11 = e_0 - e_4
    # b7 = E_11 - E_22 = e_4 - e_8
    
    # Change of basis matrix from sl_3 basis to K^9 standard basis
    # B[i][j] = coefficient of e_i in b_j
    B = np.zeros((9, 8), dtype=float)
    B[1, 0] = 1  # b0 = e_1
    B[2, 1] = 1  # b1 = e_2
    B[3, 2] = 1  # b2 = e_3
    B[5, 3] = 1  # b3 = e_5
    B[6, 4] = 1  # b4 = e_6
    B[7, 5] = 1  # b5 = e_7
    B[0, 6] = 1; B[4, 6] = -1  # b6 = e_0 - e_4
    B[4, 7] = 1; B[8, 7] = -1  # b7 = e_4 - e_8
    
    return B

# ======== Check 2: GL_8 action and stabilizer ========

def gl8_stabilizer_dim(omega_sl3_coords, p=1000003):
    """
    Compute dim of stabilizer of omega under GL_8 action on Lambda^3(C^8).
    
    A ∈ gl_8 acts on Lambda^3(C^8) by:
    (A · omega)(v1,v2,v3) = omega(A^T v1, v2, v3) + omega(v1, A^T v2, v3) + omega(v1, v2, A^T v3)
    
    In coordinates: if omega = sum_{i<j<k} c_{ijk} e_i ^ e_j ^ e_k,
    then (A · omega)_{ijk} = sum_l [A_{li} c_{ljk} + A_{lj} c_{ilk} + A_{lk} c_{ijl}]
    (with appropriate signs for sorting).
    
    The stabilizer is ker of the map phi: gl_8 -> Lambda^3(C^8), A |-> A · omega.
    """
    n = 8
    triples = list(itertools.combinations(range(n), 3))
    triple_idx = {t: i for i, t in enumerate(triples)}
    dim3 = len(triples)  # C(8,3) = 56
    
    # Build the matrix of phi: gl_8 -> Lambda^3
    # phi has dim3 rows and n*n columns (one per entry of A)
    mat = [[0]*n*n for _ in range(dim3)]
    
    for (i, j, k), coef in omega_sl3_coords.items():
        if coef == 0:
            continue
        # A_{li} contributes to c_{ljk} -> sorted(l,j,k)
        for l in range(n):
            if l == j or l == k:
                continue
            trip = tuple(sorted([l, j, k]))
            # sign: (l,j,k) -> sorted
            perm_sign = _sort_sign([l, j, k])
            # Also need sign from original (i,j,k) -> replacing i with l
            # Original triple is sorted (i,j,k); we replace index i with l
            row = triple_idx[trip]
            col = l * n + i  # A_{l,i}
            mat[row][col] = (mat[row][col] + coef * perm_sign) % p
        
        # A_{lj} contributes to c_{ilk} -> sorted(i,l,k)
        for l in range(n):
            if l == i or l == k:
                continue
            trip = tuple(sorted([i, l, k]))
            perm_sign = _sort_sign([i, l, k])
            row = triple_idx[trip]
            col = l * n + j  # A_{l,j}
            mat[row][col] = (mat[row][col] + coef * perm_sign) % p
        
        # A_{lk} contributes to c_{ijl} -> sorted(i,j,l)
        for l in range(n):
            if l == i or l == j:
                continue
            trip = tuple(sorted([i, j, l]))
            perm_sign = _sort_sign([i, j, l])
            row = triple_idx[trip]
            col = l * n + k  # A_{l,k}
            mat[row][col] = (mat[row][col] + coef * perm_sign) % p
    
    # Rank of mat (mod p) gives dim(image) = dim(gl_8) - dim(stab)
    rank = rank_mod(mat, p)
    return n*n, rank, n*n - rank  # dim_gl8, rank_phi, dim_stab

def _sort_sign(lst):
    """Sign of permutation that sorts lst."""
    inv = 0
    for i in range(len(lst)):
        for j in range(i+1, len(lst)):
            if lst[i] > lst[j]:
                inv += 1
    return (-1)**inv

def rank_mod(mat, p):
    m = len(mat)
    n = len(mat[0]) if m else 0
    A = [row[:] for row in mat]
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c] % p, -1, p)
        A[r] = [(x * inv) % p for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] % p:
                f = A[i][c] % p
                A[i] = [(A[i][j] - f * A[r][j]) % p for j in range(n)]
        r += 1
        if r == m:
            break
    return r

# ======== Convert omega to sl_3 coordinates ========

def omega_in_sl3(omega_gl3, B):
    """
    Given omega in Lambda^3(K^9) and change-of-basis B: K^8 -> K^9,
    express omega in Lambda^3(K^8) coordinates.
    
    omega = sum c_{ijk} e_i ^ e_j ^ e_k (K^9 basis)
    B maps b_a -> sum_i B[i,a] e_i
    
    So b_a ^ b_b ^ b_c maps to sum_{i,j,k} B[i,a]B[j,b]B[k,c] e_i ^ e_j ^ e_k
    
    We need to invert: find d_{abc} such that
    omega = sum_{a<b<c} d_{abc} b_a ^ b_b ^ b_c
    """
    n9 = 9
    n8 = 8
    triples9 = list(itertools.combinations(range(n9), 3))
    triples8 = list(itertools.combinations(range(n8), 3))
    
    # Build Lambda^3(B): maps Lambda^3(K^8) -> Lambda^3(K^9)
    # Matrix of size C(9,3) x C(8,3)
    idx9 = {t: i for i, t in enumerate(triples9)}
    
    mat = np.zeros((len(triples9), len(triples8)))
    for j_col, (a, b, c) in enumerate(triples8):
        # b_a ^ b_b ^ b_c = sum_{i1,i2,i3} B[i1,a]B[i2,b]B[i3,c] e_{i1}^e_{i2}^e_{i3}
        for i1 in range(n9):
            for i2 in range(n9):
                for i3 in range(n9):
                    if i1 == i2 or i1 == i3 or i2 == i3:
                        continue
                    coef = B[i1, a] * B[i2, b] * B[i3, c]
                    if abs(coef) < 1e-15:
                        continue
                    trip = tuple(sorted([i1, i2, i3]))
                    sign = _sort_sign([i1, i2, i3])
                    mat[idx9[trip], j_col] += coef * sign
    
    # omega vector in Lambda^3(K^9)
    omega_vec = np.zeros(len(triples9))
    for (i, j, k), coef in omega_gl3.items():
        omega_vec[idx9[(i, j, k)]] = coef
    
    # Solve mat @ d = omega_vec (least squares)
    d, residual, rank_B, _ = np.linalg.lstsq(mat, omega_vec, rcond=None)
    
    # Check residual
    recon = mat @ d
    err = np.max(np.abs(recon - omega_vec))
    
    # Convert to dict
    omega_sl3 = {}
    for j_col, (a, b, c) in enumerate(triples8):
        if abs(d[j_col]) > 1e-10:
            omega_sl3[(a, b, c)] = round(d[j_col])
    
    return omega_sl3, err, rank_B

# ======== Check 3: sigma_3 dimension ========

def sigma3_dimension():
    """
    G(3,8) has dimension 3*(8-3) = 15.
    A point on sigma_3 is a triple of 3-planes plus three scalars,
    so expected dim = 3*15 + 3 - 1 = 47 (projectively), or 48 affinely.
    
    More precisely: dim sigma_3(G(3,8)) <= 3*dim(G(3,8)) + 2 = 47 (projective)
    = 48 (affine, as a cone).
    
    Lambda^3(C^8) has dimension C(8,3) = 56.
    So sigma_3 is proper if 48 < 56.
    """
    dim_G38 = 3 * (8 - 3)  # = 15
    # sigma_3 in projective space: <= 3*15 + 2 = 47
    # sigma_3 as affine cone: <= 48
    dim_ambient = 56  # C(8,3)
    return {
        'dim_G38': dim_G38,
        'sigma3_projective_upper': 3 * dim_G38 + 2,
        'sigma3_affine_upper': 3 * dim_G38 + 3,
        'dim_ambient': dim_ambient,
        'sigma3_proper': (3 * dim_G38 + 3) < dim_ambient
    }

# ======== Main ========

def main():
    print("=" * 70)
    print("analysis: Verifying omega in Lambda^3(sl_3) and prehomogeneity")
    print("=" * 70)
    
    # Build omega
    omega = build_omega_dict()
    print(f"\nomega in Lambda^3(K^9): {len(omega)} nonzero terms")
    for t, c in sorted(omega.items()):
        print(f"  e_{t[0]} ^ e_{t[1]} ^ e_{t[2]}: {c}")
    
    # Check 1: contraction with tr
    print("\n--- Check 1: iota_tr(omega) ---")
    bivec = check_sl3_membership(omega)
    print(f"iota_tr(omega) nonzero terms: {len(bivec)}")
    if bivec:
        for pair, c in sorted(bivec.items()):
            print(f"  e_{pair[0]} ^ e_{pair[1]}: {c}")
    else:
        print("  ALL ZERO => omega in Lambda^3(sl_3)")
    
    # Check 1b: express in sl_3 coordinates
    print("\n--- Check 1b: omega in sl_3 basis ---")
    B = check_sl3_membership_v2(omega)
    omega_sl3, err, rank_B = omega_in_sl3(omega, B)
    print(f"Change-of-basis rank: {rank_B}")
    print(f"Reconstruction error: {err:.2e}")
    print(f"omega in Lambda^3(sl_3): {len(omega_sl3)} nonzero terms")
    for t, c in sorted(omega_sl3.items()):
        print(f"  b_{t[0]} ^ b_{t[1]} ^ b_{t[2]}: {c}")
    
    # Check 2: GL_8 stabilizer
    print("\n--- Check 2: GL_8 stabilizer of omega ---")
    for p in [1000003, 65521, 32003]:
        dim_gl8, rank_phi, dim_stab = gl8_stabilizer_dim(omega_sl3, p)
        print(f"  mod {p}: dim(gl_8)={dim_gl8}, rank(phi)={rank_phi}, dim(stab)={dim_stab}")
    
    # ad(sl_3) should give dim_stab = 8
    print(f"\n  Expected: dim(stab) = dim(sl_3) = 8 (from ad action)")
    print(f"  Orbit dimension = {64} - {dim_stab} = {64 - dim_stab}")
    print(f"  Ambient dim Lambda^3(C^8) = 56")
    is_dense = (64 - dim_stab == 56)
    print(f"  Dense orbit: {is_dense}")
    
    # Check 3: sigma_3 dimension
    print("\n--- Check 3: sigma_3(G(3,8)) dimension ---")
    s3 = sigma3_dimension()
    for k, v in s3.items():
        print(f"  {k}: {v}")
    
    # Conclusion
    print("\n--- Conclusion ---")
    is_in_sl3 = (len(bivec) == 0 and err < 1e-10)
    print(f"omega in Lambda^3(sl_3): {is_in_sl3}")
    print(f"GL_8 orbit is dense: {is_dense}")
    print(f"sigma_3 is proper: {s3['sigma3_proper']}")
    if is_in_sl3 and is_dense and s3['sigma3_proper']:
        print("=> omega is in the dense orbit of Lambda^3(C^8)")
        print("=> omega is NOT in sigma_3(G(3,8))")
        print("=> exterior rank of omega >= 4 over any characteristic-zero field")
        print("=> cyclic rank-22 skeletons with m <= 3 are EXCLUDED over char-zero")
    
    results = {
        'omega_gl3_terms': {str(k): v for k, v in omega.items()},
        'omega_gl3_count': len(omega),
        'iota_tr_omega': {str(k): v for k, v in bivec.items()},
        'iota_tr_zero': len(bivec) == 0,
        'omega_sl3_terms': {str(k): v for k, v in omega_sl3.items()},
        'omega_sl3_count': len(omega_sl3),
        'reconstruction_error': err,
        'sl3_basis_change_rank': int(rank_B),
        'gl8_stabilizer': {
            'dim_gl8': 64,
            'rank_phi': int(rank_phi),
            'dim_stab': int(dim_stab),
            'orbit_dim': 64 - int(dim_stab),
            'ambient_dim': 56,
            'is_dense': is_dense
        },
        'sigma3': s3,
        'conclusion': {
            'omega_in_lambda3_sl3': is_in_sl3,
            'dense_orbit': is_dense,
            'sigma3_proper': s3['sigma3_proper'],
            'exterior_rank_ge_4': is_in_sl3 and is_dense and s3['sigma3_proper']
        }
    }
    
    out = OUT / 'sl3_trivector_verification.json'
    out.write_text(json.dumps(results, indent=2) + '\n')
    print(f"\nSaved {out}")

if __name__ == '__main__':
    main()
