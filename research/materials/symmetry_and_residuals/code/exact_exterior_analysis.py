#!/usr/bin/env python3
"""
analysis: Find an EXACT rational rank-4 decomposition of omega in Lambda^3(sl_3).

Strategy: 
1. Use numerical TRF solution as starting point
2. Search over F_p for exact decomposition  
3. Rationalize using LLL or direct construction

Also: compute catalecticant bounds for residual cubics at m=4,5,6,7.
"""
from __future__ import annotations
import numpy as np, itertools, json, time
from pathlib import Path

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'exact_exterior'
OUT.mkdir(parents=True, exist_ok=True)

N = 8  # dim sl_3
TRIPLES = list(itertools.combinations(range(N), 3))
TRIPLE_IDX = {t: i for i, t in enumerate(TRIPLES)}
DIM3 = len(TRIPLES)  # 56

def idx(a, b):
    return 3*a + b

def build_omega_sl3_exact():
    """Build omega in Lambda^3(sl_3) as exact integer coefficients.
    
    sl_3 basis: b0=E01, b1=E02, b2=E10, b3=E12, b4=E20, b5=E21, b6=E00-E11, b7=E11-E22
    """
    # First build change of basis (exact integers)
    # B: 9x8 matrix, B[i,a] = coefficient of e_i in b_a
    B = [[0]*8 for _ in range(9)]
    B[1][0] = 1  # b0 = E_01 = e_1
    B[2][1] = 1  # b1 = E_02 = e_2
    B[3][2] = 1  # b2 = E_10 = e_3
    B[5][3] = 1  # b3 = E_12 = e_5
    B[6][4] = 1  # b4 = E_20 = e_6
    B[7][5] = 1  # b5 = E_21 = e_7
    B[0][6] = 1; B[4][6] = -1  # b6 = E_00 - E_11
    B[8][7] = -1; B[4][7] = 1  # b7 = E_11 - E_22
    
    # Build omega in gl_3 = K^9 coordinates
    omega_gl3 = {}
    for a, b, c in itertools.product(range(3), repeat=3):
        i, j, k = idx(a, b), idx(b, c), idx(c, a)
        trip = (i, j, k)
        if len(set(trip)) < 3:
            continue
        s = tuple(sorted(trip))
        perm = [s.index(x) for x in trip]
        inv = sum(1 for p in range(3) for q in range(p+1, 3) if perm[p] > perm[q])
        sign = (-1)**inv
        omega_gl3[s] = omega_gl3.get(s, 0) + sign
    omega_gl3 = {k: v for k, v in omega_gl3.items() if v}
    
    # Project to Lambda^3(sl_3) via Lambda^3(B^+)
    # Use numpy for the projection
    B_np = np.array(B, dtype=float)
    B_pinv = np.linalg.pinv(B_np)  # 8x9
    
    omega_vec = np.zeros(DIM3)
    triples9 = list(itertools.combinations(range(9), 3))
    idx9 = {t: i for i, t in enumerate(triples9)}
    
    for (i9, j9, k9), coef in omega_gl3.items():
        u = B_pinv[:, i9]
        v = B_pinv[:, j9]
        w = B_pinv[:, k9]
        for (a, b, c) in TRIPLES:
            det = (u[a]*(v[b]*w[c] - v[c]*w[b])
                 - u[b]*(v[a]*w[c] - v[c]*w[a])
                 + u[c]*(v[a]*w[b] - v[b]*w[a]))
            omega_vec[TRIPLE_IDX[(a,b,c)]] += coef * det
    
    # Round to integers (should be exact)
    omega_int = [int(round(x)) for x in omega_vec]
    err = max(abs(omega_vec[i] - omega_int[i]) for i in range(DIM3))
    print(f"omega integrality error: {err:.2e}")
    
    return omega_int, omega_vec, B_np, B_pinv

def wedge_product_fp(u, v, w, p):
    """Compute u ^ v ^ w in Lambda^3(F_p^8)."""
    result = [0]*DIM3
    for idx_t, (a, b, c) in enumerate(TRIPLES):
        det = (u[a]*(v[b]*w[c] - v[c]*w[b])
             - u[b]*(v[a]*w[c] - v[c]*w[a])
             + u[c]*(v[a]*w[b] - v[b]*w[a]))
        result[idx_t] = det % p
    return result

def search_rank4_fp(omega_fp, p, max_trials=10000):
    """Search for a rank-4 decomposition of omega over F_p by random trials."""
    import random
    rng = random.Random(42)
    
    # Grassmannian points as 3x8 matrices mod GL_3(F_p)
    # Reduced: 3-plane represented by its wedge product (a point in P(Lambda^3))
    
    # Build all decomposable 3-vectors as a catalog (too many for F_p)
    # Instead, try random triples
    
    for trial in range(max_trials):
        # Pick 3 random 3-planes
        planes = []
        wedges = []
        for _ in range(3):
            M = [[rng.randrange(p) for _ in range(8)] for _ in range(3)]
            u, v, w = M[0], M[1], M[2]
            wdg = wedge_product_fp(u, v, w, p)
            planes.append(M)
            wedges.append(wdg)
        
        # Residual: omega - sum of first 3 wedges
        residual = [(omega_fp[i] - sum(w[i] for w in wedges)) % p for i in range(DIM3)]
        
        # Check if residual is decomposable: rank of the 8x(C(8,2))=8x28 contraction matrix
        # A 3-form alpha is decomposable iff all contractions alpha(v, ., .) have rank <= 2
        # Equivalently, the contraction map V* -> Lambda^2 V has rank exactly 3
        contraction = [[0]*28 for _ in range(8)]
        pairs = list(itertools.combinations(range(8), 2))
        pair_idx = {p: i for i, p in enumerate(pairs)}
        
        for idx_t, (a, b, c) in enumerate(TRIPLES):
            val = residual[idx_t]
            if val == 0:
                continue
            # Contraction with e_a gives val * e_b ^ e_c
            contraction[a][pair_idx[(b,c)]] = (contraction[a][pair_idx[(b,c)]] + val) % p
            # Contraction with e_b gives -val * e_a ^ e_c
            bc_pair = tuple(sorted([a, c]))
            sign = 1 if a < c else -1
            contraction[b][pair_idx[bc_pair]] = (contraction[b][pair_idx[bc_pair]] + sign*val) % p
            # Contraction with e_c gives val * e_a ^ e_b
            ab_pair = tuple(sorted([a, b]))
            sign = 1 if a < b else -1
            contraction[c][pair_idx[ab_pair]] = (contraction[c][pair_idx[ab_pair]] + sign*val) % p
        
        # Compute rank mod p
        rank = rank_mod_p(contraction, p)
        
        if rank <= 3:
            if all(r == 0 for r in residual):
                print(f"Trial {trial}: residual is ZERO (rank <=3 decomposition!)")
            else:
                print(f"Trial {trial}: residual has contraction rank {rank} — DECOMPOSABLE!")
                return planes, residual
        
        if trial % 1000 == 999:
            print(f"Trial {trial}: no decomposable residual yet")
    
    return None, None

def rank_mod_p(mat, p):
    m = len(mat)
    if m == 0: return 0
    n = len(mat[0])
    A = [row[:] for row in mat]
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i][c] % p:
                piv = i; break
        if piv is None: continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c] % p, -1, p)
        A[r] = [(x * inv) % p for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] % p:
                f = A[i][c] % p
                A[i] = [(A[i][j] - f*A[r][j]) % p for j in range(n)]
        r += 1
        if r == min(m, n): break
    return r

def compute_catalecticant_for_cubic(cubic_coeffs, n=9):
    """
    Given a cubic form in n variables (as dict: sorted triple -> coefficient),
    compute its 1st catalecticant matrix (n x C(n+1,2) = n x C(n,2+1)).
    
    Cat_1: S^1(V*) -> S^2(V), defined by (l, f) -> l(f) partial derivative evaluation.
    For f = sum c_{ijk} x_i x_j x_k (with multiplicity),
    Cat_1[a, (b,c)] = d^3f / (dx_a dx_b dx_c) * normalization.
    """
    # Degree-2 monomials: (j,k) with j <= k
    deg2 = []
    for j in range(n):
        for k in range(j, n):
            deg2.append((j, k))
    d2_idx = {m: i for i, m in enumerate(deg2)}
    
    cat = np.zeros((n, len(deg2)))
    
    for (i, j, k), coef in cubic_coeffs.items():
        # The monomial x_i x_j x_k appears with this coefficient
        # Partial d/dx_a:
        for a_pos, a in enumerate([i, j, k]):
            rest = [x for p, x in enumerate([i, j, k]) if p != a_pos]
            bc = tuple(sorted(rest))
            cat[a, d2_idx[bc]] += coef
    
    return cat

def main():
    print("="*70)
    print("analysis: Exact exterior rank-4 and residual cubic analysis")
    print("="*70)
    
    omega_int, omega_float, B_np, B_pinv = build_omega_sl3_exact()
    
    nz = [(i, v) for i, v in enumerate(omega_int) if v != 0]
    print(f"\nomega in Lambda^3(sl_3): {len(nz)} nonzero terms")
    for i, v in nz:
        print(f"  b_{TRIPLES[i][0]} ^ b_{TRIPLES[i][1]} ^ b_{TRIPLES[i][2]}: {v}")
    
    # Search for rank-4 decomposition over F_p
    p = 65521
    omega_fp = [x % p for x in omega_int]
    
    print(f"\n--- Searching for rank-4 decomposition over F_{p} ---")
    planes, residual = search_rank4_fp(omega_fp, p, max_trials=5000)
    
    if planes is not None:
        print("Found decomposable residual!")
    else:
        print("No decomposable residual found in 5000 random trials over F_p")
        print("Trying optimization approach over R instead...")
    
    # Use the R-solution to compute residual cubic properties
    print(f"\n--- Residual cubic analysis from numerical decomposition ---")
    
    from scipy.optimize import least_squares
    
    def wedge_product(u, v, w):
        result = np.zeros(DIM3)
        for idx_t, (a, b, c) in enumerate(TRIPLES):
            det = (u[a]*(v[b]*w[c] - v[c]*w[b])
                 - u[b]*(v[a]*w[c] - v[c]*w[a])
                 + u[c]*(v[a]*w[b] - v[b]*w[a]))
            result[idx_t] = det
        return result
    
    def residual_func(x, omega):
        x = x.reshape(4, 3, N)
        total = np.zeros(DIM3)
        for j in range(4):
            total += wedge_product(x[j, 0], x[j, 1], x[j, 2])
        return omega - total
    
    # Find multiple rank-4 decompositions
    print("\nFinding multiple rank-4 decompositions...")
    decomps = []
    np.random.seed(0)
    for trial in range(100):
        x0 = np.random.randn(96) * 0.5
        result = least_squares(residual_func, x0, args=(omega_float,), method='trf',
                             max_nfev=5000, ftol=1e-15, xtol=1e-15, gtol=1e-15)
        if result.cost < 1e-20:
            decomps.append(result.x.reshape(4, 3, N))
    
    print(f"Found {len(decomps)} numerical rank-4 decompositions")
    
    # For each decomposition, compute the residual cubic and its catalecticant
    print("\n--- Catalecticant analysis of residual cubics ---")
    
    # tr(M^3) as a cubic in 9 variables (coefficients in the sorted-triple basis)
    from collections import defaultdict
    trM3 = defaultdict(int)
    for a in range(3):
        for b in range(3):
            for c in range(3):
                mono = tuple(sorted([3*a+b, 3*b+c, 3*c+a]))
                trM3[mono] += 1
    trM3 = dict(trM3)
    print(f"tr(M^3): {len(trM3)} monomial terms")
    
    # For each numerical decomposition, compute residual cubic
    cat_ranks = []
    for d_idx, decomp in enumerate(decomps[:20]):
        # The orbit contribution to tr(M^3) is:
        # 3 * sum_j ell_{u_j}(M) * ell_{v_j}(M) * ell_{w_j}(M)
        # where u_j, v_j, w_j are the gl_3-coordinate vectors
        
        # Convert sl_3 coordinates back to gl_3
        orbit_cubic = defaultdict(float)
        for j in range(4):
            u_sl, v_sl, w_sl = decomp[j, 0], decomp[j, 1], decomp[j, 2]
            # gl_3 vector: B @ sl_3_vec
            u_gl = B_np @ u_sl  # 9-vector
            v_gl = B_np @ v_sl
            w_gl = B_np @ w_sl
            
            for i1 in range(9):
                for i2 in range(9):
                    for i3 in range(9):
                        coef = u_gl[i1] * v_gl[i2] * w_gl[i3]
                        if abs(coef) > 1e-15:
                            mono = tuple(sorted([i1, i2, i3]))
                            orbit_cubic[mono] += 3.0 * coef  # factor of 3 for cyclic
        
        # Residual = tr(M^3) - orbit contribution
        residual_cubic = defaultdict(float)
        all_monos = set(trM3) | set(orbit_cubic)
        for mono in all_monos:
            val = trM3.get(mono, 0) - orbit_cubic.get(mono, 0)
            if abs(val) > 1e-10:
                residual_cubic[mono] = val
        
        # Compute catalecticant
        cat = compute_catalecticant_for_cubic(dict(residual_cubic))
        cat_rank = np.linalg.matrix_rank(cat, tol=1e-6)
        cat_ranks.append(cat_rank)
        
        if d_idx < 5:
            print(f"  Decomp {d_idx}: residual has {len(residual_cubic)} monomials, catalecticant rank = {cat_rank}")
    
    print(f"\nCatalecticant ranks across {len(cat_ranks)} decompositions: {sorted(set(cat_ranks))}")
    print(f"Minimum: {min(cat_ranks)}, Maximum: {max(cat_ranks)}")
    print(f"\nFor rank-22 with (f,m)=(10,4): need Waring rank <= 10")
    print(f"Catalecticant rank is a LOWER BOUND on Waring rank")
    print(f"If all catalecticant ranks >= 11, then no rank-4 decomposition")
    print(f"can give a residual of Waring rank <= 10")
    
    # Save results
    results = {
        'omega_nonzero': [(TRIPLES[i], v) for i, v in enumerate(omega_int) if v],
        'n_decompositions': len(decomps),
        'catalecticant_ranks': cat_ranks,
        'min_cat_rank': min(cat_ranks) if cat_ranks else None,
        'max_cat_rank': max(cat_ranks) if cat_ranks else None,
    }
    out = OUT / 'exact_exterior_analysis.json'
    out.write_text(json.dumps(results, indent=2, default=str) + '\n')
    print(f"\nSaved {out}")

if __name__ == '__main__':
    main()
