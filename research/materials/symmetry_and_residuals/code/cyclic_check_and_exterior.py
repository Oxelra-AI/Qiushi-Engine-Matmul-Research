#!/usr/bin/env python3
"""
analysis: Check known rank-23 schemes for cyclic symmetry, extract exterior 
decomposition of omega, and compute the residual cubic / Waring rank.

The cyclic rotation rho acts on rank-one terms as:
  (u, v, w) -> (v, w, u)

A cyclic-invariant decomposition has:
  - fixed terms (cubes): u = v = w (up to scale)
  - free 3-orbits: {(u,v,w), (v,w,u), (w,u,v)}
"""
from __future__ import annotations
import numpy as np, itertools, json
from pathlib import Path

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'cyclic_exterior'
OUT.mkdir(parents=True, exist_ok=True)

def load_qmm(path):
    """Load QMM scheme file, return U, V, W as integer arrays."""
    terms = []
    with open(path) as f:
        lines = f.readlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if line.startswith('term'):
            u_line = lines[i+1].strip().split()[1:]
            v_line = lines[i+2].strip().split()[1:]
            w_line = lines[i+3].strip().split()[1:]
            u = [int(x) for x in u_line]
            v = [int(x) for x in v_line]
            w = [int(x) for x in w_line]
            terms.append((u, v, w))
            i += 4
        else:
            i += 1
    U = np.array([t[0] for t in terms])
    V = np.array([t[1] for t in terms])
    W = np.array([t[2] for t in terms])
    return U, V, W

def check_cyclic(U, V, W):
    """Check if the decomposition has cyclic symmetry."""
    R = U.shape[0]
    
    # For each term k, find k' such that (U[k'],V[k'],W[k']) is proportional to (V[k],W[k],U[k])
    # Allow scalar multiple: all three factors scaled by same constant
    matches = {}
    for k in range(R):
        target_u, target_v, target_w = V[k], W[k], U[k]
        for k2 in range(R):
            # Check if U[k2] = alpha * target_u, V[k2] = alpha * target_v, W[k2] = alpha * target_w
            # for some nonzero alpha
            scale = None
            match = True
            for vec_src, vec_tgt in [(U[k2], target_u), (V[k2], target_v), (W[k2], target_w)]:
                for i in range(9):
                    if abs(vec_tgt[i]) > 0.5:
                        s = vec_src[i] / vec_tgt[i]
                        if scale is None:
                            scale = s
                        elif abs(s - scale) > 1e-10:
                            match = False
                            break
                    elif abs(vec_src[i]) > 0.5:
                        match = False
                        break
                if not match:
                    break
            if match and scale is not None:
                matches[k] = (k2, scale)
                break
    
    return matches

def find_orbits(matches, R):
    """From cyclic matches, find fixed points and 3-orbits."""
    visited = set()
    cubes = []
    orbits = []
    
    for k in range(R):
        if k in visited:
            continue
        orbit = [k]
        visited.add(k)
        nxt = matches[k][0]
        while nxt not in visited:
            orbit.append(nxt)
            visited.add(nxt)
            nxt = matches[nxt][0]
        if len(orbit) == 1:
            cubes.append(k)
        elif len(orbit) == 3:
            orbits.append(orbit)
        else:
            print(f"WARNING: orbit of length {len(orbit)}: {orbit}")
    
    return cubes, orbits

def idx(a, b):
    return 3*a + b

def build_T333_flat():
    """Build the flattened T_{3,3,3} tensor as 81-vector."""
    T = np.zeros(81)
    for a in range(3):
        for b in range(3):
            for c in range(3):
                for d in range(3):
                    for e in range(3):
                        for f in range(3):
                            # T_{(a,b),(c,d),(e,f)} = delta_{bc} * delta_{de} * delta_{fa}
                            if b == c and d == e and f == a:
                                # UV index: idx(a,b)*9 + idx(c,d) = (3a+b)*9 + (3c+d)
                                uv_idx = idx(a,b)*9 + idx(c,d)
                                T[uv_idx] = 1
    return T

def project_to_exterior(U_vec, V_vec, W_vec, B_inv):
    """
    Project a 3-orbit's representative (U,V,W) -> U wedge V wedge W in Lambda^3(sl_3).
    
    First project U,V,W to sl_3 coordinates, then compute the wedge product.
    B_inv: left inverse of change-of-basis matrix B (from sl_3 to gl_3).
    """
    # Project to sl_3 coordinates
    u_sl = B_inv @ U_vec
    v_sl = B_inv @ V_vec
    w_sl = B_inv @ W_vec
    
    # Compute u ^ v ^ w in Lambda^3(C^8)
    result = {}
    triples = list(itertools.combinations(range(8), 3))
    for (i, j, k) in triples:
        # Determinant of 3x3 matrix [u_sl; v_sl; w_sl] restricted to columns i,j,k
        det = (u_sl[i] * (v_sl[j]*w_sl[k] - v_sl[k]*w_sl[j])
             - u_sl[j] * (v_sl[i]*w_sl[k] - v_sl[k]*w_sl[i])
             + u_sl[k] * (v_sl[i]*w_sl[j] - v_sl[j]*w_sl[i]))
        if abs(det) > 1e-10:
            result[(i,j,k)] = det
    
    return result, u_sl, v_sl, w_sl

def build_sl3_basis():
    """
    sl_3 basis in terms of standard gl_3 = K^9 basis:
    b0 = E_01 = e_1
    b1 = E_02 = e_2
    b2 = E_10 = e_3
    b3 = E_12 = e_5
    b4 = E_20 = e_6
    b5 = E_21 = e_7
    b6 = E_00 - E_11 = e_0 - e_4
    b7 = E_11 - E_22 = e_4 - e_8
    """
    B = np.zeros((9, 8))
    B[1, 0] = 1  # b0 = E_01
    B[2, 1] = 1  # b1 = E_02
    B[3, 2] = 1  # b2 = E_10
    B[5, 3] = 1  # b3 = E_12
    B[6, 4] = 1  # b4 = E_20
    B[7, 5] = 1  # b5 = E_21
    B[0, 6] = 1; B[4, 6] = -1  # b6 = E_00 - E_11
    B[4, 7] = 1; B[8, 7] = -1  # b7 = E_11 - E_22
    return B

def compute_residual_cubic(U, V, W, cubes, orbits):
    """
    The residual cubic is:
    tr(M^3) - sum_{j in orbits} ell_Uj(M) * ell_Vj(M) * ell_Wj(M)
    
    where ell_X(M) = sum_i X_i * m_i is the linear form determined by X in gl_3.
    
    Returns the cubic as ANF coefficients.
    """
    # tr(M^3) = sum_{a,b,c} m_{ab} * m_{bc} * m_{ca}
    # As a polynomial in m_0,...,m_8 (row-major), this is:
    # sum_{a,b,c in [0,2]} m_{3a+b} * m_{3b+c} * m_{3c+a}
    
    # Build tr(M^3) symbolically using a degree-3 monomial dict
    from collections import defaultdict
    
    trM3 = defaultdict(float)
    for a in range(3):
        for b in range(3):
            for c in range(3):
                mono = tuple(sorted([3*a+b, 3*b+c, 3*c+a]))
                trM3[mono] += 1.0
    
    # Build orbit sum: sum_j ell_Uj * ell_Vj * ell_Wj
    orbit_sum = defaultdict(float)
    for orb in orbits:
        k = orb[0]  # representative
        u, v, w = U[k].astype(float), V[k].astype(float), W[k].astype(float)
        for i in range(9):
            for j in range(9):
                for l in range(9):
                    coef = u[i] * v[j] * w[l]
                    if abs(coef) > 1e-15:
                        mono = tuple(sorted([i, j, l]))
                        orbit_sum[mono] += coef
    
    # Build cube sum: sum_j ell_Xj^3
    cube_sum = defaultdict(float)
    for k in cubes:
        x = U[k].astype(float)  # cube: U=V=W=x
        for i in range(9):
            for j in range(9):
                for l in range(9):
                    coef = x[i] * x[j] * x[l]
                    if abs(coef) > 1e-15:
                        mono = tuple(sorted([i, j, l]))
                        cube_sum[mono] += coef
    
    # Residual = trM3 - orbit_sum - cube_sum
    residual = defaultdict(float)
    all_monos = set(trM3) | set(orbit_sum) | set(cube_sum)
    for mono in all_monos:
        val = trM3[mono] - orbit_sum[mono] - cube_sum[mono]
        if abs(val) > 1e-10:
            residual[mono] = val
    
    return dict(trM3), dict(orbit_sum), dict(cube_sum), dict(residual)

def compute_catalecticant(cubic_dict):
    """
    Compute the 1st catalecticant of a cubic in 9 variables.
    Cat_1: S^1 -> S^2, where [Cat_1]_{i, (j,k)} = coefficient of x_i x_j x_k in f.
    
    Rows: 9 (degree-1 monomials x_0,...,x_8)
    Columns: C(9+1,2) = 45 (degree-2 monomials x_j x_k, j<=k)
    """
    # Build degree-2 monomial index
    deg2_monos = []
    for j in range(9):
        for k in range(j, 9):
            deg2_monos.append((j, k))
    deg2_idx = {m: i for i, m in enumerate(deg2_monos)}
    
    cat = np.zeros((9, len(deg2_monos)))
    
    for mono, coef in cubic_dict.items():
        # mono is sorted triple (i,j,k)
        # The coefficient of x_a x_b x_c in the cubic is:
        # coef / (multiplicity in the monomial)
        # Actually, we need to be more careful about symmetric cubics.
        # f = sum_{i<=j<=k} c_{ijk} x_i x_j x_k * mult(i,j,k)
        # where mult counts permutations.
        # The partial derivative d/dx_a of x_i x_j x_k is:
        # count of a in {i,j,k} * product of remaining
        
        i, j, k = mono
        # All permutations of the monomial
        for a, (b, c) in [(i, (j, k)), (j, (i, k)), (k, (i, j))]:
            bc = tuple(sorted([b, c]))
            cat[a, deg2_idx[bc]] += coef
    
    return cat

def main():
    print("=" * 70)
    print("analysis: Cyclic check and exterior decomposition extraction")
    print("=" * 70)
    
    # Load all three rank-23 schemes
    schemes = {
        'cn122': WS / 'data' / 'cn122_r23_reproduce' / 'scheme.qmm',
        'serendipitous': WS / 'data' / 'fmm_r23_schemes' / 'serendipitous_8d34.qmm',
        'naive': WS / 'data' / 'fmm_r23_schemes' / 'naive_c88.qmm',
    }
    
    results = {}
    
    for name, path in schemes.items():
        print(f"\n{'='*60}")
        print(f"Checking {name}")
        print(f"{'='*60}")
        
        U, V, W = load_qmm(path)
        R = U.shape[0]
        print(f"  Rank: {R}")
        
        matches = check_cyclic(U, V, W)
        n_matched = len(matches)
        print(f"  Cyclic matches: {n_matched}/{R}")
        
        if n_matched == R:
            cubes, orbits = find_orbits(matches, R)
            f, m = len(cubes), len(orbits)
            print(f"  CYCLIC! (f,m) = ({f},{m}), f+3m = {f+3*m}")
            
            # Extract exterior decomposition
            B = build_sl3_basis()
            B_pinv = np.linalg.pinv(B)  # 8x9 pseudo-inverse
            
            print(f"\n  Exterior decomposition in Lambda^3(sl_3):")
            ext_decomp = []
            for j, orb in enumerate(orbits):
                k = orb[0]
                wdg, u_sl, v_sl, w_sl = project_to_exterior(
                    U[k].astype(float), V[k].astype(float), W[k].astype(float), B_pinv)
                ext_decomp.append({
                    'orbit_indices': orb,
                    'representative_k': k,
                    'u_sl3': u_sl.tolist(),
                    'v_sl3': v_sl.tolist(),
                    'w_sl3': w_sl.tolist(),
                    'wedge_terms': len(wdg),
                })
                print(f"    Orbit {j}: terms {orb}, wedge has {len(wdg)} nonzero components")
            
            # Verify: sum of wedge products should equal omega
            # First build omega in sl_3 coordinates
            from scripts.sl3_trivector import build_omega_dict, omega_in_sl3
            omega_gl3 = build_omega_dict()
            omega_sl3, err, _ = omega_in_sl3(omega_gl3, B)
            
            # Build sum of wedge products
            wedge_sum = {}
            for j, orb in enumerate(orbits):
                k = orb[0]
                wdg, _, _, _ = project_to_exterior(
                    U[k].astype(float), V[k].astype(float), W[k].astype(float), B_pinv)
                for trip, val in wdg.items():
                    wedge_sum[trip] = wedge_sum.get(trip, 0) + val
            
            # Compare
            all_trips = set(omega_sl3) | set(wedge_sum)
            max_diff = 0
            for trip in all_trips:
                diff = abs(omega_sl3.get(trip, 0) - wedge_sum.get(trip, 0))
                max_diff = max(max_diff, diff)
            
            print(f"\n  Exterior decomposition verification:")
            print(f"    omega has {len(omega_sl3)} nonzero terms")
            print(f"    wedge sum has {len(wedge_sum)} nonzero terms")
            print(f"    max difference: {max_diff:.2e}")
            print(f"    MATCH: {max_diff < 1e-8}")
            
            # Compute residual cubic
            trM3, orb_sum, cube_sum, residual = compute_residual_cubic(U, V, W, cubes, orbits)
            print(f"\n  Residual cubic analysis:")
            print(f"    tr(M^3): {len(trM3)} monomial terms")
            print(f"    orbit sum: {len(orb_sum)} monomial terms")
            print(f"    cube sum: {len(cube_sum)} monomial terms")
            print(f"    residual: {len(residual)} monomial terms")
            
            # Compute catalecticant rank
            cat = compute_catalecticant(residual)
            cat_rank = np.linalg.matrix_rank(cat, tol=1e-6)
            print(f"    catalecticant shape: {cat.shape}")
            print(f"    catalecticant rank: {cat_rank}")
            print(f"    => Waring rank >= {cat_rank}")
            print(f"    => residual has {cat_rank} essential variables")
            
            results[name] = {
                'cyclic': True,
                'f': f, 'm': m,
                'exterior_match': max_diff < 1e-8,
                'exterior_max_diff': float(max_diff),
                'residual_monomial_count': len(residual),
                'catalecticant_rank': int(cat_rank),
                'cubes_indices': cubes,
                'orbit_indices': [orb for orb in orbits],
            }
        else:
            results[name] = {'cyclic': False, 'matches': n_matched}
    
    out = OUT / 'cyclic_exterior_results.json'
    out.write_text(json.dumps(results, indent=2) + '\n')
    print(f"\nSaved {out}")

if __name__ == '__main__':
    main()
