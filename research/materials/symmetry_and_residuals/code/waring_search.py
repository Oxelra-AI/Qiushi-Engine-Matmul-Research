#!/usr/bin/env python3
"""
analysis: Direct search for rank-22 cyclic decomposition via Waring rank.

The cyclic rank-22 question reduces to:
  tr(M^3) = sum_{i=1}^{10} l_i(M)^3 + 3 sum_{j=1}^4 l_{Uj}(M) l_{Vj}(M) l_{Wj}(M)

where sum_j U_j ^ V_j ^ W_j = omega in Lambda^3(sl_3).

Strategy: jointly optimize the 4 orbit triples (in sl_3) and 10 cube vectors (in K^9)
to minimize ||tr(M^3) - (cubes + orbit)||^2.

The residual is evaluated on all 729 degree-3 monomials of tr(M^3).
"""
from __future__ import annotations
import numpy as np, itertools, json, time
from pathlib import Path
from scipy.optimize import least_squares

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'waring_search'
OUT.mkdir(parents=True, exist_ok=True)

N_SL3 = 8
N_GL3 = 9

def build_B():
    """Change of basis sl_3 -> gl_3."""
    B = np.zeros((9, 8))
    B[1, 0] = 1; B[2, 1] = 1; B[3, 2] = 1
    B[5, 3] = 1; B[6, 4] = 1; B[7, 5] = 1
    B[0, 6] = 1; B[4, 6] = -1
    B[4, 7] = 1; B[8, 7] = -1
    return B

def build_trM3_coeffs():
    """Build tr(M^3) coefficients as a vector indexed by sorted triples."""
    monos = list(itertools.combinations_with_replacement(range(9), 3))
    mono_idx = {m: i for i, m in enumerate(monos)}
    
    coeffs = np.zeros(len(monos))
    for a in range(3):
        for b in range(3):
            for c in range(3):
                triple = tuple(sorted([3*a+b, 3*b+c, 3*c+a]))
                coeffs[mono_idx[triple]] += 1.0
    
    return coeffs, monos, mono_idx

def cubic_from_cubes(cube_vecs, monos, mono_idx):
    """Evaluate sum_i l_i^3 on monomial basis."""
    result = np.zeros(len(monos))
    for cv in cube_vecs:
        for idx, mono in enumerate(monos):
            result[idx] += cv[mono[0]] * cv[mono[1]] * cv[mono[2]]
    return result

def cubic_from_orbits(orbit_triples, B, monos, mono_idx):
    """Evaluate 3 * sum_j l_Uj l_Vj l_Wj on monomial basis.
    
    orbit_triples: list of (u_sl, v_sl, w_sl) in sl_3 coordinates.
    B: change of basis sl_3 -> gl_3.
    """
    result = np.zeros(len(monos))
    for (u_sl, v_sl, w_sl) in orbit_triples:
        u = B @ u_sl  # gl_3 coordinates
        v = B @ v_sl
        w = B @ w_sl
        for idx, (i, j, k) in enumerate(monos):
            # l_U * l_V * l_W evaluated at monomial x_i x_j x_k
            # = sum over permutations of (i,j,k) / multiplicity
            # For sorted triple (i,j,k):
            val = 0
            for p, q, r in set(itertools.permutations([i, j, k])):
                val += u[p] * v[q] * w[r]
            val /= len(set(itertools.permutations([i, j, k])))
            # Factor of 3 for cyclic symmetry
            result[idx] += 3.0 * val * len(set(itertools.permutations([i, j, k])))
    
    # Actually, let me redo this more carefully
    result = np.zeros(len(monos))
    for (u_sl, v_sl, w_sl) in orbit_triples:
        u = B @ u_sl
        v = B @ v_sl
        w = B @ w_sl
        for i in range(9):
            for j in range(9):
                for k in range(9):
                    val = 3.0 * u[i] * v[j] * w[k]
                    mono = tuple(sorted([i, j, k]))
                    result[mono_idx[mono]] += val
    return result

def main():
    B = build_B()
    trM3, monos, mono_idx = build_trM3_coeffs()
    n_monos = len(monos)
    
    print(f"Monomials: {n_monos} (degree-3 in 9 variables)")
    print(f"tr(M^3) nonzero: {np.sum(np.abs(trM3) > 1e-10)}")
    
    # Parameters: 4 orbit triples (4 * 3 * 8 = 96 sl_3 params)
    #             10 cube vectors (10 * 9 = 90 gl_3 params)
    # Total: 186 parameters, 165 equations (= n_monos)
    
    n_orbits = 4
    n_cubes_target = 10
    n_params_orbit = n_orbits * 3 * N_SL3  # 96
    n_params_cube = n_cubes_target * N_GL3  # 90
    n_params = n_params_orbit + n_params_cube  # 186
    
    def residual(x):
        orbit_params = x[:n_params_orbit].reshape(n_orbits, 3, N_SL3)
        cube_params = x[n_params_orbit:].reshape(n_cubes_target, N_GL3)
        
        # Orbit contribution
        orbit_triples = [(orbit_params[j, 0], orbit_params[j, 1], orbit_params[j, 2])
                        for j in range(n_orbits)]
        orbit_cubic = cubic_from_orbits(orbit_triples, B, monos, mono_idx)
        
        # Cube contribution
        cube_cubic = cubic_from_cubes(cube_params, monos, mono_idx)
        
        return trM3 - orbit_cubic - cube_cubic
    
    print(f"\n--- Joint search: 4 orbits + 10 cubes = rank 22 ---")
    best_cost = float('inf')
    best_x = None
    
    np.random.seed(42)
    t0 = time.time()
    n_trials = 500
    
    for trial in range(n_trials):
        x0 = np.random.randn(n_params) * 0.3
        try:
            result = least_squares(residual, x0, method='trf',
                                 max_nfev=3000, ftol=1e-15, xtol=1e-15, gtol=1e-15)
            if result.cost < best_cost:
                best_cost = result.cost
                best_x = result.x
                if result.cost < 1e-20:
                    print(f"  Trial {trial}: cost={result.cost:.2e} — EXACT RANK-22 CYCLIC!")
                    break
        except Exception:
            pass
        
        if trial % 50 == 49:
            print(f"  Trial {trial}: best cost {best_cost:.2e} ({time.time()-t0:.1f}s)")
    
    elapsed = time.time() - t0
    print(f"\nBest cost: {best_cost:.2e} after {trial+1} trials ({elapsed:.1f}s)")
    
    # Also try: fixed known rank-4 exterior + free 10 cubes
    print(f"\n--- Fixed exterior + free cubes search ---")
    
    # First find a rank-4 exterior decomposition
    from exterior_rank4_search import build_omega_sl3, wedge_product, DIM3, TRIPLES as TRIPLES8
    omega = build_omega_sl3()
    
    def ext_residual(x):
        x = x.reshape(4, 3, N_SL3)
        total = np.zeros(DIM3)
        for j in range(4):
            total += wedge_product(x[j,0], x[j,1], x[j,2])
        return omega - total
    
    # Find a good exterior decomposition first
    ext_x0 = np.random.randn(96) * 0.5
    ext_result = least_squares(ext_residual, ext_x0, method='trf',
                               max_nfev=5000, ftol=1e-15, xtol=1e-15, gtol=1e-15)
    print(f"Exterior decomp cost: {ext_result.cost:.2e}")
    
    if ext_result.cost < 1e-20:
        orbit_params_fixed = ext_result.x.reshape(4, 3, N_SL3)
        
        # Compute the orbit cubic contribution  
        orbit_triples = [(orbit_params_fixed[j, 0], orbit_params_fixed[j, 1], orbit_params_fixed[j, 2])
                        for j in range(4)]
        orbit_cubic_fixed = cubic_from_orbits(orbit_triples, B, monos, mono_idx)
        
        # Residual to match with cubes
        target_for_cubes = trM3 - orbit_cubic_fixed
        target_norm = np.linalg.norm(target_for_cubes)
        print(f"Residual cubic norm (to be matched by 10 cubes): {target_norm:.4f}")
        
        # Now search for 10 cubes matching this residual
        def cube_residual(x):
            cube_params = x.reshape(n_cubes_target, N_GL3)
            return target_for_cubes - cubic_from_cubes(cube_params, monos, mono_idx)
        
        best_cube_cost = float('inf')
        for trial in range(200):
            x0 = np.random.randn(n_cubes_target * N_GL3) * 0.3
            try:
                result = least_squares(cube_residual, x0, method='trf',
                                     max_nfev=3000, ftol=1e-15, xtol=1e-15, gtol=1e-15)
                if result.cost < best_cube_cost:
                    best_cube_cost = result.cost
                    if result.cost < 1e-20:
                        print(f"  Cube trial {trial}: cost={result.cost:.2e} — WARING RANK <= 10!")
                        break
            except:
                pass
            if trial % 50 == 49:
                print(f"  Cube trial {trial}: best {best_cube_cost:.2e}")
        
        print(f"Best cube cost: {best_cube_cost:.2e}")
        
        # Also try with 11 cubes (rank 23)
        print(f"\n--- Same exterior + 11 cubes (rank 23 test) ---")
        n_cubes_23 = 11
        def cube_residual_11(x):
            cube_params = x.reshape(n_cubes_23, N_GL3)
            return target_for_cubes - cubic_from_cubes(cube_params, monos, mono_idx)
        
        best_11 = float('inf')
        for trial in range(200):
            x0 = np.random.randn(n_cubes_23 * N_GL3) * 0.3
            try:
                result = least_squares(cube_residual_11, x0, method='trf',
                                     max_nfev=3000, ftol=1e-15, xtol=1e-15, gtol=1e-15)
                if result.cost < best_11:
                    best_11 = result.cost
                    if result.cost < 1e-20:
                        print(f"  11-cube trial {trial}: cost={result.cost:.2e} — Waring rank <= 11!")
                        break
            except:
                pass
            if trial % 50 == 49:
                print(f"  11-cube trial {trial}: best {best_11:.2e}")
        
        print(f"Best 11-cube cost: {best_11:.2e}")
    
    # Save results
    results = {
        'joint_186_best_cost': float(best_cost),
        'n_trials_joint': n_trials,
        'elapsed_sec': elapsed,
        'rank_22_found': best_cost < 1e-10,
    }
    
    out = OUT / 'waring_search_results.json'
    out.write_text(json.dumps(results, indent=2) + '\n')
    print(f"\nSaved {out}")

if __name__ == '__main__':
    main()
