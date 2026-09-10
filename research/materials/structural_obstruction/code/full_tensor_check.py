#!/usr/bin/env python3
"""
analysis: Verify whether the numerical 10+4 cyclic decomposition matches 
ALL 729 Brent equations, not just the 165 diagonal ones.

The diagonal specialization f(M) = tr(M^3) tests only the S_3-symmetrized 
tensor entries. For distinct indices i<j<k, it gives T[i,j,k]+T[i,k,j],
not the individual values. There are 84 untested anti-symmetric conditions.
"""
from __future__ import annotations
import numpy as np, itertools, json, time
from pathlib import Path
from scipy.optimize import least_squares

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'full_tensor_check'
OUT.mkdir(parents=True, exist_ok=True)

def idx(a, b):
    return 3*a + b

def build_T333():
    """Build T_{3,3,3} as 729-entry array."""
    T = np.zeros((9, 9, 9))
    for a in range(3):
        for b in range(3):
            for c in range(3):
                for d in range(3):
                    for e in range(3):
                        for f in range(3):
                            if b == c and d == e and f == a:
                                T[idx(a,b), idx(c,d), idx(e,f)] = 1
    return T

def build_B():
    """Change of basis sl_3 -> gl_3."""
    B = np.zeros((9, 8))
    B[1, 0] = 1; B[2, 1] = 1; B[3, 2] = 1
    B[5, 3] = 1; B[6, 4] = 1; B[7, 5] = 1
    B[0, 6] = 1; B[4, 6] = -1
    B[4, 7] = 1; B[8, 7] = -1
    return B

def build_trM3_as_cubic_vector():
    """Build tr(M^3) as a vector indexed by all 165 sorted triples with repetition."""
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
    result = np.zeros(len(monos))
    for cv in cube_vecs:
        for idx_m, mono in enumerate(monos):
            result[idx_m] += cv[mono[0]] * cv[mono[1]] * cv[mono[2]]
    return result

def cubic_from_orbits(orbit_triples_gl3, monos, mono_idx):
    """Evaluate 3 * sum_j l_Uj l_Vj l_Wj as cubic coefficients."""
    result = np.zeros(len(monos))
    for (u, v, w) in orbit_triples_gl3:
        for i in range(9):
            for j in range(9):
                for k in range(9):
                    val = 3.0 * u[i] * v[j] * w[k]
                    mono = tuple(sorted([i, j, k]))
                    result[mono_idx[mono]] += val
    return result

def reconstruct_full_tensor(cube_vecs_gl3, orbit_triples_gl3):
    """Reconstruct full 729-entry tensor from cyclic decomposition."""
    T = np.zeros((9, 9, 9))
    
    # Cube terms: u ⊗ u ⊗ u
    for cv in cube_vecs_gl3:
        for i in range(9):
            for j in range(9):
                for k in range(9):
                    T[i, j, k] += cv[i] * cv[j] * cv[k]
    
    # Orbit terms: (U⊗V⊗W) + (V⊗W⊗U) + (W⊗U⊗V)
    for (u, v, w) in orbit_triples_gl3:
        for i in range(9):
            for j in range(9):
                for k in range(9):
                    T[i, j, k] += u[i]*v[j]*w[k] + v[i]*w[j]*u[k] + w[i]*u[j]*v[k]
    
    return T

def main():
    T_target = build_T333()
    B = build_B()
    trM3, monos, mono_idx = build_trM3_as_cubic_vector()
    
    print("="*70)
    print("analysis: Full tensor verification of 10+4 cyclic decomposition")
    print("="*70)
    
    # Verify tr(M^3) construction
    T_flat = T_target.flatten()
    trM3_check = np.zeros(len(monos))
    for i in range(9):
        for j in range(9):
            for k in range(9):
                mono = tuple(sorted([i, j, k]))
                trM3_check[mono_idx[mono]] += T_target[i, j, k]
    
    err = np.max(np.abs(trM3 - trM3_check))
    print(f"tr(M^3) construction check: max err = {err:.2e}")
    
    # Joint optimization: 4 orbits (in sl_3) + n_cubes cubes (in gl_3)
    N_SL3 = 8
    N_GL3 = 9
    
    for n_cubes in [10, 11, 12]:
        n_orbits = 4
        n_params_orbit = n_orbits * 3 * N_SL3
        n_params_cube = n_cubes * N_GL3
        n_params = n_params_orbit + n_params_cube
        total_rank = n_cubes + 3 * n_orbits
        
        print(f"\n{'='*60}")
        print(f"Testing {n_cubes} cubes + {n_orbits} orbits = rank {total_rank}")
        print(f"{'='*60}")
        
        # Stage 1: Diagonal search (165 equations, fast)
        def diagonal_residual(x):
            orbit_params = x[:n_params_orbit].reshape(n_orbits, 3, N_SL3)
            cube_params = x[n_params_orbit:].reshape(n_cubes, N_GL3)
            
            orbit_gl3 = [(B @ orbit_params[j,0], B @ orbit_params[j,1], B @ orbit_params[j,2])
                        for j in range(n_orbits)]
            orbit_cubic = cubic_from_orbits(orbit_gl3, monos, mono_idx)
            cube_cubic = cubic_from_cubes(cube_params, monos, mono_idx)
            
            return trM3 - orbit_cubic - cube_cubic
        
        # Stage 2: Full tensor check (729 equations)
        def full_tensor_residual(x):
            orbit_params = x[:n_params_orbit].reshape(n_orbits, 3, N_SL3)
            cube_params = x[n_params_orbit:].reshape(n_cubes, N_GL3)
            
            orbit_gl3 = [(B @ orbit_params[j,0], B @ orbit_params[j,1], B @ orbit_params[j,2])
                        for j in range(n_orbits)]
            
            T_decomp = reconstruct_full_tensor(cube_params, orbit_gl3)
            return (T_decomp - T_target).flatten()
        
        np.random.seed(42)
        best_diag = float('inf')
        best_full = float('inf')
        best_x_diag = None
        n_trials = 100
        
        t0 = time.time()
        for trial in range(n_trials):
            x0 = np.random.randn(n_params) * 0.3
            
            # First try diagonal
            try:
                res_diag = least_squares(diagonal_residual, x0, method='trf',
                                        max_nfev=3000, ftol=1e-15, xtol=1e-15, gtol=1e-15)
                if res_diag.cost < best_diag:
                    best_diag = res_diag.cost
                    best_x_diag = res_diag.x
            except:
                pass
            
            if trial % 20 == 19:
                print(f"  Trial {trial}: diag best {best_diag:.2e} ({time.time()-t0:.1f}s)")
        
        print(f"\nDiagonal best: {best_diag:.2e}")
        
        if best_diag < 1e-15 and best_x_diag is not None:
            # Check full tensor for the best diagonal solution
            full_res = full_tensor_residual(best_x_diag)
            full_err = np.max(np.abs(full_res))
            full_cost = np.sum(full_res**2)
            n_errors = np.sum(np.abs(full_res) > 1e-6)
            print(f"Full tensor check: max err = {full_err:.2e}, cost = {full_cost:.2e}, entries > 1e-6: {n_errors}/729")
            
            if full_err > 1e-6:
                print("Diagonal matches but full tensor DOES NOT. The 84 anti-symmetric conditions fail.")
                
                # Now try optimizing the FULL tensor directly
                print("\nOptimizing full 729-entry tensor directly...")
                best_full = float('inf')
                for trial in range(50):
                    x0 = best_x_diag + np.random.randn(n_params) * 0.01
                    try:
                        res_full = least_squares(full_tensor_residual, x0, method='trf',
                                               max_nfev=5000, ftol=1e-15, xtol=1e-15, gtol=1e-15)
                        if res_full.cost < best_full:
                            best_full = res_full.cost
                            if res_full.cost < 1e-15:
                                print(f"  Full trial {trial}: cost={res_full.cost:.2e} — FULL MATCH!")
                                break
                    except:
                        pass
                    if trial % 10 == 9:
                        print(f"  Full trial {trial}: best {best_full:.2e}")
                
                print(f"Full tensor optimization best: {best_full:.2e}")
            else:
                print("BOTH diagonal and full tensor match! This IS a valid rank-{total_rank} decomposition!")
        
        result_key = f'rank_{total_rank}'
        print(f"\nSummary for rank {total_rank}: diag={best_diag:.2e}, full={best_full:.2e if best_full < float('inf') else 'N/A'}")
    
    # Save
    print(f"\nSaved results to {OUT}")

if __name__ == '__main__':
    main()
