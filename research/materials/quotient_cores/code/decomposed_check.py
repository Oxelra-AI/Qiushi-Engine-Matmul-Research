#!/usr/bin/env python3
"""
analysis: Decomposed cyclic rank-22 feasibility test.

KEY INSIGHT: For a cyclic decomposition, the anti-symmetric part of the tensor
  A[i,j,k] := T[i,j,k] - T[i,k,j]
depends ONLY on the orbit parameters (not the cubes, which are symmetric).

So the problem decomposes:
  Phase 1: Find 4 orbits in sl_3 matching the 84 anti-symmetric conditions
            AND the 56 exterior conditions (140 equations, 96 unknowns)
  Phase 2: Given orbits, find 10 cubes matching the 81 symmetric conditions
            (165 equations minus 84 already handled, in 90 unknowns)

If Phase 1 has no solution: rank-22 cyclic is IMPOSSIBLE at m=4.
"""
from __future__ import annotations
import numpy as np, itertools, json, time
from pathlib import Path
from scipy.optimize import least_squares

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'decomposed'
OUT.mkdir(parents=True, exist_ok=True)

def build_T333():
    T = np.zeros((9,9,9))
    for a in range(3):
        for b in range(3):
            for c in range(3):
                for d in range(3):
                    for e in range(3):
                        for f in range(3):
                            if b==c and d==e and f==a:
                                T[3*a+b,3*c+d,3*e+f] = 1
    return T

def build_B():
    B = np.zeros((9,8))
    B[1,0]=1; B[2,1]=1; B[3,2]=1; B[5,3]=1; B[6,4]=1; B[7,5]=1
    B[0,6]=1; B[4,6]=-1; B[4,7]=1; B[8,7]=-1
    return B

def build_omega_sl3():
    """Build omega in Lambda^3(sl_3) as float vector."""
    B = build_B()
    B_pinv = np.linalg.pinv(B)
    
    omega_gl3 = {}
    for a, b, c in itertools.product(range(3), repeat=3):
        i, j, k = 3*a+b, 3*b+c, 3*c+a
        trip = (i, j, k)
        if len(set(trip)) < 3: continue
        s = tuple(sorted(trip))
        perm = [s.index(x) for x in trip]
        inv = sum(1 for p in range(3) for q in range(p+1,3) if perm[p] > perm[q])
        sign = (-1)**inv
        omega_gl3[s] = omega_gl3.get(s, 0) + sign
    omega_gl3 = {k: v for k, v in omega_gl3.items() if v}
    
    TRIPLES8 = list(itertools.combinations(range(8), 3))
    omega_vec = np.zeros(len(TRIPLES8))
    for (i9, j9, k9), coef in omega_gl3.items():
        u = B_pinv[:, i9]; v = B_pinv[:, j9]; w = B_pinv[:, k9]
        for idx_t, (a, b, c) in enumerate(TRIPLES8):
            det = (u[a]*(v[b]*w[c]-v[c]*w[b]) - u[b]*(v[a]*w[c]-v[c]*w[a]) + u[c]*(v[a]*w[b]-v[b]*w[a]))
            omega_vec[idx_t] += coef * det
    
    return omega_vec, TRIPLES8

def build_antisymmetric_pairs(T):
    """Build the 84 anti-symmetric conditions: pairs of cyclic orbits with distinct indices."""
    pairs = []
    for i in range(9):
        for j in range(i+1, 9):
            for k in range(j+1, 9):
                # The condition is: T[i,j,k] - T[i,k,j] must match
                target = T[i,j,k] - T[i,k,j]
                pairs.append(((i,j,k), (i,k,j), target))
    return pairs

def main():
    T = build_T333()
    B = build_B()
    omega, TRIPLES8 = build_omega_sl3()
    asym_pairs = build_antisymmetric_pairs(T)
    
    print(f"Anti-symmetric pairs: {len(asym_pairs)}")
    print(f"Exterior equations: {len(TRIPLES8)}")
    print(f"Orbit parameters: 4 × 3 × 8 = 96")
    
    # Count nonzero anti-symmetric targets
    nz_asym = sum(1 for _, _, t in asym_pairs if abs(t) > 0.5)
    print(f"Nonzero anti-symmetric targets: {nz_asym}/84")
    
    # Anti-symmetric contribution from orbits:
    # A_decomp[i,j,k] = sum_s [U[i](V[j]W[k]-V[k]W[j]) + V[i](W[j]U[k]-W[k]U[j]) + W[i](U[j]V[k]-U[k]V[j])]
    
    def orbit_antisym(x_orb):
        """Compute anti-symmetric residual for 4 orbits."""
        orb = x_orb.reshape(4, 3, 8)
        residual = np.zeros(84)
        
        for idx, ((i,j,k), (i2,k2,j2), target) in enumerate(asym_pairs):
            val = 0.0
            for s in range(4):
                U = B @ orb[s, 0]
                V = B @ orb[s, 1]
                W = B @ orb[s, 2]
                # T_decomp[i,j,k] - T_decomp[i,k,j]
                # = (U[i]V[j]W[k] + V[i]W[j]U[k] + W[i]U[j]V[k])
                # - (U[i]V[k]W[j] + V[i]W[k]U[j] + W[i]U[k]V[j])
                val += (U[i]*V[j]*W[k] + V[i]*W[j]*U[k] + W[i]*U[j]*V[k]
                      - U[i]*V[k]*W[j] - V[i]*W[k]*U[j] - W[i]*U[k]*V[j])
            residual[idx] = val - target
        
        return residual
    
    def orbit_exterior(x_orb):
        """Compute exterior residual for 4 orbits."""
        orb = x_orb.reshape(4, 3, 8)
        residual = np.zeros(len(TRIPLES8))
        
        for s in range(4):
            u, v, w = orb[s, 0], orb[s, 1], orb[s, 2]
            for idx_t, (a, b, c) in enumerate(TRIPLES8):
                det = (u[a]*(v[b]*w[c]-v[c]*w[b]) - u[b]*(v[a]*w[c]-v[c]*w[a]) + u[c]*(v[a]*w[b]-v[b]*w[a]))
                residual[idx_t] += det
        
        return residual - omega
    
    def combined_orbit_residual(x_orb):
        """Combined anti-symmetric (84) + exterior (56) = 140 equations."""
        return np.concatenate([orbit_antisym(x_orb), orbit_exterior(x_orb)])
    
    # Phase 1: Find orbits satisfying both conditions
    print(f"\n{'='*60}")
    print("Phase 1: Anti-symmetric + exterior optimization (140 eqs, 96 params)")
    print(f"{'='*60}")
    
    np.random.seed(42)
    best_cost = float('inf')
    best_x = None
    t0 = time.time()
    
    for trial in range(500):
        x0 = np.random.randn(96) * 0.5
        try:
            res = least_squares(combined_orbit_residual, x0, method='trf',
                              max_nfev=3000, ftol=1e-15, xtol=1e-15, gtol=1e-15)
            if res.cost < best_cost:
                best_cost = res.cost
                best_x = res.x
                if res.cost < 1e-20:
                    print(f"  Trial {trial}: cost={res.cost:.2e} — EXACT! ({time.time()-t0:.1f}s)")
                    break
        except:
            pass
        
        if trial % 50 == 49:
            print(f"  Trial {trial}: best {best_cost:.2e} ({time.time()-t0:.1f}s)")
    
    elapsed = time.time() - t0
    print(f"\nPhase 1 result: cost={best_cost:.2e} ({elapsed:.1f}s)")
    
    if best_cost < 1e-10:
        # Check components
        asym_err = np.max(np.abs(orbit_antisym(best_x)))
        ext_err = np.max(np.abs(orbit_exterior(best_x)))
        print(f"  Anti-symmetric max error: {asym_err:.2e}")
        print(f"  Exterior max error: {ext_err:.2e}")
        print("  Phase 1 SUCCEEDED: orbit parameters found!")
    else:
        print("  Phase 1 FAILED: no orbit solution found")
        # Check which part is harder
        asym_only = least_squares(orbit_antisym, best_x, method='trf', max_nfev=3000,
                                 ftol=1e-15, xtol=1e-15, gtol=1e-15)
        ext_only = least_squares(orbit_exterior, best_x, method='trf', max_nfev=3000,
                                ftol=1e-15, xtol=1e-15, gtol=1e-15)
        print(f"  Anti-symmetric only: cost={asym_only.cost:.2e}")
        print(f"  Exterior only: cost={ext_only.cost:.2e}")
        
        # Check if the system is genuinely overdetermined
        # Jacobian at best point
        from scipy.optimize import approx_fprime
        eps = 1e-7
        J = np.zeros((140, 96))
        for j in range(96):
            e = np.zeros(96)
            e[j] = eps
            J[:, j] = (combined_orbit_residual(best_x + e) - combined_orbit_residual(best_x - e)) / (2*eps)
        rank_J = np.linalg.matrix_rank(J, tol=1e-8)
        print(f"  Jacobian rank at best point: {rank_J}/140 (96 params)")
        if rank_J > 96:
            print(f"  System is OVERDETERMINED with {rank_J} independent constraints > 96 params")
            print(f"  => Phase 1 is generically infeasible!")
        
    results = {
        'phase1_cost': float(best_cost),
        'phase1_elapsed': elapsed,
        'phase1_converged': best_cost < 1e-10,
    }
    out = OUT / 'decomposed_results.json'
    out.write_text(json.dumps(results, indent=2) + '\n')
    print(f"\nSaved {out}")

if __name__ == '__main__':
    main()
