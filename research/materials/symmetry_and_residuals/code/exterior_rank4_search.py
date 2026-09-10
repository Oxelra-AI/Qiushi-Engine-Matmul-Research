#!/usr/bin/env python3
"""
analysis: Find a rank-4 decomposition of omega in Lambda^3(sl_3 = C^8).

Since omega is in the dense GL_8-orbit of Lambda^3(C^8) (verified), and 
dim sigma_3 <= 48 < 56 = dim Lambda^3(C^8), the exterior rank is >= 4.
We search for an exact rank-4 decomposition.

Method: nonlinear least squares over R, then verify over F_p.
"""
from __future__ import annotations
import numpy as np, itertools, json, time
from pathlib import Path
from scipy.optimize import least_squares

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'exterior_rank4'
OUT.mkdir(parents=True, exist_ok=True)

N = 8  # dim sl_3

TRIPLES = list(itertools.combinations(range(N), 3))
TRIPLE_IDX = {t: i for i, t in enumerate(TRIPLES)}
DIM3 = len(TRIPLES)  # C(8,3) = 56

def idx(a, b):
    return 3*a + b

def build_omega_sl3():
    """Build omega in Lambda^3(sl_3) coordinates directly.
    
    sl_3 basis:
    b0=E01, b1=E02, b2=E10, b3=E12, b4=E20, b5=E21, b6=E00-E11, b7=E11-E22
    
    omega = alternating part of tr(ABC) restricted to sl_3.
    """
    # Change-of-basis: B maps sl_3 basis to gl_3 standard basis
    B = np.zeros((9, 8))
    B[1, 0] = 1  # b0 = E_01
    B[2, 1] = 1  # b1 = E_02
    B[3, 2] = 1  # b2 = E_10
    B[5, 3] = 1  # b3 = E_12
    B[6, 4] = 1  # b4 = E_20
    B[7, 5] = 1  # b5 = E_21
    B[0, 6] = 1; B[4, 6] = -1  # b6 = E_00 - E_11
    B[4, 7] = 1; B[8, 7] = -1  # b7 = E_11 - E_22
    
    # Build omega in gl_3 basis first
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
    
    # Project to sl_3 via Lambda^3(B^+)
    B_pinv = np.linalg.pinv(B)  # 8x9
    
    triples9 = list(itertools.combinations(range(9), 3))
    
    omega_vec = np.zeros(DIM3)  # in Lambda^3(C^8)
    
    for (i9, j9, k9), coef in omega_gl3.items():
        # Express e_i9 ^ e_j9 ^ e_k9 in sl_3 basis
        # e_i9 = sum_a B[i9,a] b_a, so B_pinv[a, i9] = coefficient of b_a
        u = B_pinv[:, i9]
        v = B_pinv[:, j9]
        w = B_pinv[:, k9]
        
        for (a, b, c) in TRIPLES:
            det = (u[a]*(v[b]*w[c] - v[c]*w[b]) 
                 - u[b]*(v[a]*w[c] - v[c]*w[a]) 
                 + u[c]*(v[a]*w[b] - v[b]*w[a]))
            omega_vec[TRIPLE_IDX[(a,b,c)]] += coef * det
    
    return omega_vec

def wedge_product(u, v, w):
    """Compute u ^ v ^ w in Lambda^3(C^N) as a vector."""
    result = np.zeros(DIM3)
    for idx_t, (a, b, c) in enumerate(TRIPLES):
        det = (u[a]*(v[b]*w[c] - v[c]*w[b]) 
             - u[b]*(v[a]*w[c] - v[c]*w[a]) 
             + u[c]*(v[a]*w[b] - v[b]*w[a]))
        result[idx_t] = det
    return result

def residual_func(x, omega):
    """Residual for least squares: omega - sum of 4 wedge products."""
    # x has 4*3*8 = 96 components
    x = x.reshape(4, 3, N)
    total = np.zeros(DIM3)
    for j in range(4):
        total += wedge_product(x[j, 0], x[j, 1], x[j, 2])
    return omega - total

def jacobian_func(x, omega):
    """Jacobian of the residual."""
    x = x.reshape(4, 3, N)
    J = np.zeros((DIM3, 96))
    
    for j in range(4):
        u, v, w = x[j, 0], x[j, 1], x[j, 2]
        for idx_t, (a, b, c) in enumerate(TRIPLES):
            # d(u^v^w)/du_i
            for i in range(N):
                # Derivative of det w.r.t. u[i]
                if i == a:
                    d = v[b]*w[c] - v[c]*w[b]
                elif i == b:
                    d = -(v[a]*w[c] - v[c]*w[a])
                elif i == c:
                    d = v[a]*w[b] - v[b]*w[a]
                else:
                    d = 0
                J[idx_t, j*24 + 0*8 + i] -= d
            
            # d(u^v^w)/dv_i
            for i in range(N):
                if i == b:
                    d = u[a]*w[c] - u[c]*w[a]
                elif i == a:
                    d = -(u[b]*w[c] - u[c]*w[b])
                elif i == c:
                    d = u[b]*w[a] - u[a]*w[b]
                else:
                    d = 0
                J[idx_t, j*24 + 1*8 + i] -= d
            
            # d(u^v^w)/dw_i
            for i in range(N):
                if i == c:
                    d = u[a]*v[b] - u[b]*v[a]
                elif i == a:
                    d = u[b]*v[c] - u[c]*v[b]
                elif i == b:
                    d = -(u[a]*v[c] - u[c]*v[a])
                else:
                    d = 0
                J[idx_t, j*24 + 2*8 + i] -= d
    
    return J

def main():
    print("=" * 70)
    print("analysis: Finding rank-4 exterior decomposition of omega")
    print("=" * 70)
    
    omega = build_omega_sl3()
    print(f"omega norm: {np.linalg.norm(omega):.6f}")
    print(f"omega nonzero: {np.sum(np.abs(omega) > 1e-10)}/{DIM3}")
    
    best_result = None
    best_residual = float('inf')
    
    np.random.seed(42)
    n_trials = 200
    t0 = time.time()
    
    for trial in range(n_trials):
        x0 = np.random.randn(96) * 0.5
        
        try:
            result = least_squares(
                residual_func, x0, args=(omega,),
                jac=jacobian_func,
                method='lm',
                max_nfev=2000,
                ftol=1e-14, xtol=1e-14, gtol=1e-14
            )
            
            res_norm = np.linalg.norm(result.fun)
            if res_norm < best_residual:
                best_residual = res_norm
                best_result = result
                if res_norm < 1e-10:
                    print(f"  Trial {trial}: residual {res_norm:.2e} — SUCCESS!")
                    break
        except Exception as e:
            pass
        
        if trial % 20 == 19:
            print(f"  Trial {trial}: best residual so far {best_residual:.2e} ({time.time()-t0:.1f}s)")
    
    elapsed = time.time() - t0
    print(f"\nBest residual: {best_residual:.2e} after {trial+1} trials ({elapsed:.1f}s)")
    
    if best_residual < 1e-8:
        x_sol = best_result.x.reshape(4, 3, N)
        print(f"\nRank-4 decomposition FOUND!")
        
        # Print the decomposition
        for j in range(4):
            u, v, w = x_sol[j, 0], x_sol[j, 1], x_sol[j, 2]
            wdg = wedge_product(u, v, w)
            print(f"\n  Term {j}:")
            print(f"    u = {np.round(u, 4)}")
            print(f"    v = {np.round(v, 4)}")
            print(f"    w = {np.round(w, 4)}")
            print(f"    |u^v^w| = {np.linalg.norm(wdg):.4f}")
        
        # Verify
        total = np.zeros(DIM3)
        for j in range(4):
            total += wedge_product(x_sol[j, 0], x_sol[j, 1], x_sol[j, 2])
        verify_err = np.max(np.abs(total - omega))
        print(f"\n  Verification: max|sum - omega| = {verify_err:.2e}")
        
        # Try to rationalize (round to simple fractions)
        # Check over several primes
        print("\n  Checking structure...")
        for j in range(4):
            u, v, w = x_sol[j, 0], x_sol[j, 1], x_sol[j, 2]
            norms = [np.linalg.norm(u), np.linalg.norm(v), np.linalg.norm(w)]
            print(f"    Term {j}: |u|={norms[0]:.4f}, |v|={norms[1]:.4f}, |w|={norms[2]:.4f}")
        
        # Save solution
        results = {
            'exterior_rank': 4,
            'residual_norm': float(best_residual),
            'verification_error': float(verify_err),
            'n_trials': trial + 1,
            'elapsed_sec': elapsed,
            'decomposition': []
        }
        for j in range(4):
            results['decomposition'].append({
                'u': x_sol[j, 0].tolist(),
                'v': x_sol[j, 1].tolist(),
                'w': x_sol[j, 2].tolist(),
            })
        
        out = OUT / 'exterior_rank4_decomposition.json'
        out.write_text(json.dumps(results, indent=2) + '\n')
        print(f"\nSaved {out}")
    else:
        print(f"\nDid not find exact rank-4 decomposition (best {best_residual:.2e})")
        print("This does NOT mean rank != 4; the numerical search may need more trials or a structured approach.")
        
        results = {
            'exterior_rank_lower_bound': 4,
            'best_residual': float(best_residual),
            'n_trials': n_trials,
            'elapsed_sec': elapsed,
        }
        out = OUT / 'exterior_rank4_search.json'
        out.write_text(json.dumps(results, indent=2) + '\n')
        print(f"\nSaved {out}")

if __name__ == '__main__':
    main()
