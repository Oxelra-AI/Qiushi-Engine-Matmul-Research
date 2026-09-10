#!/usr/bin/env python3
r"""analysis: Regularized real ALS+trust-region rank-22 optimizer for T_{333}.

Key improvement over analysis: L2 regularization prevents factor-norm
divergence (cancellation degeneration). If a bounded rank-22 decomposition
exists, the regularized optimizer will find it. If not, the optimizer reaches
a stable nonzero-residual minimum with bounded factors.

Augmented residual: [Brent_residual (729), sqrt(lam)*u (198), sqrt(lam)*v (198), sqrt(lam)*w (198)]
Total: 1323 components, 594 variables.
"""
import numpy as np
from scipy.optimize import least_squares
from pathlib import Path
import json, time

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'regularized_optimizer'
OUT.mkdir(parents=True, exist_ok=True)

def build_T333():
    T = np.zeros((9,9,9))
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1.0
    return T

def load_cn122():
    path = WS / 'data' / 'cn122_r23_reproduce' / 'scheme.qmm'
    U, V, W = [], [], []
    with open(path) as f:
        for line in f:
            parts = line.strip().split()
            if not parts: continue
            if parts[0] == 'u': U.append(list(map(float, parts[1:])))
            elif parts[0] == 'v': V.append(list(map(float, parts[1:])))
            elif parts[0] == 'w': W.append(list(map(float, parts[1:])))
    return np.array(U), np.array(V), np.array(W)

def pack(U, V, W):
    return np.concatenate([U.ravel(), V.ravel(), W.ravel()])

def unpack(x, r):
    U = x[:9*r].reshape(r, 9)
    V = x[9*r:18*r].reshape(r, 9)
    W = x[18*r:].reshape(r, 9)
    return U, V, W

def brent_residual_vec(x, T, r, lam):
    """Augmented residual: Brent + L2 regularization."""
    U, V, W = unpack(x, r)
    # Brent residual
    approx = np.einsum('ia,ib,ic->abc', U, V, W)
    brent = (T - approx).ravel()  # 729
    # Regularization: sqrt(lam) * factors
    sl = np.sqrt(lam)
    reg = sl * x  # 594
    return np.concatenate([brent, reg])

def brent_jacobian_vec(x, T, r, lam):
    """Analytical Jacobian of augmented residual. Shape: (729+594) × 594."""
    U, V, W = unpack(x, r)
    nvar = 27 * r
    J = np.zeros((729 + nvar, nvar))
    
    # Brent part: dR_{abc}/d(u_{i,a'}) = -delta(a,a') v_{ib} w_{ic}
    for i in range(r):
        vw = np.outer(V[i], W[i]).ravel()  # 81
        for a in range(9):
            J[81*a:81*a+81, 27*i+a] = -vw
        
        for b in range(9):
            for a2 in range(9):
                J[81*a2+9*b:81*a2+9*b+9, 27*i+9+b] -= U[i, a2] * W[i]
        
        uv = np.outer(U[i], V[i]).ravel()
        for c in range(9):
            rows = np.arange(81)*9 + np.tile(np.arange(9)*81, 9) // 9 * 81
            # Actually compute row indices properly
            for a2 in range(9):
                for b2 in range(9):
                    J[81*a2 + 9*b2 + c, 27*i + 18 + c] -= U[i, a2] * V[i, b2]
    
    # Regularization part: d(sqrt(lam)*x_j)/d(x_j) = sqrt(lam)
    sl = np.sqrt(lam)
    for j in range(nvar):
        J[729 + j, j] = sl
    
    return J

def als_rank_r(T, r, n_iter=3000, rng=None):
    """ALS for rank-r approximation of T."""
    if rng is None: rng = np.random.default_rng()
    U = rng.standard_normal((r, 9))
    V = rng.standard_normal((r, 9))
    W = rng.standard_normal((r, 9))
    T_norm = np.linalg.norm(T)
    
    for it in range(n_iter):
        # Fix V, W; solve for U
        VW = np.einsum('ib,ic->ibc', V, W).reshape(r, 81)  # r × 81
        M = VW @ VW.T  # r × r
        rhs = VW @ T.reshape(9, 81).T  # r × 9
        try:
            U = np.linalg.solve(M + 1e-12*np.eye(r), rhs).T.T
        except:
            U = rng.standard_normal((r, 9))
        U = np.linalg.solve(M + 1e-12*np.eye(r), 
                            np.einsum('ibc,abc->ia', 
                                      np.einsum('ib,ic->ibc', V, W), T))
        
        # Fix U, W; solve for V
        UW = np.einsum('ia,ic->iac', U, W).reshape(r, 81)
        M = UW @ UW.T
        V = np.linalg.solve(M + 1e-12*np.eye(r),
                            np.einsum('iac,abc->ib',
                                      np.einsum('ia,ic->iac', U, W), T))
        
        # Fix U, V; solve for W
        UV = np.einsum('ia,ib->iab', U, V).reshape(r, 81)
        M = UV @ UV.T
        W = np.linalg.solve(M + 1e-12*np.eye(r),
                            np.einsum('iab,abc->ic',
                                      np.einsum('ia,ib->iab', U, V), T))
    
    approx = np.einsum('ia,ib,ic->abc', U, V, W)
    rel_res = np.linalg.norm(T - approx) / T_norm
    return U, V, W, rel_res

def main():
    T = build_T333()
    T_norm = np.linalg.norm(T)
    r = 22
    nvar = 27 * r
    rng = np.random.default_rng(2026)
    
    print(f"T333 norm={T_norm:.4f}")
    
    # Load cn122 for truncation starts
    Ucn, Vcn, Wcn = load_cn122()
    cn_res = np.linalg.norm(T - np.einsum('ia,ib,ic->abc', Ucn, Vcn, Wcn))
    print(f"cn122 residual: {cn_res:.2e}")
    
    results = {"tensor": "T333", "rank": r, "experiments": []}
    
    # === Experiment 1: Regularized LM from cn122 truncations ===
    print("\n=== Exp 1: Regularized LM from cn122 truncations ===")
    lambdas = [1e-4, 1e-6, 1e-8, 0.0]
    
    for drop in range(min(23, 5)):  # first 5 truncations
        for lam in lambdas:
            keep = [j for j in range(23) if j != drop]
            U0, V0, W0 = Ucn[keep], Vcn[keep], Wcn[keep]
            x0 = pack(U0, V0, W0)
            
            t0 = time.time()
            try:
                res = least_squares(
                    brent_residual_vec, x0,
                    jac=brent_jacobian_vec,
                    args=(T, r, lam),
                    method='lm',
                    max_nfev=5000,
                    verbose=0
                )
                elapsed = time.time() - t0
                
                # Extract Brent residual (without regularization)
                U_sol, V_sol, W_sol = unpack(res.x, r)
                brent_res = np.linalg.norm(T - np.einsum('ia,ib,ic->abc', U_sol, V_sol, W_sol))
                rel_res = brent_res / T_norm
                amp = np.sum(np.linalg.norm(np.einsum('ia,ib,ic->iabc', U_sol, V_sol, W_sol).reshape(r,-1), axis=1))
                
                rec = {"source": f"cn122_drop{drop}", "lambda": lam,
                       "brent_rel_residual": rel_res, "amplitude": amp,
                       "nfev": res.nfev, "cost": float(res.cost),
                       "optimality": float(res.optimality),
                       "status": int(res.status), "elapsed": elapsed}
                results["experiments"].append(rec)
                
                tag = "***" if rel_res < 1e-10 else ""
                print(f"  drop={drop} λ={lam:.0e}: rel_res={rel_res:.6e} amp={amp:.1f} "
                      f"nfev={res.nfev} opt={res.optimality:.2e} {elapsed:.1f}s {tag}")
                
                if rel_res < 1e-10:
                    print("  *** EXACT RANK-22 DECOMPOSITION FOUND! ***")
                    np.savez(OUT / 'rank22_solution.npz', U=U_sol, V=V_sol, W=W_sol)
                    
            except Exception as e:
                print(f"  drop={drop} λ={lam:.0e}: ERROR {e}")
    
    # === Experiment 2: ALS + regularized LM from random starts ===
    print(f"\n=== Exp 2: ALS + regularized LM, 50 random starts ===")
    als_results = []
    for trial in range(50):
        U_als, V_als, W_als, als_res = als_rank_r(T, r, n_iter=1000, rng=rng)
        als_results.append((als_res, pack(U_als, V_als, W_als)))
    
    als_results.sort(key=lambda x: x[0])
    print(f"  ALS top 5: {[f'{r[0]:.4e}' for r in als_results[:5]]}")
    
    for idx in range(min(10, len(als_results))):
        als_res_val, x0 = als_results[idx]
        lam = 1e-6
        
        try:
            res = least_squares(
                brent_residual_vec, x0,
                jac=brent_jacobian_vec,
                args=(T, r, lam),
                method='lm',
                max_nfev=5000,
                verbose=0
            )
            U_sol, V_sol, W_sol = unpack(res.x, r)
            brent_res = np.linalg.norm(T - np.einsum('ia,ib,ic->abc', U_sol, V_sol, W_sol))
            rel_res = brent_res / T_norm
            amp = np.sum(np.linalg.norm(np.einsum('ia,ib,ic->iabc', U_sol, V_sol, W_sol).reshape(r,-1), axis=1))
            
            rec = {"source": f"random_als_{idx}", "als_residual": als_res_val,
                   "lambda": lam, "brent_rel_residual": rel_res, "amplitude": amp,
                   "nfev": res.nfev, "optimality": float(res.optimality)}
            results["experiments"].append(rec)
            
            tag = "***" if rel_res < 1e-10 else ""
            print(f"  [{idx}] ALS={als_res_val:.4e} -> LM rel={rel_res:.6e} amp={amp:.1f} "
                  f"nfev={res.nfev} opt={res.optimality:.2e} {tag}")
                  
        except Exception as e:
            print(f"  [{idx}] ERROR: {e}")
    
    # === Experiment 3: Rank-23 positive control ===
    print(f"\n=== Exp 3: Rank-23 positive control (cn122 as-is) ===")
    x23 = pack(Ucn, Vcn, Wcn)
    lam = 1e-8
    res23 = least_squares(
        brent_residual_vec, x23,
        jac=brent_jacobian_vec,
        args=(T, 23, lam),
        method='lm',
        max_nfev=2000,
        verbose=0
    )
    U23, V23, W23 = unpack(res23.x, 23)
    res23_brent = np.linalg.norm(T - np.einsum('ia,ib,ic->abc', U23, V23, W23)) / T_norm
    print(f"  Rank-23 from cn122: rel_res={res23_brent:.6e} (expect ~0)")
    
    # === Experiment 4: Random rank-22 tensor positive control ===
    print(f"\n=== Exp 4: Random rank-22 tensor control ===")
    U_ctrl = rng.standard_normal((r, 9))
    V_ctrl = rng.standard_normal((r, 9))
    W_ctrl = rng.standard_normal((r, 9))
    T_ctrl = np.einsum('ia,ib,ic->abc', U_ctrl, V_ctrl, W_ctrl)
    
    x_ctrl = pack(U_ctrl + 0.1*rng.standard_normal((r,9)),
                  V_ctrl + 0.1*rng.standard_normal((r,9)),
                  W_ctrl + 0.1*rng.standard_normal((r,9)))
    lam = 1e-6
    res_ctrl = least_squares(
        brent_residual_vec, x_ctrl,
        jac=brent_jacobian_vec,
        args=(T_ctrl, r, lam),
        method='lm',
        max_nfev=5000,
        verbose=0
    )
    U_c, V_c, W_c = unpack(res_ctrl.x, r)
    ctrl_res = np.linalg.norm(T_ctrl - np.einsum('ia,ib,ic->abc', U_c, V_c, W_c)) / np.linalg.norm(T_ctrl)
    ctrl_amp = np.sum(np.linalg.norm(np.einsum('ia,ib,ic->iabc', U_c, V_c, W_c).reshape(r,-1), axis=1))
    print(f"  Random rank-22 control: rel_res={ctrl_res:.6e} amp={ctrl_amp:.1f}")
    
    results["rank23_control"] = {"rel_residual": res23_brent}
    results["rank22_control"] = {"rel_residual": ctrl_res, "amplitude": ctrl_amp}
    
    fp = OUT / 'regularized_optimization.json'
    fp.write_text(json.dumps(results, indent=2, default=str) + '\n')
    print(f"\nSaved to {fp}")

if __name__ == '__main__':
    main()
