#!/usr/bin/env python3
r"""analysis v2: efficient Gauss-Newton + scipy.optimize for rank-22 T_{333}.

Fixes the Jacobian computation from v1 and uses scipy.optimize.least_squares
for robust Levenberg-Marquardt optimization.
"""
import numpy as np
from scipy.optimize import least_squares
from pathlib import Path
import json, time

def make_T333():
    T = np.zeros((9,9,9), dtype=np.float64)
    for ip in range(3):
        for m in range(3):
            for kp in range(3):
                T[3*ip+m, 3*m+kp, 3*ip+kp] = 1.0
    return T

def load_qmm_scheme(path):
    path = Path(path)
    U, V, W = [], [], []
    for line in path.read_text().splitlines():
        parts = line.strip().split()
        if len(parts) >= 10 and parts[0] in ('u','v','w'):
            vals = [float(x) for x in parts[1:10]]
            {'u': U, 'v': V, 'w': W}[parts[0]].append(vals)
    return np.array(U).T, np.array(V).T, np.array(W).T

def khatri_rao(A, B):
    mA, r = A.shape
    mB = B.shape[0]
    return (A[:, np.newaxis, :] * B[np.newaxis, :, :]).reshape(mA*mB, r)

# ---- Residual and Jacobian for scipy.optimize.least_squares ----
def brent_residual(x, T_flat, r, m=9):
    """Residual vector: T - sum u_i x v_i x w_i, flattened to 729."""
    U = x[:m*r].reshape(m, r)
    V = x[m*r:2*m*r].reshape(m, r)
    W = x[2*m*r:].reshape(m, r)
    T_approx = np.einsum('ir,jr,kr->ijk', U, V, W).ravel()
    return T_flat - T_approx

def brent_jacobian(x, T_flat, r, m=9):
    """Analytical Jacobian of residual. Shape: (m^3, 3*m*r).
    
    Residual[a*m^2 + b*m + c] = T[a,b,c] - sum_i U[a,i]*V[b,i]*W[c,i]
    dRes/dU[a',i] = -delta(a,a') * V[b,i] * W[c,i]
    dRes/dV[b',i] = -U[a,i] * delta(b,b') * W[c,i]
    dRes/dW[c',i] = -U[a,i] * V[b,i] * delta(c,c')
    
    Variable layout: x = [U.ravel(), V.ravel(), W.ravel()]
    U.ravel() with reshape(m,r): U[a,i] = x[a*r+i]
    """
    n_eq = m**3
    n_var = 3 * m * r
    U = x[:m*r].reshape(m, r)
    V = x[m*r:2*m*r].reshape(m, r)
    W = x[2*m*r:].reshape(m, r)
    
    J = np.zeros((n_eq, n_var))
    
    # Precompute outer products
    VW = np.einsum('bi,ci->bci', V, W)  # m x m x r: VW[b,c,i] = V[b,i]*W[c,i]
    UW = np.einsum('ai,ci->aci', U, W)  # m x m x r
    UV = np.einsum('ai,bi->abi', U, V)  # m x m x r
    
    for i in range(r):
        vw_i = VW[:,:,i].ravel()  # m^2 vector
        uw_i = UW[:,:,i].ravel()
        uv_i = UV[:,:,i].ravel()
        
        for a in range(m):
            # dRes[a*m^2+b*m+c]/dU[a,i] = -V[b,i]*W[c,i]
            row_start = a * m * m
            col_U = a * r + i
            J[row_start:row_start + m*m, col_U] = -vw_i
        
        for b in range(m):
            # dRes[a*m^2+b*m+c]/dV[b,i] = -U[a,i]*W[c,i]
            col_V = m*r + b*r + i
            for a in range(m):
                row_start = a*m*m + b*m
                J[row_start:row_start+m, col_V] = -UW[a,:,i]
        
        for c in range(m):
            # dRes[a*m^2+b*m+c]/dW[c,i] = -U[a,i]*V[b,i]
            col_W = 2*m*r + c*r + i
            for a in range(m):
                for b in range(m):
                    row = a*m*m + b*m + c
                    J[row, col_W] = -U[a,i] * V[b,i]
    
    return J

def als_cp(T, r, U0=None, V0=None, W0=None, max_iter=2000, reg=1e-12):
    m1, m2, m3 = T.shape
    T1 = T.reshape(m1, m2*m3)
    T2 = T.transpose(1,0,2).reshape(m2, m1*m3)
    T3 = T.transpose(2,0,1).reshape(m3, m1*m2)
    Tn = np.linalg.norm(T)
    rng = np.random.default_rng()
    U = U0.copy() if U0 is not None else rng.standard_normal((m1, r))
    V = V0.copy() if V0 is not None else rng.standard_normal((m2, r))
    W = W0.copy() if W0 is not None else rng.standard_normal((m3, r))
    
    best_res = 1.0
    for it in range(max_iter):
        KR = khatri_rao(V, W); G = KR.T@KR + reg*np.eye(r)
        U = np.linalg.solve(G, KR.T@T1.T).T
        KR = khatri_rao(U, W); G = KR.T@KR + reg*np.eye(r)
        V = np.linalg.solve(G, KR.T@T2.T).T
        KR = khatri_rao(U, V); G = KR.T@KR + reg*np.eye(r)
        W = np.linalg.solve(G, KR.T@T3.T).T
        
        res = np.linalg.norm(T - np.einsum('ir,jr,kr->ijk', U, V, W)) / Tn
        best_res = min(best_res, res)
        if res < 1e-14 or (it > 50 and abs(res - best_res) < 1e-16):
            break
    return U, V, W, best_res

def scipy_lm_optimize(T, r, U0, V0, W0, max_nfev=5000):
    """Use scipy Levenberg-Marquardt for rank-r decomposition."""
    T_flat = T.ravel()
    x0 = np.concatenate([U0.ravel(), V0.ravel(), W0.ravel()])
    Tn = np.linalg.norm(T)
    
    result = least_squares(
        brent_residual, x0,
        jac=brent_jacobian,
        args=(T_flat, r),
        method='lm',
        max_nfev=max_nfev,
        ftol=1e-15, xtol=1e-15, gtol=1e-15
    )
    
    final_res = np.linalg.norm(result.fun) / Tn
    return result, final_res

def main():
    T = make_T333()
    Tn = np.linalg.norm(T)
    T_flat = T.ravel()
    print(f'T333: shape={T.shape}, norm={Tn:.6f}')
    
    # Determine base directory from script location
    script_dir = Path(__file__).resolve().parent
    ws_dir = script_dir.parent  # workspace/
    data_dir = ws_dir / 'data'
    out_dir = data_dir / 'real_optimization'
    out_dir.mkdir(parents=True, exist_ok=True)
    
    # Load cn122
    cn122_path = data_dir / 'cn122_r23_reproduce' / 'scheme.qmm'
    U23, V23, W23 = load_qmm_scheme(cn122_path)
    cn122_res = np.linalg.norm(T - np.einsum('ir,jr,kr->ijk', U23, V23, W23)) / Tn
    print(f'cn122 residual: {cn122_res:.2e}')
    
    results = {'experiments': []}
    
    # ---- Exp 1: Jacobian verification ----
    print('\n=== Jacobian verification ===')
    rng = np.random.default_rng(123)
    x_test = rng.standard_normal(3*9*22)
    J_ana = brent_jacobian(x_test, T_flat, 22)
    # Numerical check
    eps = 1e-7
    J_num = np.zeros_like(J_ana)
    for j in range(J_ana.shape[1]):
        xp = x_test.copy(); xp[j] += eps
        xm = x_test.copy(); xm[j] -= eps
        J_num[:, j] = (brent_residual(xp, T_flat, 22) - brent_residual(xm, T_flat, 22)) / (2*eps)
    err = np.max(np.abs(J_ana - J_num))
    print(f'  Jacobian max error: {err:.2e}')
    assert err < 1e-4, f"Jacobian error too large: {err}"
    
    # ---- Exp 2: scipy LM from cn122 truncations ----
    print('\n=== Exp 2: scipy LM rank-22, cn122 truncations ===')
    trunc_results = []
    for drop in range(23):
        cols = [j for j in range(23) if j != drop]
        U0 = U23[:, cols].copy()
        V0 = V23[:, cols].copy()
        W0 = W23[:, cols].copy()
        
        # First ALS warm-up
        U_w, V_w, W_w, als_res = als_cp(T, 22, U0=U0, V0=V0, W0=W0, max_iter=500)
        
        # Then scipy LM
        res_obj, lm_res = scipy_lm_optimize(T, 22, U_w, V_w, W_w, max_nfev=3000)
        trunc_results.append({
            'drop': drop, 'als_res': float(als_res), 'lm_res': float(lm_res),
            'nfev': res_obj.nfev, 'success': bool(res_obj.success),
            'cost': float(res_obj.cost), 'optimality': float(res_obj.optimality)
        })
        if drop < 5 or lm_res < 0.01:
            print(f'  drop={drop}: ALS={als_res:.4e} -> LM={lm_res:.4e} (nfev={res_obj.nfev})')
    
    best_drop = min(trunc_results, key=lambda x: x['lm_res'])
    print(f'  Best: drop={best_drop["drop"]}, lm_res={best_drop["lm_res"]:.6e}')
    results['experiments'].append({
        'name': 'lm_r22_cn122_truncations',
        'best': best_drop,
        'all': trunc_results
    })
    
    # ---- Exp 3: scipy LM from random starts ----
    print('\n=== Exp 3: scipy LM rank-22, random starts (30 trials) ===')
    random_lm = []
    for trial in range(30):
        U_w, V_w, W_w, als_res = als_cp(T, 22, max_iter=1000)
        res_obj, lm_res = scipy_lm_optimize(T, 22, U_w, V_w, W_w, max_nfev=2000)
        random_lm.append(float(lm_res))
        if trial < 3 or lm_res < 0.005:
            print(f'  trial {trial}: ALS={als_res:.4e} -> LM={lm_res:.4e}')
    
    print(f'  Best: {min(random_lm):.6e}, Median: {np.median(random_lm):.6e}')
    results['experiments'].append({
        'name': 'lm_r22_random',
        'best': float(min(random_lm)),
        'median': float(np.median(random_lm)),
        'min5': sorted(random_lm)[:5]
    })
    
    # ---- Exp 4: scipy LM rank-23, random starts (calibration) ----
    print('\n=== Exp 4: scipy LM rank-23, random starts (30 trials) ===')
    r23_lm = []
    for trial in range(30):
        U_w, V_w, W_w, als_res = als_cp(T, 23, max_iter=1000)
        res_obj, lm_res = scipy_lm_optimize(T, 23, U_w, V_w, W_w, max_nfev=3000)
        r23_lm.append(float(lm_res))
        if trial < 3 or lm_res < 1e-8:
            print(f'  trial {trial}: ALS={als_res:.4e} -> LM={lm_res:.4e}')
    
    n_conv = sum(1 for r in r23_lm if r < 1e-8)
    print(f'  Best: {min(r23_lm):.6e}, Converged: {n_conv}/30')
    results['experiments'].append({
        'name': 'lm_r23_random',
        'best': float(min(r23_lm)),
        'n_converged': n_conv,
        'min5': sorted(r23_lm)[:5]
    })
    
    # ---- Exp 5: Positive control - rank-22 random tensor ----
    print('\n=== Exp 5: scipy LM rank-22, random rank-22 tensor (control) ===')
    rng = np.random.default_rng(42)
    Ut = rng.standard_normal((9, 22))
    Vt = rng.standard_normal((9, 22))
    Wt = rng.standard_normal((9, 22))
    T22 = np.einsum('ir,jr,kr->ijk', Ut, Vt, Wt)
    T22_flat = T22.ravel()
    T22n = np.linalg.norm(T22)
    
    ctrl_lm = []
    for trial in range(20):
        U_w, V_w, W_w, _ = als_cp(T22, 22, max_iter=1000)
        x0 = np.concatenate([U_w.ravel(), V_w.ravel(), W_w.ravel()])
        res_obj = least_squares(brent_residual, x0, jac=brent_jacobian,
                                args=(T22_flat, 22), method='lm',
                                max_nfev=3000, ftol=1e-15, xtol=1e-15, gtol=1e-15)
        rel_res = np.linalg.norm(res_obj.fun) / T22n
        ctrl_lm.append(float(rel_res))
        if trial < 3 or rel_res < 1e-8:
            print(f'  trial {trial}: LM={rel_res:.4e}')
    
    n_ctrl_conv = sum(1 for r in ctrl_lm if r < 1e-8)
    print(f'  Best: {min(ctrl_lm):.6e}, Converged: {n_ctrl_conv}/20')
    results['experiments'].append({
        'name': 'lm_r22_control_tensor',
        'best': float(min(ctrl_lm)),
        'n_converged': n_ctrl_conv,
        'min5': sorted(ctrl_lm)[:5]
    })
    
    # ---- Summary ----
    print('\n=== Summary ===')
    for e in results['experiments']:
        print(f"  {e['name']}: best={e.get('best', e.get('best',{}).get('lm_res','?'))}")
    
    out_path = out_dir / 'real_optimization_v2.json'
    out_path.write_text(json.dumps(results, indent=2, default=str) + '\n')
    print(f'\nSaved to {out_path}')

if __name__ == '__main__':
    main()
