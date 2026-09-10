#!/usr/bin/env python3
r"""analysis v3: vectorized Jacobian + focused scipy LM rank-22 search.

Key insight: each function evaluation takes O(729*594) for the Jacobian,
so we vectorize and reduce experiment count.
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
    U, V, W = [], [], []
    for line in Path(path).read_text().splitlines():
        parts = line.strip().split()
        if len(parts) >= 10 and parts[0] in ('u','v','w'):
            vals = [float(x) for x in parts[1:10]]
            {'u': U, 'v': V, 'w': W}[parts[0]].append(vals)
    return np.array(U).T, np.array(V).T, np.array(W).T

def khatri_rao(A, B):
    return (A[:, np.newaxis, :] * B[np.newaxis, :, :]).reshape(A.shape[0]*B.shape[0], -1)

def brent_residual(x, T_flat, r, m=9):
    U = x[:m*r].reshape(m, r)
    V = x[m*r:2*m*r].reshape(m, r)
    W = x[2*m*r:].reshape(m, r)
    return T_flat - np.einsum('ir,jr,kr->ijk', U, V, W).ravel()

def brent_jacobian_fast(x, T_flat, r, m=9):
    """Vectorized Jacobian. Shape: (m^3, 3*m*r)."""
    U = x[:m*r].reshape(m, r)
    V = x[m*r:2*m*r].reshape(m, r)
    W = x[2*m*r:].reshape(m, r)
    
    n_eq = m**3
    J = np.zeros((n_eq, 3*m*r))
    
    # dRes[a*m^2+b*m+c] / dU[a',i] = -delta(a,a') V[b,i] W[c,i]
    # For each a: block of m^2 rows, contributions from U[a,0..r-1]
    VW = np.einsum('bi,ci->bci', V, W).reshape(m*m, r)  # (m^2, r)
    for a in range(m):
        # rows a*m^2 : (a+1)*m^2, cols a*r : (a+1)*r
        J[a*m*m:(a+1)*m*m, a*r:(a+1)*r] = -VW
    
    # dRes[a*m^2+b*m+c] / dV[b',i] = -U[a,i] delta(b,b') W[c,i]
    UW = np.einsum('ai,ci->aci', U, W)  # (m, m, r)
    for b in range(m):
        # For row a*m^2+b*m+c, we need U[a,i]*W[c,i]
        # Rows with this b: indices a*m^2+b*m+c for a=0..m-1, c=0..m-1
        # Build block: for each a, rows a*m^2+b*m+0 to a*m^2+b*m+(m-1)
        col_start = m*r + b*r
        for a in range(m):
            row_start = a*m*m + b*m
            J[row_start:row_start+m, col_start:col_start+r] = -UW[a, :, :]
    
    # dRes[a*m^2+b*m+c] / dW[c',i] = -U[a,i] V[b,i] delta(c,c')
    UV = np.einsum('ai,bi->abi', U, V).reshape(m*m, r)  # (m^2, r) for (a,b)
    for c in range(m):
        col_start = 2*m*r + c*r
        # Rows with this c: a*m^2+b*m+c for a=0..m-1, b=0..m-1
        rows = np.arange(m*m) * m + c  # [0*m+c, 1*m+c, ..., (m^2-1)*m+c]
        # Wait, rows are a*m^2+b*m+c. For fixed c, varying a,b:
        # linear index = a*81 + b*9 + c
        row_indices = []
        for a in range(m):
            for b in range(m):
                row_indices.append(a*m*m + b*m + c)
        row_indices = np.array(row_indices)
        J[row_indices, col_start:col_start+r] = -UV
    
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
        if res < 1e-14:
            break
    return U, V, W, best_res

def main():
    T = make_T333()
    Tn = np.linalg.norm(T)
    T_flat = T.ravel()
    
    script_dir = Path(__file__).resolve().parent
    data_dir = script_dir.parent / 'data'
    out_dir = data_dir / 'real_optimization'
    out_dir.mkdir(parents=True, exist_ok=True)
    
    # Load cn122
    U23, V23, W23 = load_qmm_scheme(data_dir / 'cn122_r23_reproduce' / 'scheme.qmm')
    print(f'T333 norm={Tn:.4f}, cn122 res={np.linalg.norm(T - np.einsum("ir,jr,kr->ijk", U23, V23, W23))/Tn:.2e}')
    
    results = {'T333_norm': float(Tn), 'experiments': []}
    
    # ---- Jacobian check ----
    rng = np.random.default_rng(123)
    x_test = rng.standard_normal(3*9*22)
    J = brent_jacobian_fast(x_test, T_flat, 22)
    eps = 1e-7
    J_num = np.zeros_like(J)
    for j in range(min(50, J.shape[1])):  # check first 50 columns
        xp, xm = x_test.copy(), x_test.copy()
        xp[j] += eps; xm[j] -= eps
        J_num[:, j] = (brent_residual(xp, T_flat, 22) - brent_residual(xm, T_flat, 22))/(2*eps)
    err = np.max(np.abs(J[:, :50] - J_num[:, :50]))
    print(f'Jacobian check (50 cols): max_err={err:.2e}')
    assert err < 1e-4
    print(f'Jacobian rank at random point: {np.linalg.matrix_rank(J)}')
    
    # ---- Exp 1: ALS rank-22 best starts + LM polish ----
    print('\n=== ALS rank-22: 100 random + 23 truncations, then LM top 10 ===')
    t0 = time.time()
    
    als_results = []
    # Random starts
    for trial in range(100):
        U, V, W, res = als_cp(T, 22, max_iter=2000)
        als_results.append(('random', trial, res, U, V, W))
    
    # cn122 truncation starts
    for drop in range(23):
        cols = [j for j in range(23) if j != drop]
        U, V, W, res = als_cp(T, 22, U0=U23[:,cols], V0=V23[:,cols], W0=W23[:,cols], max_iter=2000)
        als_results.append(('trunc', drop, res, U, V, W))
    
    als_time = time.time() - t0
    als_sorted = sorted(als_results, key=lambda x: x[2])
    print(f'ALS phase: {als_time:.1f}s')
    print(f'  Top 5 ALS residuals:')
    for name, idx, res, _, _, _ in als_sorted[:5]:
        print(f'    {name}_{idx}: {res:.6e}')
    
    results['als_r22_top10'] = [
        {'source': f'{n}_{i}', 'als_res': float(r)} for n, i, r, _, _, _ in als_sorted[:10]
    ]
    
    # LM polish on top 10
    print('\n  LM polish on top 10:')
    lm_results = []
    for name, idx, als_res, U, V, W in als_sorted[:10]:
        x0 = np.concatenate([U.ravel(), V.ravel(), W.ravel()])
        t1 = time.time()
        res_obj = least_squares(brent_residual, x0, jac=brent_jacobian_fast,
                                args=(T_flat, 22), method='lm',
                                max_nfev=2000, ftol=1e-15, xtol=1e-15, gtol=1e-15)
        lm_time = time.time() - t1
        lm_res = np.linalg.norm(res_obj.fun) / Tn
        print(f'    {name}_{idx}: ALS={als_res:.4e} -> LM={lm_res:.6e} ({lm_time:.1f}s, nfev={res_obj.nfev})')
        lm_results.append({
            'source': f'{name}_{idx}', 'als_res': float(als_res),
            'lm_res': float(lm_res), 'nfev': res_obj.nfev,
            'lm_time': round(lm_time, 2)
        })
        
        if lm_res < 1e-10:
            print(f'    *** CONVERGED! Verifying... ***')
            m = 9
            Uf = res_obj.x[:m*22].reshape(m, 22)
            Vf = res_obj.x[m*22:2*m*22].reshape(m, 22)
            Wf = res_obj.x[2*m*22:].reshape(m, 22)
            verify_res = np.linalg.norm(T - np.einsum('ir,jr,kr->ijk', Uf, Vf, Wf)) / Tn
            print(f'    Verification residual: {verify_res:.2e}')
    
    results['experiments'].append({
        'name': 'als_lm_r22_best10', 'lm_results': lm_results
    })
    
    # ---- Exp 2: ALS+LM rank-23 calibration ----
    print('\n=== ALS+LM rank-23 calibration (50 random starts) ===')
    r23_results = []
    for trial in range(50):
        U, V, W, als_res = als_cp(T, 23, max_iter=2000)
        x0 = np.concatenate([U.ravel(), V.ravel(), W.ravel()])
        res_obj = least_squares(brent_residual, x0, jac=brent_jacobian_fast,
                                args=(T_flat, 23), method='lm',
                                max_nfev=2000, ftol=1e-15, xtol=1e-15, gtol=1e-15)
        lm_res = np.linalg.norm(res_obj.fun) / Tn
        r23_results.append(float(lm_res))
        if trial < 3 or lm_res < 1e-8:
            print(f'  trial {trial}: ALS={als_res:.4e} -> LM={lm_res:.6e}')
    
    n_conv_23 = sum(1 for r in r23_results if r < 1e-8)
    print(f'  Best: {min(r23_results):.6e}, Converged: {n_conv_23}/50')
    results['experiments'].append({
        'name': 'als_lm_r23_random',
        'best': float(min(r23_results)),
        'n_converged': n_conv_23,
        'n_trials': 50,
        'min5': sorted(r23_results)[:5]
    })
    
    # ---- Exp 3: Positive control ----
    print('\n=== Control: rank-22 random tensor (20 trials) ===')
    rng2 = np.random.default_rng(42)
    T22 = np.einsum('ir,jr,kr->ijk',
        rng2.standard_normal((9,22)), rng2.standard_normal((9,22)), rng2.standard_normal((9,22)))
    T22_flat = T22.ravel(); T22n = np.linalg.norm(T22)
    
    ctrl_res = []
    for trial in range(20):
        U, V, W, _ = als_cp(T22, 22, max_iter=1000)
        x0 = np.concatenate([U.ravel(), V.ravel(), W.ravel()])
        res_obj = least_squares(brent_residual, x0, jac=brent_jacobian_fast,
                                args=(T22_flat, 22), method='lm',
                                max_nfev=2000, ftol=1e-15, xtol=1e-15, gtol=1e-15)
        ctrl_res.append(float(np.linalg.norm(res_obj.fun) / T22n))
    
    n_ctrl = sum(1 for r in ctrl_res if r < 1e-8)
    print(f'  Best: {min(ctrl_res):.6e}, Converged: {n_ctrl}/20')
    results['experiments'].append({
        'name': 'control_r22_random_tensor',
        'best': float(min(ctrl_res)),
        'n_converged': n_ctrl,
        'min5': sorted(ctrl_res)[:5]
    })
    
    # ---- Summary ----
    print('\n' + '='*60)
    print('SUMMARY')
    print('='*60)
    for e in results['experiments']:
        if 'lm_results' in e:
            best = min(r['lm_res'] for r in e['lm_results'])
            print(f"  {e['name']}: best LM = {best:.6e}")
        else:
            print(f"  {e['name']}: best = {e['best']:.6e}, converged = {e.get('n_converged','?')}")
    
    out_path = out_dir / 'real_optimization_v3.json'
    out_path.write_text(json.dumps(results, indent=2, default=str) + '\n')
    print(f'\nSaved to {out_path}')

if __name__ == '__main__':
    main()
