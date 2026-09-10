#!/usr/bin/env python3
"""analysis v4: focused LM continuation from best ALS point + rank-23 comparison.

From v3: best ALS start is cn122 drop_term=1 at 1.979e-02, LM improved to 5.469e-04.
Now: (1) Continue LM with 10000 nfev, (2) Compare rank-23, (3) Control.
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

def load_qmm(path):
    U, V, W = [], [], []
    for line in Path(path).read_text().splitlines():
        p = line.strip().split()
        if len(p) >= 10 and p[0] in ('u','v','w'):
            {'u': U, 'v': V, 'w': W}[p[0]].append([float(x) for x in p[1:10]])
    return np.array(U).T, np.array(V).T, np.array(W).T

def khatri_rao(A, B):
    return (A[:, None, :] * B[None, :, :]).reshape(A.shape[0]*B.shape[0], -1)

def als_cp(T, r, U0=None, V0=None, W0=None, max_iter=2000, reg=1e-12):
    m = 9; Tn = np.linalg.norm(T)
    T1 = T.reshape(m, m*m); T2 = T.transpose(1,0,2).reshape(m, m*m); T3 = T.transpose(2,0,1).reshape(m, m*m)
    U = U0.copy() if U0 is not None else np.random.randn(m, r)
    V = V0.copy() if V0 is not None else np.random.randn(m, r)
    W = W0.copy() if W0 is not None else np.random.randn(m, r)
    best = 1.0
    for it in range(max_iter):
        KR = khatri_rao(V, W); U = np.linalg.solve(KR.T@KR + reg*np.eye(r), KR.T@T1.T).T
        KR = khatri_rao(U, W); V = np.linalg.solve(KR.T@KR + reg*np.eye(r), KR.T@T2.T).T
        KR = khatri_rao(U, V); W = np.linalg.solve(KR.T@KR + reg*np.eye(r), KR.T@T3.T).T
        res = np.linalg.norm(T - np.einsum('ir,jr,kr->ijk', U, V, W)) / Tn
        best = min(best, res)
        if res < 1e-14: break
    return U, V, W, best

def brent_res(x, T_flat, r, m=9):
    U, V, W = x[:m*r].reshape(m,r), x[m*r:2*m*r].reshape(m,r), x[2*m*r:].reshape(m,r)
    return T_flat - np.einsum('ir,jr,kr->ijk', U, V, W).ravel()

def brent_jac(x, T_flat, r, m=9):
    U, V, W = x[:m*r].reshape(m,r), x[m*r:2*m*r].reshape(m,r), x[2*m*r:].reshape(m,r)
    J = np.zeros((m**3, 3*m*r))
    VW = np.einsum('bi,ci->bci', V, W).reshape(m*m, r)
    for a in range(m):
        J[a*m*m:(a+1)*m*m, a*r:(a+1)*r] = -VW
    UW = np.einsum('ai,ci->aci', U, W)
    for b in range(m):
        for a in range(m):
            J[a*m*m+b*m:a*m*m+b*m+m, m*r+b*r:m*r+(b+1)*r] = -UW[a,:,:]
    UV = np.einsum('ai,bi->abi', U, V).reshape(m*m, r)
    for c in range(m):
        idx = np.array([a*m*m + b*m + c for a in range(m) for b in range(m)])
        J[idx, 2*m*r+c*r:2*m*r+(c+1)*r] = -UV
    return J

def run_lm(T, r, U0, V0, W0, max_nfev=5000):
    T_flat = T.ravel(); Tn = np.linalg.norm(T)
    x0 = np.concatenate([U0.ravel(), V0.ravel(), W0.ravel()])
    res = least_squares(brent_res, x0, jac=brent_jac, args=(T_flat, r),
                        method='lm', max_nfev=max_nfev,
                        ftol=1e-15, xtol=1e-15, gtol=1e-15)
    return res, np.linalg.norm(res.fun) / Tn

def main():
    T = make_T333(); Tn = np.linalg.norm(T)
    sd = Path(__file__).resolve().parent.parent
    U23, V23, W23 = load_qmm(sd / 'data/cn122_r23_reproduce/scheme.qmm')
    out = sd / 'data/real_optimization'
    out.mkdir(parents=True, exist_ok=True)
    
    results = {}
    
    # ---- Exp 1: Extended LM from cn122 drop-1 ----
    print('=== Exp 1: Extended LM rank-22 from cn122 drop=1 ===')
    cols = [j for j in range(23) if j != 1]
    U0, V0, W0, als_res = als_cp(T, 22, U23[:,cols], V23[:,cols], W23[:,cols], 3000)
    print(f'  ALS warm-up: {als_res:.6e}')
    
    t0 = time.time()
    res_obj, lm_res = run_lm(T, 22, U0, V0, W0, max_nfev=10000)
    print(f'  LM: {lm_res:.8e} ({time.time()-t0:.1f}s, nfev={res_obj.nfev}, cost={res_obj.cost:.2e})')
    print(f'  optimality={res_obj.optimality:.2e}, status={res_obj.status}, message={res_obj.message}')
    
    results['rank22_drop1_extended'] = {
        'als_res': float(als_res), 'lm_res': float(lm_res),
        'nfev': res_obj.nfev, 'cost': float(res_obj.cost),
        'optimality': float(res_obj.optimality), 'status': int(res_obj.status)
    }
    
    # Try ALL 23 truncations with extended LM
    print('\n=== Exp 2: All 23 cn122 truncations with 5000 nfev LM ===')
    trunc = []
    for drop in range(23):
        cols = [j for j in range(23) if j != drop]
        U0, V0, W0, als_res = als_cp(T, 22, U23[:,cols], V23[:,cols], W23[:,cols], 1000)
        res_obj, lm_res = run_lm(T, 22, U0, V0, W0, max_nfev=5000)
        trunc.append({'drop': drop, 'als': float(als_res), 'lm': float(lm_res),
                      'opt': float(res_obj.optimality), 'nfev': res_obj.nfev})
        if drop < 5 or lm_res < 1e-3:
            print(f'  drop={drop}: ALS={als_res:.4e} -> LM={lm_res:.6e}')
    
    best = min(trunc, key=lambda x: x['lm'])
    print(f'  Best: drop={best["drop"]}, LM={best["lm"]:.8e}')
    results['rank22_all_truncations'] = {'best': best, 'all': trunc}
    
    # ---- Exp 3: rank-23 comparison ----
    print('\n=== Exp 3: ALS+LM rank-23 from random (20 trials) ===')
    r23 = []
    for trial in range(20):
        U, V, W, als_res = als_cp(T, 23, max_iter=1000)
        _, lm_res = run_lm(T, 23, U, V, W, max_nfev=3000)
        r23.append(float(lm_res))
        if trial < 3 or lm_res < 1e-6:
            print(f'  trial {trial}: ALS={als_res:.4e} -> LM={lm_res:.6e}')
    
    n23 = sum(1 for r in r23 if r < 1e-8)
    print(f'  Best: {min(r23):.6e}, Converged(<1e-8): {n23}/20')
    results['rank23_random'] = {'best': float(min(r23)), 'n_conv': n23, 'min5': sorted(r23)[:5]}
    
    # ---- Exp 4: rank-23 from cn122 (sanity) ----
    print('\n=== Exp 4: LM rank-23 from cn122 (sanity check) ===')
    _, lm23 = run_lm(T, 23, U23, V23, W23, max_nfev=100)
    print(f'  cn122 LM: {lm23:.6e}')
    results['rank23_cn122'] = float(lm23)
    
    # ---- Exp 5: control tensor ----
    print('\n=== Exp 5: Control (random rank-22 tensor, 10 trials) ===')
    rng = np.random.default_rng(42)
    T22 = np.einsum('ir,jr,kr->ijk', rng.standard_normal((9,22)),
                    rng.standard_normal((9,22)), rng.standard_normal((9,22)))
    ctrl = []
    for trial in range(10):
        U, V, W, _ = als_cp(T22, 22, max_iter=1000)
        _, lm_res = run_lm(T22, 22, U, V, W, max_nfev=3000)
        ctrl.append(float(lm_res))
        if trial < 3 or lm_res < 1e-6:
            print(f'  trial {trial}: LM={lm_res:.6e}')
    
    nc = sum(1 for r in ctrl if r < 1e-8)
    print(f'  Best: {min(ctrl):.6e}, Converged: {nc}/10')
    results['control_r22'] = {'best': float(min(ctrl)), 'n_conv': nc, 'min5': sorted(ctrl)[:5]}
    
    # ---- Summary ----
    print('\n' + '='*60)
    print('DECISIVE COMPARISON:')
    print(f'  rank-22 T333 best (all truncations): {best["lm"]:.8e}')
    print(f'  rank-23 T333 best (random starts):   {min(r23):.8e}')
    print(f'  rank-22 control best (random tensor): {min(ctrl):.8e}')
    print(f'  rank-23 from cn122:                   {lm23:.8e}')
    print('='*60)
    
    (out / 'real_optimization_v4.json').write_text(json.dumps(results, indent=2, default=str)+'\n')
    print(f'\nSaved to {out}/real_optimization_v4.json')

if __name__ == '__main__':
    main()
