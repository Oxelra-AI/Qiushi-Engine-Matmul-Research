#!/usr/bin/env python3
r"""Real-valued numerical rank-22 decomposition search for T_{333}.

Over R (or C), the tensor decomposition problem admits a well-posed
least-squares formulation:
    min_{U,V,W}  ||T_333 - sum_i u_i x v_i x w_i||_F^2
This has gradient and Hessian structure from the Brent Jacobian.

Methods:
  (1) ALS (alternating least squares): fix two factors, solve for third
  (2) Gradient descent with line search
  (3) Gauss-Newton / Levenberg-Marquardt via scipy.optimize.least_squares

Starting points:
  (a) Random initialization
  (b) cn122 truncation (remove one of 23 terms)
  (c) Perturbed cn122 truncation
"""
import numpy as np
from pathlib import Path
import json, time, sys

# ---- tensor construction ----
def make_T333():
    """Build the 3x3 matrix multiplication tensor T_{333} as 9x9x9 array."""
    T = np.zeros((9,9,9), dtype=np.float64)
    for ip in range(3):
        for m in range(3):
            for kp in range(3):
                a = 3*ip + m
                b = 3*m + kp
                c = 3*ip + kp
                T[a,b,c] = 1.0
    return T

def verify_tensor(T):
    """Verify T has exactly 27 ones at the right positions."""
    count = 0
    for a in range(9):
        for b in range(9):
            for c in range(9):
                ip, m = divmod(a, 3)
                mp, kp = divmod(b, 3)
                ip2, kp2 = divmod(c, 3)
                expected = 1.0 if (m == mp and ip == ip2 and kp == kp2) else 0.0
                assert T[a,b,c] == expected, f"T[{a},{b},{c}] = {T[a,b,c]}, expected {expected}"
                count += int(expected == 1.0)
    assert count == 27
    return True

def load_qmm_scheme(path):
    """Load a QMM_SCHEME_V1 file. Return (U, V, W) each 9 x rank."""
    path = Path(path)
    U_list, V_list, W_list = [], [], []
    current_factor = None
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith('QMM') or line.startswith('dimensions') \
           or line.startswith('rank') or line.startswith('domain') \
           or line.startswith('index_order') or line.startswith('term'):
            continue
        parts = line.split()
        if len(parts) >= 10 and parts[0] in ('u','v','w'):
            vals = [float(x) for x in parts[1:10]]
            if parts[0] == 'u':
                U_list.append(vals)
            elif parts[0] == 'v':
                V_list.append(vals)
            else:
                W_list.append(vals)
    U = np.array(U_list).T  # 9 x r
    V = np.array(V_list).T
    W = np.array(W_list).T
    return U, V, W

def load_cn122(data_dir):
    """Load cn122 rank-23 decomposition."""
    path = data_dir / 'cn122_r23_reproduce' / 'scheme.qmm'
    if path.exists():
        return load_qmm_scheme(path)
    return None, None, None

# ---- Khatri-Rao product ----
def khatri_rao(A, B):
    """Column-wise Kronecker: (mA x r) o (mB x r) -> (mA*mB x r)."""
    mA, r = A.shape
    mB = B.shape[0]
    return (A[:, np.newaxis, :] * B[np.newaxis, :, :]).reshape(mA*mB, r)

# ---- ALS ----
def als_cp(T, r, U0=None, V0=None, W0=None, max_iter=2000, tol=1e-14,
           verbose=False, reg=1e-12):
    """ALS for rank-r CP decomposition of a 3-tensor T (real-valued).
    Returns (U, V, W, residual_history)."""
    m1, m2, m3 = T.shape
    T1 = T.reshape(m1, m2*m3)
    T2 = T.transpose(1,0,2).reshape(m2, m1*m3)
    T3 = T.transpose(2,0,1).reshape(m3, m1*m2)
    Tnorm = np.linalg.norm(T)
    
    # init
    rng = np.random.default_rng()
    U = U0.copy() if U0 is not None else rng.standard_normal((m1, r))
    V = V0.copy() if V0 is not None else rng.standard_normal((m2, r))
    W = W0.copy() if W0 is not None else rng.standard_normal((m3, r))
    
    history = []
    for it in range(max_iter):
        # update U
        KR_VW = khatri_rao(V, W)  # (m2*m3) x r
        G = KR_VW.T @ KR_VW + reg * np.eye(r)
        U = np.linalg.solve(G, KR_VW.T @ T1.T).T
        
        # update V
        KR_UW = khatri_rao(U, W)
        G = KR_UW.T @ KR_UW + reg * np.eye(r)
        V = np.linalg.solve(G, KR_UW.T @ T2.T).T
        
        # update W
        KR_UV = khatri_rao(U, V)
        G = KR_UV.T @ KR_UV + reg * np.eye(r)
        W = np.linalg.solve(G, KR_UV.T @ T3.T).T
        
        # residual
        T_approx = np.einsum('ir,jr,kr->ijk', U, V, W)
        rel_res = np.linalg.norm(T - T_approx) / Tnorm
        history.append(float(rel_res))
        
        if verbose and (it < 5 or it % 100 == 0):
            print(f'  ALS it {it}: rel_res={rel_res:.6e}')
        
        if rel_res < tol:
            break
        
        # stagnation check
        if it > 50 and abs(history[-1] - history[-2]) < 1e-16:
            break
    
    return U, V, W, history

# ---- Gauss-Newton via scipy ----
def residual_vec(x, T, r):
    """Compute the 729-dim residual vector T - sum u_i x v_i x w_i."""
    m = 9
    U = x[:m*r].reshape(m, r)
    V = x[m*r:2*m*r].reshape(m, r)
    W = x[2*m*r:3*m*r].reshape(m, r)
    T_approx = np.einsum('ir,jr,kr->ijk', U, V, W)
    return (T - T_approx).ravel()

def jacobian_vec(x, T, r):
    """Compute the 729 x (3*9*r) Jacobian of the residual."""
    m = 9
    n_eq = m**3
    U = x[:m*r].reshape(m, r)
    V = x[m*r:2*m*r].reshape(m, r)
    W = x[2*m*r:3*m*r].reshape(m, r)
    
    J = np.zeros((n_eq, 3*m*r))
    
    for i in range(r):
        # dF/du_i[a] at position (a*81 + b*9 + c) = -v_i[b]*w_i[c]
        # Using outer products for efficiency
        vw = np.outer(V[:, i], W[:, i]).ravel()  # 81-dim
        for a in range(m):
            J[a*81:(a+1)*81, i*m + a] -= vw
        
        uw = np.outer(U[:, i], W[:, i]).ravel()  # 81-dim
        for b in range(m):
            J[b*9::81, m*r + i*m + b] -= uw[b*9:(b+1)*9].repeat(9)  # wrong
    
    # Simpler: build J using einsum structure
    J = np.zeros((n_eq, 3*m*r))
    for i in range(r):
        # dRes[a,b,c]/du_i[a'] = -delta(a,a') v_i[b] w_i[c]
        vw_i = np.outer(V[:, i], W[:, i])  # 9x9
        for a in range(m):
            J[a*81:(a+1)*81, i + a*r] = -vw_i.ravel()  # WRONG indexing
    
    # Let me do this correctly with explicit indexing
    J = np.zeros((n_eq, 3*m*r))
    # Variables: [u_0[0],...,u_0[8], u_1[0],...,u_1[8], ..., u_{r-1}[0],...,u_{r-1}[8],
    #             v_0[0],..., w_{r-1}[8]]
    # But x layout is: U.ravel() = [u[0,0],...,u[8,0],u[0,1],...,u[8,r-1]]
    # No: U = x[:m*r].reshape(m, r), so x[:m*r] = [U[0,0],U[1,0],...,U[8,0],U[0,1],...,U[8,r-1]]
    # Wait: reshape(m,r) with row-major: x[0:mr] as (m,r) means x[j] = U[j//r, j%r]?
    # No: reshape(9, r) means U[a, i] = x[a*r + i] for a in 0..8, i in 0..r-1.
    
    # dRes[a,b,c]/dU[a',i] = -delta(a,a') * V[b,i] * W[c,i]
    # Res index = a*81 + b*9 + c
    # U[a',i] index in x = a'*r + i
    
    for i in range(r):
        VW_i = np.outer(V[:, i], W[:, i]).ravel()  # length 81
        for a in range(m):
            # dRes[a,b,c]/dU[a,i] = -V[b,i]*W[c,i] for all b,c
            row_start = a * 81
            col = a * r + i
            J[row_start:row_start+81, col] = -VW_i
        
        UW_i = np.outer(U[:, i], W[:, i]).ravel()  # length 81
        for b in range(m):
            # dRes[a,b,c]/dV[b,i] = -U[a,i]*W[c,i] for all a,c
            col = m*r + b*r + i
            for a in range(m):
                row_start = a*81 + b*9
                J[row_start:row_start+9, col] = -U[a, i] * W[:, i]
        
        UV_i = np.outer(U[:, i], V[:, i]).ravel()  # length 81
        for c in range(m):
            # dRes[a,b,c]/dW[c,i] = -U[a,i]*V[b,i] for all a,b
            col = 2*m*r + c*r + i
            for a in range(m):
                for b in range(m):
                    row = a*81 + b*9 + c
                    J[row, col] = -U[a, i] * V[b, i]
    
    return J

def gauss_newton_search(T, r, x0, max_iter=500, tol=1e-14, verbose=False):
    """Gauss-Newton with Tikhonov regularization for rank-r CP decomposition."""
    m = 9
    n_vars = 3 * m * r
    x = x0.copy()
    Tnorm = np.linalg.norm(T)
    history = []
    
    for it in range(max_iter):
        F = residual_vec(x, T, r)
        rel_res = np.linalg.norm(F) / Tnorm
        history.append(float(rel_res))
        
        if verbose and (it < 5 or it % 50 == 0):
            print(f'  GN it {it}: rel_res={rel_res:.6e}')
        
        if rel_res < tol:
            break
        
        J = jacobian_vec(x, T, r)
        # Gauss-Newton ARTIFACT: (J^T J + lambda I) dx = -J^T F
        lam = 1e-8 * np.linalg.norm(F)**2
        JtJ = J.T @ J + lam * np.eye(n_vars)
        JtF = J.T @ F
        try:
            dx = np.linalg.solve(JtJ, -JtF)
        except np.linalg.LinAlgError:
            break
        
        # Line search
        alpha = 1.0
        for _ in range(20):
            x_new = x + alpha * dx
            F_new = residual_vec(x_new, T, r)
            if np.linalg.norm(F_new) < np.linalg.norm(F):
                break
            alpha *= 0.5
        x = x + alpha * dx
        
        if it > 10 and abs(history[-1] - history[-2]) < 1e-16:
            break
    
    return x, history

# ---- main experiment ----
def main():
    T = make_T333()
    verify_tensor(T)
    Tnorm = np.linalg.norm(T)
    print(f'T333 constructed: shape={T.shape}, nnz={np.count_nonzero(T)}, norm={Tnorm:.6f}')
    
    data_dir = Path('data')
    out_dir = data_dir / 'real_optimization'
    out_dir.mkdir(parents=True, exist_ok=True)
    
    results = {'T333_norm': float(Tnorm), 'experiments': []}
    
    # ---- Experiment 1: ALS rank-23 with cn122 start (positive control) ----
    print('\n=== Exp 1: ALS rank-23, cn122 start (positive control) ===')
    U23, V23, W23 = load_cn122(data_dir)
    
    if U23 is not None:
        T_check = np.einsum('ir,jr,kr->ijk', U23, V23, W23)
        cn122_res = np.linalg.norm(T - T_check) / Tnorm
        print(f'  cn122 initial residual: {cn122_res:.6e}')
        results['cn122_initial_residual'] = float(cn122_res)
        
        U_als, V_als, W_als, hist = als_cp(T, 23, U0=U23, V0=V23, W0=W23,
                                            max_iter=100, verbose=True)
        results['experiments'].append({
            'name': 'als_r23_cn122', 'rank': 23,
            'final_rel_res': hist[-1], 'iterations': len(hist),
            'status': 'converged' if hist[-1] < 1e-10 else 'not_converged'
        })
    else:
        print('  cn122 not loaded')
    
    # ---- Experiment 2: ALS rank-22 from cn122 truncations ----
    print('\n=== Exp 2: ALS rank-22, cn122 truncations (23 starts) ===')
    best_trunc_res = 1.0
    trunc_results = []
    if U23 is not None:
        for drop in range(min(23, U23.shape[1])):
            cols = [j for j in range(U23.shape[1]) if j != drop]
            U_init = U23[:, cols].copy()
            V_init = V23[:, cols].copy()
            W_init = W23[:, cols].copy()
            
            U_r, V_r, W_r, hist = als_cp(T, 22, U0=U_init, V0=V_init, W0=W_init,
                                          max_iter=2000, reg=1e-14)
            final = hist[-1]
            if final < best_trunc_res:
                best_trunc_res = final
            trunc_results.append({'drop_term': drop, 'final_rel_res': float(final),
                                  'iterations': len(hist)})
            if drop < 3 or final < 0.01:
                print(f'  drop={drop}: rel_res={final:.6e} ({len(hist)} iters)')
        
        print(f'  Best truncation residual: {best_trunc_res:.6e}')
        results['experiments'].append({
            'name': 'als_r22_cn122_truncations', 'rank': 22,
            'best_rel_res': float(best_trunc_res),
            'all_truncations': trunc_results
        })
    
    # ---- Experiment 3: ALS rank-22 from random starts ----
    print('\n=== Exp 3: ALS rank-22, random starts (50 trials) ===')
    n_random = 50
    random_results = []
    best_random_res = 1.0
    for trial in range(n_random):
        U_r, V_r, W_r, hist = als_cp(T, 22, max_iter=2000, reg=1e-14)
        final = hist[-1]
        if final < best_random_res:
            best_random_res = final
        random_results.append(float(final))
        if trial < 3:
            print(f'  trial {trial}: rel_res={final:.6e} ({len(hist)} iters)')
    
    print(f'  Best random residual: {best_random_res:.6e}')
    print(f'  Median: {np.median(random_results):.6e}, Mean: {np.mean(random_results):.6e}')
    results['experiments'].append({
        'name': 'als_r22_random', 'rank': 22,
        'n_trials': n_random,
        'best_rel_res': float(best_random_res),
        'median_rel_res': float(np.median(random_results)),
        'mean_rel_res': float(np.mean(random_results)),
        'min5': sorted(random_results)[:5]
    })
    
    # ---- Experiment 4: ALS rank-23 from random starts (calibration) ----
    print('\n=== Exp 4: ALS rank-23, random starts (30 trials) ===')
    n_r23 = 30
    r23_results = []
    best_r23_res = 1.0
    for trial in range(n_r23):
        U_r, V_r, W_r, hist = als_cp(T, 23, max_iter=3000, reg=1e-14)
        final = hist[-1]
        if final < best_r23_res:
            best_r23_res = final
        r23_results.append(float(final))
        if trial < 3 or final < 1e-8:
            print(f'  trial {trial}: rel_res={final:.6e} ({len(hist)} iters)')
    
    print(f'  Best rank-23 random residual: {best_r23_res:.6e}')
    results['experiments'].append({
        'name': 'als_r23_random', 'rank': 23,
        'n_trials': n_r23,
        'best_rel_res': float(best_r23_res),
        'median_rel_res': float(np.median(r23_results)),
        'all': sorted(r23_results)[:10]
    })
    
    # ---- Experiment 5: Gauss-Newton rank-22 from best ALS result ----
    print('\n=== Exp 5: Gauss-Newton rank-22, from perturbed cn122 truncation ===')
    if U23 is not None:
        # Start from best truncation + perturbation
        best_drop = min(range(23), key=lambda d: trunc_results[d]['final_rel_res'])
        cols = [j for j in range(23) if j != best_drop]
        U_init = U23[:, cols] + 0.01 * np.random.randn(9, 22)
        V_init = V23[:, cols] + 0.01 * np.random.randn(9, 22)
        W_init = W23[:, cols] + 0.01 * np.random.randn(9, 22)
        
        # First do ALS to warm up
        U_w, V_w, W_w, _ = als_cp(T, 22, U0=U_init, V0=V_init, W0=W_init,
                                   max_iter=500, reg=1e-14)
        
        # Then Gauss-Newton
        x0 = np.concatenate([U_w.ravel(), V_w.ravel(), W_w.ravel()])
        x_gn, gn_hist = gauss_newton_search(T, 22, x0, max_iter=200, verbose=True)
        
        print(f'  GN final: {gn_hist[-1]:.6e} ({len(gn_hist)} iters)')
        results['experiments'].append({
            'name': 'gauss_newton_r22_cn122_perturbed', 'rank': 22,
            'best_drop_term': int(best_drop),
            'final_rel_res': float(gn_hist[-1]),
            'iterations': len(gn_hist)
        })
    
    # ---- Experiment 6: ALS rank-22 for random rank-22 tensor (positive control) ----
    print('\n=== Exp 6: ALS rank-22, random rank-22 tensor (positive control) ===')
    rng = np.random.default_rng(42)
    U_true = rng.standard_normal((9, 22))
    V_true = rng.standard_normal((9, 22))
    W_true = rng.standard_normal((9, 22))
    T_rand22 = np.einsum('ir,jr,kr->ijk', U_true, V_true, W_true)
    T_rand_norm = np.linalg.norm(T_rand22)
    
    n_ctrl = 20
    ctrl_results = []
    for trial in range(n_ctrl):
        U_r, V_r, W_r, hist = als_cp(T_rand22, 22, max_iter=3000, reg=1e-14)
        final = hist[-1]
        ctrl_results.append(float(final))
        if trial < 3 or final < 1e-8:
            print(f'  trial {trial}: rel_res={final:.6e} ({len(hist)} iters)')
    
    print(f'  Best control residual: {min(ctrl_results):.6e}')
    print(f'  Converged: {sum(1 for r in ctrl_results if r < 1e-8)}/{n_ctrl}')
    results['experiments'].append({
        'name': 'als_r22_random_tensor_control', 'rank': 22,
        'n_trials': n_ctrl,
        'best_rel_res': float(min(ctrl_results)),
        'n_converged': sum(1 for r in ctrl_results if r < 1e-8),
        'min5': sorted(ctrl_results)[:5]
    })
    
    # ---- Summary ----
    print('\n=== Summary ===')
    for exp in results['experiments']:
        best = exp.get('best_rel_res', exp.get('final_rel_res', '?'))
        print(f"  {exp['name']}: best_rel_res={best}")
    
    out_path = out_dir / 'real_optimization_results.json'
    out_path.write_text(json.dumps(results, indent=2, default=str) + '\n')
    print(f'\nSaved to {out_path}')

if __name__ == '__main__':
    main()
