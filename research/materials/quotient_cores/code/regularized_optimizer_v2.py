#!/usr/bin/env python3
r"""analysis: Regularized real rank-22 optimizer for T_{333}.

Reuses the PROVEN v3 analytical Jacobian. Adds L2 regularization
to prevent cancellation degeneration (earlier analysis showed factors
diverge without regularization). Multiple lambda values compare:
- lam=0: unregularized (baseline, known to degenerate)
- lam=1e-6..1e-4: prevent divergence; if bounded rank-22 exists, find it

Variable layout: x = [U.ravel(), V.ravel(), W.ravel()] with U(9,r), V(9,r), W(9,r).
"""
import numpy as np
from scipy.optimize import least_squares
from pathlib import Path
import json, time

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'regularized_optimizer'
OUT.mkdir(parents=True, exist_ok=True)

# === T333 and cn122 ===
def make_T333():
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
            p = line.strip().split()
            if not p: continue
            if p[0] == 'u': U.append(list(map(float, p[1:])))
            elif p[0] == 'v': V.append(list(map(float, p[1:])))
            elif p[0] == 'w': W.append(list(map(float, p[1:])))
    # QMM convention: U[term,a], V[term,b], W[term,c]
    # v3 convention: U[a,term], V[b,term], W[c,term]
    return np.array(U).T, np.array(V).T, np.array(W).T

# === Proven v3 infrastructure ===
def khatri_rao(A, B):
    """Column-wise Kronecker: A(m,r), B(n,r) -> (mn, r)."""
    m, r = A.shape; n = B.shape[0]
    return (A[:, None, :] * B[None, :, :]).reshape(m*n, r)

def residual_vec(x, T_flat, m, r):
    U = x[:m*r].reshape(m, r)
    V = x[m*r:2*m*r].reshape(m, r)
    W = x[2*m*r:].reshape(m, r)
    approx = np.einsum('ai,bi,ci->abc', U, V, W).ravel()
    return T_flat - approx

def jacobian_vec(x, T_flat, m, r):
    U = x[:m*r].reshape(m, r)
    V = x[m*r:2*m*r].reshape(m, r)
    W = x[2*m*r:].reshape(m, r)
    n_eq = m**3
    J = np.zeros((n_eq, 3*m*r))
    VW = np.einsum('bi,ci->bci', V, W).reshape(m*m, r)
    for a in range(m):
        J[a*m*m:(a+1)*m*m, a*r:(a+1)*r] = -VW
    UW = np.einsum('ai,ci->aci', U, W)
    for b in range(m):
        col_start = m*r + b*r
        for a in range(m):
            J[a*m*m+b*m:a*m*m+b*m+m, col_start:col_start+r] = -UW[a]
    UV = np.einsum('ai,bi->abi', U, V).reshape(m*m, r)
    for c in range(m):
        col_start = 2*m*r + c*r
        row_indices = np.array([a*m*m+b*m+c for a in range(m) for b in range(m)])
        J[row_indices, col_start:col_start+r] = -UV
    return J

def als_cp(T, r, max_iter=2000, rng=None):
    if rng is None: rng = np.random.default_rng()
    m = T.shape[0]
    T1 = T.reshape(m, m*m)
    T2 = T.transpose(1,0,2).reshape(m, m*m)
    T3 = T.transpose(2,0,1).reshape(m, m*m)
    Tn = np.linalg.norm(T)
    U = rng.standard_normal((m, r))
    V = rng.standard_normal((m, r))
    W = rng.standard_normal((m, r))
    reg = 1e-12
    for _ in range(max_iter):
        KR = khatri_rao(V, W); G = KR.T@KR + reg*np.eye(r)
        U = np.linalg.solve(G, KR.T@T1.T).T
        KR = khatri_rao(U, W); G = KR.T@KR + reg*np.eye(r)
        V = np.linalg.solve(G, KR.T@T2.T).T
        KR = khatri_rao(U, V); G = KR.T@KR + reg*np.eye(r)
        W = np.linalg.solve(G, KR.T@T3.T).T
    res = np.linalg.norm(T - np.einsum('ai,bi,ci->abc', U, V, W)) / Tn
    return U, V, W, res

# === Augmented system ===
def aug_residual(x, T_flat, m, r, lam):
    brent = residual_vec(x, T_flat, m, r)
    return np.concatenate([brent, np.sqrt(lam)*x])

def aug_jacobian(x, T_flat, m, r, lam):
    J = jacobian_vec(x, T_flat, m, r)
    n = len(x)
    return np.vstack([J, np.sqrt(lam)*np.eye(n)])

# === Main ===
def main():
    T = make_T333()
    Tn = np.linalg.norm(T)
    T_flat = T.ravel()
    m = 9; r = 22
    rng = np.random.default_rng(2026)

    U23, V23, W23 = load_cn122()
    cn_res = np.linalg.norm(T - np.einsum('ai,bi,ci->abc', U23, V23, W23)) / Tn
    print(f'T333 norm={Tn:.4f}, cn122 res={cn_res:.2e}')

    # Jacobian check
    x_test = rng.standard_normal(3*m*r)
    J_a = jacobian_vec(x_test, T_flat, m, r)
    J_fd = np.zeros_like(J_a)
    h = 1e-7
    f0 = residual_vec(x_test, T_flat, m, r)
    for j in range(min(50, J_a.shape[1])):
        x_p = x_test.copy(); x_p[j] += h
        J_fd[:, j] = (residual_vec(x_p, T_flat, m, r) - f0) / h
    jac_err = np.max(np.abs(J_a[:, :50] - J_fd[:, :50]))
    print(f'Jacobian check (50 cols): max_err={jac_err:.2e}')
    jac_rank = np.linalg.matrix_rank(J_a, tol=1e-8)
    print(f'Jacobian rank at random point: {jac_rank}')

    results = {"r": r, "experiments": []}

    # === Exp 1: cn122 truncations + regularized LM ===
    print('\n=== Exp 1: cn122 truncations + regularized LM ===')
    lambdas = [0, 1e-8, 1e-6, 1e-4]
    for drop in [1, 0, 5, 10, 15]:  # best drops from analysis
        cols = [j for j in range(23) if j != drop]
        U0 = U23[:, cols]; V0 = V23[:, cols]; W0 = W23[:, cols]
        x0 = np.concatenate([U0.ravel(), V0.ravel(), W0.ravel()])
        init_res = np.linalg.norm(residual_vec(x0, T_flat, m, r)) / Tn

        for lam in lambdas:
            t0 = time.time()
            if lam > 0:
                res = least_squares(aug_residual, x0, jac=aug_jacobian,
                                    args=(T_flat, m, r, lam),
                                    method='lm', max_nfev=5000, verbose=0)
            else:
                res = least_squares(residual_vec, x0, jac=jacobian_vec,
                                    args=(T_flat, m, r),
                                    method='lm', max_nfev=5000, verbose=0)
            elapsed = time.time() - t0
            U_s = res.x[:m*r].reshape(m, r)
            V_s = res.x[m*r:2*m*r].reshape(m, r)
            W_s = res.x[2*m*r:].reshape(m, r)
            brent_res = np.linalg.norm(T - np.einsum('ai,bi,ci->abc', U_s, V_s, W_s))
            rel = brent_res / Tn
            amp = np.sqrt(np.sum(np.einsum('ai,bi,ci->i',
                                           U_s**2, np.ones_like(V_s), np.ones_like(W_s)) *
                                 np.einsum('ai,bi,ci->i',
                                           np.ones_like(U_s), V_s**2, np.ones_like(W_s)) *
                                 np.einsum('ai,bi,ci->i',
                                           np.ones_like(U_s), np.ones_like(V_s), W_s**2)))
            rec = {"source": f"cn122_drop{drop}", "lam": lam, "init_rel": init_res,
                   "brent_rel": rel, "amp": amp, "nfev": res.nfev,
                   "opt": float(res.optimality), "elapsed": elapsed}
            results["experiments"].append(rec)
            tag = "***" if rel < 1e-10 else ""
            print(f'  drop={drop} lam={lam:.0e}: init={init_res:.4e} -> rel={rel:.6e} '
                  f'amp={amp:.1f} nfev={res.nfev} opt={res.optimality:.2e} {elapsed:.1f}s {tag}')
            if rel < 1e-10:
                print('  *** EXACT RANK-22 DECOMPOSITION FOUND ***')
                np.savez(OUT / f'rank22_drop{drop}_lam{lam}.npz', U=U_s, V=V_s, W=W_s)

    # === Exp 2: ALS + regularized LM from random starts ===
    print('\n=== Exp 2: ALS + regularized LM, 30 random starts ===')
    als_pool = []
    for trial in range(30):
        U_a, V_a, W_a, als_res = als_cp(T, r, max_iter=1500, rng=rng)
        x_a = np.concatenate([U_a.ravel(), V_a.ravel(), W_a.ravel()])
        als_pool.append((als_res, x_a))
    als_pool.sort(key=lambda t: t[0])
    print(f'  ALS top 5: {[f"{p[0]:.4e}" for p in als_pool[:5]]}')

    for idx in range(min(5, len(als_pool))):
        als_res_val, x0 = als_pool[idx]
        for lam in [1e-6, 1e-4]:
            t0 = time.time()
            res = least_squares(aug_residual, x0, jac=aug_jacobian,
                                args=(T_flat, m, r, lam),
                                method='lm', max_nfev=5000, verbose=0)
            elapsed = time.time() - t0
            U_s = res.x[:m*r].reshape(m, r)
            V_s = res.x[m*r:2*m*r].reshape(m, r)
            W_s = res.x[2*m*r:].reshape(m, r)
            brent_res = np.linalg.norm(T - np.einsum('ai,bi,ci->abc', U_s, V_s, W_s)) / Tn
            print(f'  [{idx}] lam={lam:.0e}: ALS={als_res_val:.4e} -> rel={brent_res:.6e} '
                  f'nfev={res.nfev} opt={res.optimality:.2e} {elapsed:.1f}s')
            results["experiments"].append(
                {"source": f"als_{idx}", "lam": lam, "als_res": als_res_val,
                 "brent_rel": brent_res, "nfev": res.nfev})

    # === Exp 3: rank-22 random tensor positive control ===
    print('\n=== Exp 3: Positive control (random rank-22 tensor) ===')
    U_c = rng.standard_normal((m, r)); V_c = rng.standard_normal((m, r))
    W_c = rng.standard_normal((m, r))
    T_ctrl = np.einsum('ai,bi,ci->abc', U_c, V_c, W_c)
    x_c = np.concatenate([(U_c+0.1*rng.standard_normal((m,r))).ravel(),
                           (V_c+0.1*rng.standard_normal((m,r))).ravel(),
                           (W_c+0.1*rng.standard_normal((m,r))).ravel()])
    res_c = least_squares(residual_vec, x_c, jac=jacobian_vec,
                          args=(T_ctrl.ravel(), m, r),
                          method='lm', max_nfev=5000, verbose=0)
    ctrl_rel = np.linalg.norm(T_ctrl - np.einsum('ai,bi,ci->abc',
                              res_c.x[:m*r].reshape(m,r),
                              res_c.x[m*r:2*m*r].reshape(m,r),
                              res_c.x[2*m*r:].reshape(m,r))) / np.linalg.norm(T_ctrl)
    print(f'  Control: rel={ctrl_rel:.6e} nfev={res_c.nfev}')
    results["positive_control_rel"] = ctrl_rel

    fp = OUT / 'regularized_optimization.json'
    fp.write_text(json.dumps(results, indent=2, default=str) + '\n')
    print(f'\nSaved to {fp}')

if __name__ == '__main__':
    main()
