#!/usr/bin/env python3
r"""analysisb: Real homotopy continuation — track rank-22 roots toward T_{333}.

Decisive experiment: generate random rank-22 tensors T_0 with known decompositions,
then continuously deform T(t) = (1-t)T_0 + t T_{333} for t ∈ [0,1].
Track the decomposition root using predictor-corrector.

If T_{333} has rank 22, at least one path converges to a finite decomposition.
If T_{333} has rank 23, all paths diverge (amplitude → ∞ or residual leaves zero).

Uses the proven v3 analytical Jacobian from analysis.
"""
from __future__ import annotations
import json, sys, time
from pathlib import Path
import numpy as np
from numpy.linalg import lstsq, norm, svd

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
import rank22_singular_stratum_v2 as s19

R = 22   # target rank
N = 9    # tensor dimension

def make_T333_real():
    T = np.zeros((N, N, N))
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1.0
    return T

def brent_residual_real(U, V, W, T):
    """Compute 729-vector of Brent residuals: T - sum u_i ⊗ v_i ⊗ w_i."""
    Trec = np.zeros_like(T)
    for i in range(U.shape[0]):
        Trec += np.einsum('a,b,c->abc', U[i], V[i], W[i])
    return (T - Trec).ravel()

def brent_jacobian_real(U, V, W):
    """Analytical Jacobian of Brent equations w.r.t. (U, V, W).
    
    J is 729 × (27*r).  Column layout: [u_0(9), v_0(9), w_0(9), u_1(9), ...].
    Brent eq k: T_{a,b,c} - sum_i U[i,a]*V[i,b]*W[i,c] = 0
    dF_k/dU[i,a'] = -delta(a,a') * V[i,b] * W[i,c]
    dF_k/dV[i,b'] = -U[i,a] * delta(b,b') * W[i,c]
    dF_k/dW[i,c'] = -U[i,a] * V[i,b] * delta(c,c')
    """
    r = U.shape[0]
    J = np.zeros((729, 27*r))
    abc = np.arange(729)
    a_idx = abc // 81
    b_idx = (abc % 81) // 9
    c_idx = abc % 9
    for i in range(r):
        base = 27 * i
        u, v, w = U[i], V[i], W[i]
        vw = v[b_idx] * w[c_idx]
        uw = u[a_idx] * w[c_idx]
        uv = u[a_idx] * v[b_idx]
        for a in range(9):
            mask = (a_idx == a)
            J[mask, base + a] = -vw[mask]
        for b in range(9):
            mask = (b_idx == b)
            J[mask, base + 9 + b] = -uw[mask]
        for c in range(9):
            mask = (c_idx == c)
            J[mask, base + 18 + c] = -uv[mask]
    return J

def random_rank22_real(rng, scale=1.0):
    """Generate a random rank-22 tensor over R with known decomposition."""
    U = rng.standard_normal((R, N)) * scale
    V = rng.standard_normal((R, N)) * scale
    W = rng.standard_normal((R, N)) * scale
    T = np.zeros((N, N, N))
    for i in range(R):
        T += np.einsum('a,b,c->abc', U[i], V[i], W[i])
    return T, U, V, W

def amplitude(U, V, W):
    """Total factor amplitude: sum_i ||u_i|| * ||v_i|| * ||w_i||."""
    return sum(norm(U[i]) * norm(V[i]) * norm(W[i]) for i in range(U.shape[0]))

def homotopy_track(T0, U0, V0, W0, T1, max_steps=500, dt_init=0.01, 
                    dt_min=1e-8, dt_max=0.1, tol=1e-10, max_newton=10,
                    max_amp=1e8, verbose=True):
    """Track root from (T0, U0, V0, W0) toward T1 using predictor-corrector.
    
    T(t) = (1-t)*T0 + t*T1.
    At t=0: the decomposition (U0, V0, W0) satisfies T0 = sum u_i ⊗ v_i ⊗ w_i.
    
    Returns: trajectory list of {t, residual, amplitude, svmin, dt} dicts.
    """
    U, V, W = U0.copy(), V0.copy(), W0.copy()
    t = 0.0
    dt = dt_init
    r = U.shape[0]
    n_vars = 27 * r
    
    # Direction of homotopy: dT/dt = T1 - T0
    dT = (T1 - T0).ravel()  # 729-vector
    
    trajectory = []
    
    # Initial check
    res0 = brent_residual_real(U, V, W, T0)
    amp0 = amplitude(U, V, W)
    if verbose:
        print(f"  t=0.000: |res|={norm(res0):.2e}, amp={amp0:.2f}")
    trajectory.append({'t': 0.0, 'residual': float(norm(res0)), 
                       'amplitude': float(amp0), 'dt': dt})
    
    step = 0
    while t < 1.0 and step < max_steps:
        step += 1
        dt = min(dt, 1.0 - t)  # Don't overshoot t=1
        
        # Current target tensor
        Tt = (1 - t) * T0 + t * T1
        
        # Predictor: compute tangent dx/dt = -J^+ dT
        J = brent_jacobian_real(U, V, W)
        
        # Minimum-norm solution: dx/dt = -J^T (J J^T)^{-1} dT
        # Use lstsq for numerical stability
        dx_dt, _, _, sv = lstsq(J, -dT, rcond=None)
        
        # Euler predictor ARTIFACT
        x = np.concatenate([U.ravel(), V.ravel(), W.ravel()])
        x_pred = x + dt * dx_dt
        
        # Unpack
        U_pred = x_pred[:R*N].reshape(R, N)
        V_pred = x_pred[R*N:2*R*N].reshape(R, N)
        W_pred = x_pred[2*R*N:].reshape(R, N)
        
        # Corrector: Newton iterations at t + dt
        t_new = t + dt
        Tt_new = (1 - t_new) * T0 + t_new * T1
        
        Uc, Vc, Wc = U_pred.copy(), V_pred.copy(), W_pred.copy()
        converged = False
        for newton_iter in range(max_newton):
            res = brent_residual_real(Uc, Vc, Wc, Tt_new)
            if norm(res) < tol:
                converged = True
                break
            Jc = brent_jacobian_real(Uc, Vc, Wc)
            dx_corr, _, _, _ = lstsq(Jc, -res, rcond=None)
            xc = np.concatenate([Uc.ravel(), Vc.ravel(), Wc.ravel()])
            xc += dx_corr
            Uc = xc[:R*N].reshape(R, N)
            Vc = xc[R*N:2*R*N].reshape(R, N)
            Wc = xc[2*R*N:].reshape(R, N)
        
        # Adaptive ARTIFACT size
        res_final = brent_residual_real(Uc, Vc, Wc, Tt_new)
        res_norm = norm(res_final)
        amp_new = amplitude(Uc, Vc, Wc)
        
        if converged and res_norm < tol * 100:
            # Accept ARTIFACT
            U, V, W = Uc, Vc, Wc
            t = t_new
            # Increase ARTIFACT size
            dt = min(dt * 1.5, dt_max)
        else:
            # Reject ARTIFACT, reduce dt
            dt = max(dt * 0.5, dt_min)
            if dt <= dt_min:
                if verbose:
                    print(f"  t={t:.4f}: STALLED, |res|={res_norm:.2e}, amp={amp_new:.2e}")
                trajectory.append({'t': float(t), 'residual': float(res_norm),
                                   'amplitude': float(amp_new), 'dt': float(dt),
                                   'event': 'stalled'})
                break
            continue  # Try again with smaller dt
        
        # Log
        if step % 20 == 0 or t >= 1.0 - 1e-12 or amp_new > max_amp:
            svmin_J = min(sv) if len(sv) else 0
            if verbose:
                print(f"  t={t:.4f}: |res|={res_norm:.2e}, amp={amp_new:.2e}, "
                      f"σ_min={svmin_J:.2e}, dt={dt:.4f}, steps={step}")
        
        trajectory.append({'t': float(t), 'residual': float(res_norm),
                           'amplitude': float(amp_new), 'dt': float(dt)})
        
        # Check amplitude bound
        if amp_new > max_amp:
            if verbose:
                print(f"  t={t:.4f}: DIVERGED, amp={amp_new:.2e} > {max_amp:.2e}")
            trajectory[-1]['event'] = 'diverged'
            break
    
    return trajectory

def main():
    rng = np.random.default_rng(2026090428)
    T333 = make_T333_real()
    T333_norm = norm(T333)
    
    print(f"T333 norm: {T333_norm:.4f}")
    print(f"T333 Brent vector nnz: {np.count_nonzero(T333.ravel())}")
    
    results = {
        'purpose': 'Real homotopy continuation: track rank-22 roots toward T333',
        'T333_norm': float(T333_norm),
        'rank': R,
        'paths': [],
    }
    
    # Run multiple homotopy paths from different random rank-22 tensors
    n_paths = 10
    print(f"\n=== Running {n_paths} homotopy paths ===")
    
    for path_id in range(n_paths):
        print(f"\n--- Path {path_id} ---")
        
        # Random rank-22 start
        T0, U0, V0, W0 = random_rank22_real(rng, scale=1.0)
        
        # Verify start
        res_start = norm(brent_residual_real(U0, V0, W0, T0))
        amp_start = amplitude(U0, V0, W0)
        print(f"  Start: |res|={res_start:.2e}, amp={amp_start:.2f}, "
              f"|T0|={norm(T0):.4f}")
        
        traj = homotopy_track(T0, U0, V0, W0, T333,
                              max_steps=300, dt_init=0.02, dt_max=0.1,
                              tol=1e-10, max_amp=1e6, verbose=True)
        
        # Summary
        t_final = traj[-1]['t'] if traj else 0
        amp_final = traj[-1].get('amplitude', 0)
        res_final = traj[-1].get('residual', 0)
        event = traj[-1].get('event', 'reached_t1' if t_final >= 1.0 - 1e-6 else 'unknown')
        
        path_rec = {
            'path_id': path_id,
            't_final': float(t_final),
            'amp_start': float(amp_start),
            'amp_final': float(amp_final),
            'res_final': float(res_final),
            'n_steps': len(traj),
            'event': event,
        }
        
        # If reached t=1, verify Brent equations
        if t_final >= 1.0 - 1e-6 and res_final < 1e-6:
            path_rec['verified_rank22'] = True
            print(f"  *** POTENTIAL RANK-22 SOLUTION FOUND! ***")
            print(f"  Final amplitude: {amp_final:.2f}")
        else:
            path_rec['verified_rank22'] = False
        
        results['paths'].append(path_rec)
        print(f"  Result: t={t_final:.4f}, event={event}, amp={amp_final:.2e}")
    
    # Summary statistics
    n_reached = sum(1 for p in results['paths'] if p['t_final'] >= 0.99)
    n_diverged = sum(1 for p in results['paths'] if p.get('event') == 'diverged')
    n_stalled = sum(1 for p in results['paths'] if p.get('event') == 'stalled')
    n_rank22 = sum(1 for p in results['paths'] if p.get('verified_rank22', False))
    
    print(f"\n=== Summary ===")
    print(f"  Reached t≈1: {n_reached}/{n_paths}")
    print(f"  Diverged: {n_diverged}/{n_paths}")
    print(f"  Stalled: {n_stalled}/{n_paths}")
    print(f"  Verified rank-22: {n_rank22}/{n_paths}")
    
    results['summary'] = {
        'n_paths': n_paths,
        'n_reached_t1': n_reached,
        'n_diverged': n_diverged,
        'n_stalled': n_stalled,
        'n_rank22': n_rank22,
    }
    
    # Amplitude growth analysis
    for p_rec in results['paths'][:3]:
        print(f"\n  Path {p_rec['path_id']}: "
              f"amp {p_rec['amp_start']:.1f} → {p_rec['amp_final']:.1e}, "
              f"t_final={p_rec['t_final']:.4f}")
    
    out_dir = Path(__file__).resolve().parent.parent / 'data/completion_chart'
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / 'homotopy_results.json'
    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nSaved to {out_path}")

if __name__ == '__main__':
    main()
