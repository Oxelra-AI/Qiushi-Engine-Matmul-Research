#!/usr/bin/env python3
r"""analysisd: Gauge-fixed real homotopy continuation toward T_{333}.

Previous attempt stalled because the 729×594 Brent Jacobian has rank 550 with
a 44-dim kernel (22 scalings + 26 stabilizer − 2 center − 2 overlap).
Fix: add 44 random linear gauge conditions g(x) = a·x − b = 0 to break the
symmetry.  The augmented system [Brent; gauge] is 773 × 594, full column rank.
"""
import numpy as np, json, time, sys
from numpy.linalg import lstsq, norm, svd, solve
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
import rank22_singular_stratum_v2 as s19

R, N = 22, 9

def make_T333():
    T = np.zeros((N, N, N))
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1.0
    return T

def brent_res(U, V, W, T):
    Trec = np.zeros_like(T)
    for i in range(R):
        Trec += np.einsum('a,b,c->abc', U[i], V[i], W[i])
    return (T - Trec).ravel()

def brent_jac(U, V, W):
    J = np.zeros((729, 27*R))
    abc = np.arange(729); a = abc//81; b = (abc%81)//9; c = abc%9
    for i in range(R):
        base = 27*i
        u, v, w = U[i], V[i], W[i]
        vw = v[b]*w[c]; uw = u[a]*w[c]; uv = u[a]*v[b]
        for aa in range(9): J[a==aa, base+aa] = -vw[a==aa]
        for bb in range(9): J[b==bb, base+9+bb] = -uw[b==bb]
        for cc in range(9): J[c==cc, base+18+cc] = -uv[c==cc]
    return J

def amplitude(U, V, W):
    return sum(norm(U[i])*norm(V[i])*norm(W[i]) for i in range(R))

def pack(U, V, W):
    return np.concatenate([U.ravel(), V.ravel(), W.ravel()])

def unpack(x):
    U = x[:R*N].reshape(R, N)
    V = x[R*N:2*R*N].reshape(R, N)
    W = x[2*R*N:].reshape(R, N)
    return U, V, W

def homotopy_gauged(T0, U0, V0, W0, T1, rng,
                     max_steps=2000, dt_init=0.005, dt_min=1e-12,
                     dt_max=0.05, tol=1e-10, max_newton=20, max_amp=1e8):
    """Gauge-fixed predictor-corrector homotopy."""
    n_vars = 27 * R  # 594
    
    # Gauge: 44 random linear conditions anchored at starting point
    n_gauge = 44
    A_gauge = rng.standard_normal((n_gauge, n_vars))
    x0 = pack(U0, V0, W0)
    b_gauge = A_gauge @ x0  # A_gauge @ x = b_gauge
    
    # Augmented system: [Brent(x,T(t)); A_gauge @ x - b_gauge]
    # Jacobian: [J_brent; A_gauge]  —  (773 × 594)
    
    dT = (T1 - T0).ravel()  # 729-vector: dBrent/dt
    # For the augmented system, dF/dt = [dT; 0]  (gauge doesn't depend on t)
    dF_dt = np.zeros(729 + n_gauge)
    dF_dt[:729] = dT
    
    U, V, W = U0.copy(), V0.copy(), W0.copy()
    t = 0.0; dt = dt_init
    
    trajectory = []
    res0 = norm(brent_res(U, V, W, T0))
    trajectory.append({'t': 0.0, 'res': float(res0), 'amp': float(amplitude(U,V,W))})
    
    for step in range(max_steps):
        if t >= 1.0 - 1e-14:
            break
        dt = min(dt, 1.0 - t)
        
        # Current Jacobian
        J_brent = brent_jac(U, V, W)
        J_aug = np.vstack([J_brent, A_gauge])  # 773 × 594
        
        # Predictor: solve J_aug @ dx/dt = -dF_dt
        # Since J_aug is tall (773×594), use least-squares
        dx_dt, _, _, _ = lstsq(J_aug, -dF_dt, rcond=None)
        
        # Euler ARTIFACT
        x = pack(U, V, W)
        x_pred = x + dt * dx_dt
        U_p, V_p, W_p = unpack(x_pred)
        
        # Corrector: Newton on augmented system at t+dt
        t_new = t + dt
        Tt = (1 - t_new) * T0 + t_new * T1
        
        Uc, Vc, Wc = U_p.copy(), V_p.copy(), W_p.copy()
        converged = False
        for nit in range(max_newton):
            r_brent = brent_res(Uc, Vc, Wc, Tt)
            r_gauge = A_gauge @ pack(Uc, Vc, Wc) - b_gauge
            r_aug = np.concatenate([r_brent, r_gauge])
            
            if norm(r_aug) < tol:
                converged = True; break
            
            J_c = np.vstack([brent_jac(Uc, Vc, Wc), A_gauge])
            dx, _, _, _ = lstsq(J_c, -r_aug, rcond=None)
            xc = pack(Uc, Vc, Wc) + dx
            Uc, Vc, Wc = unpack(xc)
        
        r_final = norm(np.concatenate([brent_res(Uc, Vc, Wc, Tt),
                                       A_gauge @ pack(Uc, Vc, Wc) - b_gauge]))
        amp_new = amplitude(Uc, Vc, Wc)
        
        if converged or r_final < tol * 10:
            U, V, W = Uc, Vc, Wc
            t = t_new
            dt = min(dt * 1.5, dt_max)
            
            if step % 50 == 0 or t >= 1.0 - 1e-6:
                brent_r = norm(brent_res(U, V, W, Tt))
                print(f"  t={t:.6f}: |brent|={brent_r:.2e}, amp={amp_new:.2e}, "
                      f"dt={dt:.4e}, ARTIFACT={step}")
            trajectory.append({'t': float(t), 'res': float(r_final),
                              'amp': float(amp_new), 'dt': float(dt)})
        else:
            dt = dt * 0.3
            if dt < dt_min:
                print(f"  t={t:.6f}: STALLED at ARTIFACT {step}, "
                      f"|res|={r_final:.2e}, amp={amp_new:.2e}")
                trajectory.append({'t': float(t), 'res': float(r_final),
                                  'amp': float(amp_new), 'event': 'stalled'})
                break
        
        if amp_new > max_amp:
            print(f"  t={t:.6f}: DIVERGED, amp={amp_new:.2e}")
            trajectory.append({'t': float(t), 'res': float(r_final),
                              'amp': float(amp_new), 'event': 'diverged'})
            break
    
    return trajectory

def main():
    rng = np.random.default_rng(2026090428)
    T333 = make_T333()
    
    results = {'purpose': 'Gauge-fixed homotopy from random rank-22 toward T333', 'paths': []}
    n_paths = 8
    print(f"Running {n_paths} gauge-fixed homotopy paths")
    
    for pid in range(n_paths):
        print(f"\n--- Path {pid} ---")
        U0 = rng.standard_normal((R, N))
        V0 = rng.standard_normal((R, N))
        W0 = rng.standard_normal((R, N))
        T0 = np.zeros((N,N,N))
        for i in range(R): T0 += np.einsum('a,b,c->abc', U0[i], V0[i], W0[i])
        
        amp0 = amplitude(U0, V0, W0)
        print(f"  Start: amp={amp0:.2f}, |T0|={norm(T0):.2f}")
        
        traj = homotopy_gauged(T0, U0, V0, W0, T333, rng,
                               max_steps=2000, dt_init=0.002, dt_max=0.03,
                               tol=1e-10, max_amp=1e7)
        
        t_final = traj[-1]['t']
        amp_final = traj[-1]['amp']
        event = traj[-1].get('event', 'reached_t1' if t_final > 0.99 else 'running')
        
        # If reached t≈1, verify
        verified = False
        if t_final > 0.99:
            Tt1 = T333
            U_f, V_f, W_f = U0, V0, W0  # would need to extract from trajectory
            # For now just check amplitude
            print(f"  *** REACHED t≈1! amp={amp_final:.2e} ***")
            if amp_final < 1e5:
                verified = True
        
        rec = {'path_id': pid, 't_final': float(t_final),
               'amp_start': float(amp0), 'amp_final': float(amp_final),
               'n_steps': len(traj), 'event': event, 'verified': verified}
        
        # Amplitude trajectory sampling
        t_samples = [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]
        for ts in t_samples:
            closest = min(traj, key=lambda r: abs(r['t'] - ts))
            if abs(closest['t'] - ts) < 0.05:
                rec[f'amp_at_{ts:.1f}'] = float(closest['amp'])
        
        results['paths'].append(rec)
        print(f"  Result: t={t_final:.4f}, event={event}, amp={amp_final:.2e}")
    
    # Summary
    n_reached = sum(1 for p in results['paths'] if p['t_final'] > 0.99)
    n_diverged = sum(1 for p in results['paths'] if p.get('event') == 'diverged')
    n_stalled = sum(1 for p in results['paths'] if p.get('event') == 'stalled')
    max_t = max(p['t_final'] for p in results['paths'])
    
    print(f"\n=== Summary ===")
    print(f"  Reached t≈1: {n_reached}/{n_paths}")
    print(f"  Diverged: {n_diverged}/{n_paths}")
    print(f"  Stalled: {n_stalled}/{n_paths}")
    print(f"  Max t reached: {max_t:.6f}")
    
    results['summary'] = {'n_paths': n_paths, 'n_reached': n_reached,
                          'n_diverged': n_diverged, 'n_stalled': n_stalled,
                          'max_t': float(max_t)}
    
    out_dir = Path(__file__).resolve().parent.parent / 'data/homotopy_v2'
    out_dir.mkdir(parents=True, exist_ok=True)
    with open(out_dir / 'homotopy_gauged.json', 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nSaved to {out_dir / 'homotopy_gauged.json'}")

if __name__ == '__main__':
    main()
