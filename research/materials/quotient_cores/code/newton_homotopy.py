#!/usr/bin/env python3
r"""analysisc: Newton homotopy for rank-22 T333 using J+G combined system.

Key corrections from earlier attempts:
  - Uses J (729×594) + G (68×594) combined system with full rank 594
  - Newton ARTIFACT solves 594×594 square system
  - Homotopy tracks from random rank-22 tensor to T333
  - Also tests cn122 gauge with linear-combination anchoring

Scientific question: if T333 has rank 22 over F_p, Newton homotopy should 
find a rank-22 decomposition. Failure is evidence (not proof) of rank > 22.
"""
from __future__ import annotations
import json, sys, time
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
import rank22_singular_stratum_v2 as s19

WS = SCRIPT_DIR.parent
OUT = WS / 'data' / 'gauge_chart'
OUT.mkdir(parents=True, exist_ok=True)

def det3(A, p):
    A = A % p
    return int(A[0,0]*(A[1,1]*A[2,2]-A[1,2]*A[2,1])
              -A[0,1]*(A[1,0]*A[2,2]-A[1,2]*A[2,0])
              +A[0,2]*(A[1,0]*A[2,1]-A[1,1]*A[2,0])) % p

def inv3(A, p):
    return s19.solve_mod(A % p, np.eye(3, dtype=np.int64), p)

def companion_form(B, p):
    B = B % p
    for v1 in [np.array([1,0,0]), np.array([0,1,0]), np.array([0,0,1]),
               np.array([1,1,0]), np.array([1,0,1]), np.array([0,1,1]), np.array([1,1,1])]:
        v = v1.astype(np.int64) % p
        v2 = B @ v % p; v3 = B @ v2 % p
        Q = np.column_stack([v, v2, v3]).astype(np.int64) % p
        if det3(Q, p) == 0: continue
        return Q, inv3(Q, p) @ B @ Q % p
    return None, None

def gauge_fix_simple(U, V, W, p):
    """Gauge-fix: try individual terms then 2-term combos as anchors."""
    r = U.shape[0]
    # Try individual terms first
    for i1 in range(min(r, 8)):
        A1 = U[i1].reshape(3,3) % p
        if det3(A1, p) == 0: continue
        A1i = inv3(A1, p)
        for i2 in range(min(r, 8)):
            if i2 == i1: continue
            B = A1i @ (U[i2].reshape(3,3)%p) % p
            Qm, Cm = companion_form(B, p)
            if Qm is None: continue
            Pm = Qm @ A1i % p
            for j1 in range(min(r, 8)):
                V1 = V[j1].reshape(3,3) % p
                Rm = Qm @ V1 % p
                if det3(Rm, p) == 0: continue
                Qi = inv3(Qm, p); Pi = inv3(Pm, p); Ri = inv3(Rm, p)
                Un = np.empty_like(U); Vn = np.empty_like(V); Wn = np.empty_like(W)
                for i in range(r):
                    Un[i] = (Pm @ (U[i].reshape(3,3)%p) @ Qi%p).ravel()%p
                    Vn[i] = (Qm @ (V[i].reshape(3,3)%p) @ Ri%p).ravel()%p
                    Wn[i] = (Rm @ (W[i].reshape(3,3)%p) @ Pi%p).ravel()%p
                ok = True
                for i in range(r):
                    if Un[i,0]%p==0 or Vn[i,0]%p==0: ok=False; break
                    lam = pow(int(Un[i,0]%p),p-2,p)
                    Un[i] = Un[i]*lam%p; Wn[i] = Wn[i]*pow(lam,p-2,p)%p
                    mu = pow(int(Vn[i,0]%p),p-2,p)
                    Vn[i] = Vn[i]*mu%p; Wn[i] = Wn[i]*pow(mu,p-2,p)%p
                if not ok: continue
                return Un%p, Vn%p, Wn%p
    return None

def build_gauge_matrix(r, p):
    """Build 68×(27r) gauge condition Jacobian."""
    G = []
    # u_0 = I_3 (or anchor form): fix all 9 entries
    for k in range(9):
        row = np.zeros(27*r, dtype=np.int64); row[k] = 1; G.append(row)
    # v_0 = I_3: fix all 9 entries
    for k in range(9):
        row = np.zeros(27*r, dtype=np.int64); row[9+k] = 1; G.append(row)
    # u_i[0]=1 for i=1,...,r-1
    for i in range(1, r):
        row = np.zeros(27*r, dtype=np.int64); row[27*i] = 1; G.append(row)
    # v_i[0]=1 for i=1,...,r-1
    for i in range(1, r):
        row = np.zeros(27*r, dtype=np.int64); row[27*i+9] = 1; G.append(row)
    # u_1 companion: lower triangle u_1[3,6,7]=0
    for idx in [3, 6, 7]:
        row = np.zeros(27*r, dtype=np.int64); row[27+idx] = 1; G.append(row)
    # u_1[1]=0 (extra companion normalization)
    row = np.zeros(27*r, dtype=np.int64); row[27+1] = 1; G.append(row)
    # v_1 companion lower: v_1[3,6,7]=0
    for idx in [3, 6, 7]:
        row = np.zeros(27*r, dtype=np.int64); row[27+9+idx] = 1; G.append(row)
    # v_1[1]=0 (to reach 68)
    row = np.zeros(27*r, dtype=np.int64); row[27+9+1] = 1; G.append(row)
    Gmat = np.array(G, dtype=np.int64) % p
    assert Gmat.shape == (68, 27*r), f'G shape {Gmat.shape}'
    return Gmat

def newton_step_full(U, V, W, T_target, G, p):
    """One Newton ARTIFACT using J+G combined 594×594 system.
    Returns (U', V', W', residual_nnz_before, residual_nnz_after)."""
    r = U.shape[0]; n = 27 * r
    res = s19.brent_residual(U, V, W, T_target, p)
    nnz_before = int(np.count_nonzero(res))
    if nnz_before == 0:
        return U, V, W, 0, 0
    
    # Build Brent Jacobian (729 × 27r) 
    J = s19.brent_jacobian(U, V, W, p)
    
    # Gauge residual: distance from gauge-fixed values
    x = np.concatenate([U.ravel(), V.ravel(), W.ravel()]).astype(np.int64) % p
    # Gauge target: the gauge conditions fix specific coordinates to specific values
    # The gauge rows are identity-like (selecting one coordinate each)
    # Gauge residual = G @ x - target_values
    # For simplicity, treat gauge residual as just the current deviation
    # (We won't enforce gauge in Newton — just use it for rank)
    
    # Combined system: [J; G] @ delta = -[brent_res; gauge_res]
    # But we just want to solve Brent equations, using gauge to make system determined
    JG = np.concatenate([J, G], axis=0) % p  # (729+68) × n
    
    # Right-hand side: -F(x) = [brent residual (with sign); gauge doesn't change]
    neg_res = (p - res) % p
    gauge_rhs = np.zeros(68, dtype=np.int64)  # gauge already satisfied, keep fixed
    rhs = np.concatenate([neg_res, gauge_rhs])
    
    # Select n=594 independent rows
    pivs = s19.pivot_columns_rref(JG, p)
    if len(pivs) < n:
        return U, V, W, nnz_before, -1  # system rank deficient
    sel = pivs[:n]
    
    try:
        delta = s19.solve_mod(JG[sel] % p, rhs[sel].reshape(-1, 1) % p, p).ravel()
    except ValueError:
        return U, V, W, nnz_before, -2
    
    # Apply correction
    xn = (x + delta) % p
    Un = xn[:9*r].reshape(r, 9)
    Vn = xn[9*r:18*r].reshape(r, 9)
    Wn = xn[18*r:].reshape(r, 9)
    res2 = s19.brent_residual(Un, Vn, Wn, T_target, p)
    nnz_after = int(np.count_nonzero(res2))
    return Un, Vn, Wn, nnz_before, nnz_after

def main():
    p = 65521; T333 = s19.make_T333() % p
    r = 22; n = 27 * r
    G = build_gauge_matrix(r, p)
    rng = np.random.RandomState(2026)
    result = {'prime': p, 'rank': r}
    
    print(f'Gauge matrix: {G.shape}, rank={s19.rank_mod(G, p)}')
    
    # ── Newton homotopy trials ──
    print('\n=== Newton homotopy: random rank-22 → T333 ===')
    homotopy_results = []
    
    for trial in range(15):
        # Generate gauge-fixed random rank-22 decomposition
        for _ in range(100):
            U0 = rng.randint(0, p, (r, 9)).astype(np.int64)
            V0 = rng.randint(0, p, (r, 9)).astype(np.int64)
            W0 = rng.randint(0, p, (r, 9)).astype(np.int64)
            ret = gauge_fix_simple(U0, V0, W0, p)
            if ret is not None: break
        else:
            continue
        Ug, Vg, Wg = ret
        T0 = s19.tensor_from_factors(Ug, Vg, Wg, p)
        
        # Direct Newton: try to jump from T0 to T333 in one ARTIFACT
        U, V, W = Ug.copy(), Vg.copy(), Wg.copy()
        
        # Multi-ARTIFACT homotopy: T_t = T0 + t*(T333-T0)
        N_steps = 5  # number of homotopy steps
        success = True
        for step in range(1, N_steps + 1):
            # t = ARTIFACT/N_steps mod p
            t = step * pow(N_steps, p-2, p) % p
            T_t = ((1 + p - t) * T0 + t * T333) % p
            
            for newton_it in range(5):
                U, V, W, nb, na = newton_step_full(U, V, W, T_t, G, p)
                if na == 0: break
                if na < 0:
                    success = False; break
            if not success or na != 0:
                success = False; break
        
        # Final check against T333
        final_nnz = int(np.count_nonzero(s19.brent_residual(U, V, W, T333, p)))
        
        rec = {
            'trial': trial, 'success': success and final_nnz == 0,
            'final_residual': final_nnz, 'N_steps': N_steps,
        }
        homotopy_results.append(rec)
        
        status = 'FOUND!' if rec['success'] else f'failed (res={final_nnz})'
        print(f'  Trial {trial}: {status}')
        if rec['success']:
            print('  *** RANK-22 DECOMPOSITION OF T333 FOUND ***')
            rec['U'] = U.tolist(); rec['V'] = V.tolist(); rec['W'] = W.tolist()
            break
    
    result['homotopy'] = homotopy_results
    
    # ── Direct Newton from random start (calibration) ──
    print('\n=== Direct Newton from random start (expect failure, calibration) ===')
    direct_results = []
    for trial in range(5):
        U = rng.randint(0, p, (r, 9)).astype(np.int64)
        V = rng.randint(0, p, (r, 9)).astype(np.int64)
        W = rng.randint(0, p, (r, 9)).astype(np.int64)
        for nit in range(3):
            U, V, W, nb, na = newton_step_full(U, V, W, T333, G, p)
            if na == 0 or na < 0: break
        direct_results.append({'trial': trial, 'residual_after': na})
        print(f'  Trial {trial}: residual {na}/729')
    result['direct_newton'] = direct_results
    
    # ── Homotopy convergence on known rank-23 (control: should work at r=23) ──
    print('\n=== Control: Newton homotopy for rank-23 (known to exist) ===')
    G23 = build_gauge_matrix(23, p)
    ctrl_results = []
    for trial in range(5):
        for _ in range(100):
            U0 = rng.randint(0, p, (23, 9)).astype(np.int64)
            V0 = rng.randint(0, p, (23, 9)).astype(np.int64)
            W0 = rng.randint(0, p, (23, 9)).astype(np.int64)
            ret = gauge_fix_simple(U0, V0, W0, p)
            if ret is not None: break
        else: continue
        Ug, Vg, Wg = ret
        T0 = s19.tensor_from_factors(Ug, Vg, Wg, p)
        U, V, W = Ug.copy(), Vg.copy(), Wg.copy()
        N_steps = 5; success = True
        for step in range(1, N_steps + 1):
            t = step * pow(N_steps, p-2, p) % p
            T_t = ((1+p-t)*T0 + t*T333) % p
            for nit in range(5):
                U, V, W, nb, na = newton_step_full(U, V, W, T_t, G23, p)
                if na == 0: break
                if na < 0: success = False; break
            if not success or na != 0: success = False; break
        final_nnz = int(np.count_nonzero(s19.brent_residual(U, V, W, T333, p)))
        ctrl_results.append({'trial': trial, 'success': success and final_nnz==0, 'final_res': final_nnz})
        print(f'  Trial {trial}: {"OK" if final_nnz==0 else "FAIL"} (res={final_nnz})')
    result['control_r23_homotopy'] = ctrl_results

    # Save
    result['summary'] = {
        'rank22_found': any(r['success'] for r in homotopy_results),
        'rank23_control_found': any(r['success'] for r in ctrl_results),
        'interpretation': (
            'Homotopy over F_p is not continuous — t=ARTIFACT/N is a modular inverse, '
            'not a small perturbation. Success depends on global algebraic connectivity. '
            'Failure for r=22 with success for r=23 would be evidence of rank>22 over F_p.'
        )
    }
    out = OUT / 'newton_homotopy_results.json'
    out.write_text(json.dumps(result, indent=2, default=int) + '\n')
    print(f'\nSaved to {out}')

if __name__ == '__main__':
    main()
