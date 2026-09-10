#!/usr/bin/env python3
r"""analysisb (fixed): Gauge chart for rank-22 T333 with multi-anchor selection.

Fixes from first run:
  - Try multiple term pairs for (anchor1, anchor2) when first choice fails
  - Remove incorrect tensor-check for non-T333 controls
  - Correctly distinguish T333 decompositions from random-tensor decompositions
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
        Qi = inv3(Q, p)
        C = Qi @ B @ Q % p
        return Q, C
    rng = np.random.RandomState(777)
    for _ in range(100):
        v = rng.randint(0, p, 3).astype(np.int64)
        v2 = B @ v % p; v3 = B @ v2 % p
        Q = np.column_stack([v, v2, v3]).astype(np.int64) % p
        if det3(Q, p) == 0: continue
        return Q, inv3(Q, p) @ B @ Q % p
    return None, None

def gauge_fix(U, V, W, p):
    """Multi-anchor gauge fix. Tries all (i1, i2, j1) anchor triples."""
    r = U.shape[0]
    for i1 in range(r):
        A1 = U[i1].reshape(3,3) % p
        if det3(A1, p) == 0: continue
        A1i = inv3(A1, p)
        for i2 in range(r):
            if i2 == i1: continue
            B = A1i @ (U[i2].reshape(3,3) % p) % p
            Qmat, Cmat = companion_form(B, p)
            if Qmat is None: continue
            Pmat = Qmat @ A1i % p
            for j1 in range(r):
                V1 = V[j1].reshape(3,3) % p
                Rmat = Qmat @ V1 % p
                if det3(Rmat, p) == 0: continue
                Qi = inv3(Qmat, p); Pi = inv3(Pmat, p); Ri = inv3(Rmat, p)
                Un = np.empty_like(U); Vn = np.empty_like(V); Wn = np.empty_like(W)
                for i in range(r):
                    Un[i] = (Pmat @ (U[i].reshape(3,3)%p) @ Qi % p).ravel() % p
                    Vn[i] = (Qmat @ (V[i].reshape(3,3)%p) @ Ri % p).ravel() % p
                    Wn[i] = (Rmat @ (W[i].reshape(3,3)%p) @ Pi % p).ravel() % p
                # term scalings: u_k[0]=1, v_k[0]=1 for all k except anchor
                ok = True
                for i in range(r):
                    if Un[i,0] % p == 0 or Vn[i,0] % p == 0:
                        ok = False; break
                    lam = pow(int(Un[i,0]%p), p-2, p)
                    Un[i] = Un[i]*lam%p; Wn[i] = Wn[i]*pow(lam,p-2,p)%p
                    mu = pow(int(Vn[i,0]%p), p-2, p)
                    Vn[i] = Vn[i]*mu%p; Wn[i] = Wn[i]*pow(mu,p-2,p)%p
                if not ok: continue
                # Verify anchor normalizations
                u1_check = Un[i1].reshape(3,3) % p
                v1_check = Vn[j1].reshape(3,3) % p
                return Un%p, Vn%p, Wn%p, {
                    'anchor_u': (int(i1), int(i2)),
                    'anchor_v': int(j1),
                    'u_anchor1_is_I3': bool(np.allclose(u1_check, np.eye(3))),
                    'companion': Cmat.tolist(),
                    'all_u0_one': bool(all(int(Un[k,0])%p==1 for k in range(r))),
                    'all_v0_one': bool(all(int(Vn[k,0])%p==1 for k in range(r))),
                }
    return None

def sparse_pi(p):
    from projected_kernel_model import sparse_t333_quotient_matrix
    return sparse_t333_quotient_matrix(p)

def main():
    p = 65521; T333 = s19.make_T333() % p
    pi = sparse_pi(p)
    result = {'prime': p}; rng = np.random.RandomState(42)

    # 1. Gauge-fix random rank-22 controls
    print('=== Gauge-fixing random rank-22 controls (30 trials) ===')
    good = 0; fail = 0; controls = []
    for trial in range(30):
        U = rng.randint(0, p, (22, 9)).astype(np.int64)
        V = rng.randint(0, p, (22, 9)).astype(np.int64)
        W = rng.randint(0, p, (22, 9)).astype(np.int64)
        ret = gauge_fix(U, V, W, p)
        if ret is None: fail += 1; continue
        Ug, Vg, Wg, ginfo = ret
        good += 1
        # Check Brent against the TRANSFORMED tensor
        Tg = s19.tensor_from_factors(Ug, Vg, Wg, p)
        brent_nnz = int(np.count_nonzero(s19.brent_residual(Ug, Vg, Wg, Tg, p)))
        # Jacobian rank
        J = s19.brent_jacobian(Ug, Vg, Wg, p)
        j_rank = int(s19.rank_mod(J, p))
        # projected-kernel rank (against TRANSFORMED tensor, NOT T333)
        pir = int(s19.rank_mod((pi @ s19.pairing_matrix(Ug, Vg, p))%p, p))
        controls.append({
            'trial': trial, 'brent_ok': brent_nnz==0, 'J_rank': j_rank,
            'pi_rank_vs_Tg': pir, 'ginfo': ginfo,
        })
        if good <= 5:
            print(f'  trial {trial}: J_rank={j_rank}, pi_rank={pir}, '
                  f'anchors=({ginfo["anchor_u"]},{ginfo["anchor_v"]}), '
                  f'u0=1:{ginfo["all_u0_one"]}, v0=1:{ginfo["all_v0_one"]}')
    result['gauge_fix'] = {'good': good, 'fail': fail, 'controls': controls[:5]}
    print(f'  Success: {good}/{good+fail}')

    # 2. Gauge-fix cn122 (rank-23 decomposition OF T333)
    print('\n=== Gauge-fixing cn122 rank-23 ===')
    cnU, cnV, cnW = s19.load_qmm(WS/'data/cn122_r23_reproduce/scheme.qmm')
    ret23 = gauge_fix(cnU%p, cnV%p, cnW%p, p)
    if ret23:
        U23, V23, W23, gi23 = ret23
        brent23 = int(np.count_nonzero(s19.brent_residual(U23, V23, W23, T333, p)))
        J23 = s19.brent_jacobian(U23, V23, W23, p)
        j23 = int(s19.rank_mod(J23, p))
        pi23 = int(s19.rank_mod((pi @ s19.pairing_matrix(U23, V23, p))%p, p))
        result['cn122'] = {
            'brent_residual_nnz': brent23, 'J_rank': j23, 'pi_rank': pi23,
            'anchors': gi23['anchor_u'], 'v_anchor': gi23['anchor_v'],
        }
        print(f'  cn122: brent_nnz={brent23}, J_rank={j23}, pi_rank={pi23}, '
              f'anchors=({gi23["anchor_u"]},{gi23["anchor_v"]})')
    else:
        result['cn122'] = 'gauge_fix_failed'
        print('  FAILED')

    # 3. Combined J+gauge rank on generic controls (the isolated-solution test)
    print('\n=== Combined J+G rank test (generic rank-22 controls) ===')
    jg_results = []
    for trial in range(10):
        U = rng.randint(0, p, (22, 9)).astype(np.int64)
        V = rng.randint(0, p, (22, 9)).astype(np.int64)
        W = rng.randint(0, p, (22, 9)).astype(np.int64)
        ret = gauge_fix(U, V, W, p)
        if ret is None: continue
        Ug, Vg, Wg, _ = ret
        J = s19.brent_jacobian(Ug, Vg, Wg, p)
        # Build coordinate-gauge rows (68 total)
        r = 22; G = []
        for k in range(9):  # u_anchor1 = I_3 (9 conditions)
            row = np.zeros(27*r, dtype=np.int64); row[0+k]=1; G.append(row)
        for k in range(9):  # v_anchor1 = I_3 (9 conditions)
            row = np.zeros(27*r, dtype=np.int64); row[9+k]=1; G.append(row)
        for i in range(r):  # u_i[0]=1 (22 conditions)
            row = np.zeros(27*r, dtype=np.int64); row[27*i]=1; G.append(row)
        for i in range(r):  # v_i[0]=1 (22 conditions)
            row = np.zeros(27*r, dtype=np.int64); row[27*i+9]=1; G.append(row)
        # u_anchor2 companion: lower triangle (3) + u2[1]=0 (1)
        for idx in [3,6,7]:
            row = np.zeros(27*r, dtype=np.int64); row[27*1+idx]=1; G.append(row)
        row = np.zeros(27*r, dtype=np.int64); row[27*1+1]=1; G.append(row)
        # v_anchor2 lower triangle (3)
        for idx in [3,6,7]:
            row = np.zeros(27*r, dtype=np.int64); row[27*1+9+idx]=1; G.append(row)
        Gmat = np.array(G, dtype=np.int64) % p
        g_rank = int(s19.rank_mod(Gmat, p))
        JG = np.concatenate([J, Gmat], axis=0) % p
        jg_rank = int(s19.rank_mod(JG, p))
        j_rank = int(s19.rank_mod(J, p))
        jg_results.append({'J':j_rank, 'G':g_rank, 'JG':jg_rank, 'n':27*r, 'full':jg_rank==27*r})
        if len(jg_results) <= 3:
            print(f'  J={j_rank} G={g_rank} J+G={jg_rank}/{27*r} full={jg_rank==27*r}')
    result['combined_JG'] = jg_results

    # 4. Key diagnostic: Newton homotopy from one gauge-fixed rank-22 of random tensor 
    #    toward T333 using the FULL Newton system
    print('\n=== Newton homotopy (1 path, from gauged random rank-22 toward T333) ===')
    for attempt in range(50):
        U = rng.randint(0, p, (22, 9)).astype(np.int64)
        V = rng.randint(0, p, (22, 9)).astype(np.int64)
        W = rng.randint(0, p, (22, 9)).astype(np.int64)
        ret = gauge_fix(U, V, W, p)
        if ret is None: continue
        Ug, Vg, Wg, _ = ret
        T0 = s19.tensor_from_factors(Ug, Vg, Wg, p)
        # One Newton ARTIFACT toward T333 (full ARTIFACT, t=0→1)
        res = (T333.ravel() - s19.tensor_from_factors(Ug, Vg, Wg, p).ravel()) % p
        print(f'  Attempt {attempt}: initial Brent residual vs T333 = {np.count_nonzero(res)}/729')
        # Try Newton correction
        J = s19.brent_jacobian(Ug, Vg, Wg, p)
        j_rank = int(s19.rank_mod(J, p))
        neg_res = (p - res) % p
        # Select j_rank independent rows
        pivs = s19.pivot_columns_rref(J, p)[:min(j_rank, 27*22)]
        if len(pivs) < 27*22:
            print(f'    J rank {j_rank} < {27*22}, system underdetermined. Picking {len(pivs)} rows.')
        # Solve subsystem
        J_sub = J[pivs] % p
        r_sub = neg_res[pivs].reshape(-1, 1) % p
        try:
            delta = s19.solve_mod(J_sub, r_sub, p).ravel()
        except ValueError:
            print(f'    Solve failed (singular subsystem)'); break
        # Apply correction
        r22 = 22
        Uc = (Ug.ravel() + delta[:9*r22]) % p
        Vc = (Vg.ravel() + delta[9*r22:18*r22]) % p
        Wc = (Wg.ravel() + delta[18*r22:]) % p
        Uc = Uc.reshape(r22, 9); Vc = Vc.reshape(r22, 9); Wc = Wc.reshape(r22, 9)
        res2 = s19.brent_residual(Uc, Vc, Wc, T333, p)
        print(f'    After Newton ARTIFACT: residual = {np.count_nonzero(res2)}/729')
        if np.count_nonzero(res2) == 0:
            print('    *** FOUND RANK-22 DECOMPOSITION OF T333! ***')
        break

    # 5. Save
    result['summary'] = {
        'gauge_chart_works': good > 0,
        'generic_JG_full_rank': all(x['full'] for x in jg_results) if jg_results else False,
        'cn122_gauged': 'cn122' in result and result['cn122'] != 'gauge_fix_failed',
    }
    out = OUT / 'gauge_chart_calibration.json'
    out.write_text(json.dumps(result, indent=2, default=int) + '\n')
    print(f'\nSaved to {out}')

if __name__ == '__main__':
    main()
