#!/usr/bin/env python3
r"""analysis: Modular Newton homotopy for rank-22 decomposition of T_{333}.

Two experiments:
  1. Homotopy from random rank-22 tensor decompositions to T_{333}
  2. Multi-start Newton from random points for T_{333}

Over F_p (p < 2^16), using vectorized int64 Gaussian elimination.
If T_{333} has rank 22 over F_p, the homotopy should succeed with high
probability for generic starting tensors. Consistent failure across
multiple primes is strong (but not conclusive) evidence for rank > 22.
"""
import numpy as np
import json, sys, time
from pathlib import Path
from math import comb

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'modular_newton'
OUT.mkdir(parents=True, exist_ok=True)

# ---------- tensor and system ----------

def build_T333(p):
    T = np.zeros((9,9,9), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T % p

def load_cn122(p):
    """Load cn122 rank-23 QMM scheme."""
    path = WS / 'data' / 'cn122_r23_reproduce' / 'scheme.qmm'
    U, V, W = [], [], []
    with open(path) as f:
        lines = f.readlines()
    idx = 0
    while idx < len(lines):
        line = lines[idx].strip()
        if line.startswith('term'):
            u = list(map(int, lines[idx+1].split()[1:]))
            v = list(map(int, lines[idx+2].split()[1:]))
            w = list(map(int, lines[idx+3].split()[1:]))
            U.append(u); V.append(v); W.append(w)
            idx += 4
        else:
            idx += 1
    return (np.array(U, dtype=np.int64) % p,
            np.array(V, dtype=np.int64) % p,
            np.array(W, dtype=np.int64) % p)

def brent_residual(U, V, W, T, p):
    """Flat 729-vector of T - sum u_i⊗v_i⊗w_i mod p."""
    r = U.shape[0]
    R = T.reshape(-1).copy()
    for i in range(r):
        R -= np.einsum('a,b,c->abc', U[i], V[i], W[i]).reshape(-1)
    return R % p

def brent_jacobian(U, V, W, p):
    """729 × 27r Jacobian. J[abc, 27i+a'] = -delta(a,a')v_{ib}w_{ic} etc."""
    r = U.shape[0]
    J = np.zeros((729, 27*r), dtype=np.int64)
    for i in range(r):
        vw = np.outer(V[i], W[i]).ravel() % p   # 81
        uw = np.outer(U[i], W[i])               # 9×9
        uv = np.outer(U[i], V[i])               # 9×9
        for a in range(9):
            J[81*a:81*a+81, 27*i+a] = (p - vw) % p
        for b in range(9):
            for a2 in range(9):
                J[81*a2+9*b:81*a2+9*b+9, 27*i+9+b] = (p - U[i,a2]*W[i]) % p
        for c in range(9):
            rows_c = np.array([81*aa+9*bb+c for aa in range(9) for bb in range(9)])
            vals_c = (p - uv.ravel()) % p   # 81
            J[rows_c, 27*i+18+c] = vals_c
    return J % p

# ---------- linear algebra over F_p ----------

def gauss_solve(A, b, p):
    """Solve Ax=b over F_p (A is n×n). Returns None if singular."""
    n = A.shape[0]
    Ab = np.hstack([A.astype(np.int64) % p, b.reshape(-1,1).astype(np.int64) % p])
    piv_order = []
    for col in range(n):
        pivot = None
        for row in range(col, n):
            if Ab[row, col] % p != 0:
                pivot = row; break
        if pivot is None:
            return None
        if pivot != col:
            Ab[[col, pivot]] = Ab[[pivot, col]]
        inv_val = pow(int(Ab[col, col] % p), p-2, p)
        Ab[col] = Ab[col] * inv_val % p
        factors = Ab[:, col].copy(); factors[col] = 0
        Ab = (Ab - np.outer(factors, Ab[col])) % p
    return Ab[:, -1] % p

def select_independent_rows(M, n_needed, p):
    """Select n_needed independent rows from M over F_p. Returns row indices."""
    m, n = M.shape
    selected = []
    pivots_used = set()
    for row in range(m):
        if len(selected) >= n_needed:
            break
        # Check if this row is independent of selected rows
        if len(selected) == 0:
            # Find first nonzero entry
            for j in range(n):
                if M[row, j] % p != 0:
                    selected.append(row)
                    pivots_used.add(j)
                    break
        else:
            # Reduce this row by selected rows (too expensive for full check)
            # Just add it and let Gaussian elimination handle singularity
            selected.append(row)
    return selected[:n_needed]

# ---------- Newton ARTIFACT ----------

def newton_step(U, V, W, T, gauge_G, gauge_g, p, cached_rows=None):
    """One Newton ARTIFACT. Returns (U_new, V_new, W_new, converged, row_cache)."""
    r = U.shape[0]
    nvar = 27 * r
    
    # Residual
    F = brent_residual(U, V, W, T, p)     # 729
    theta = np.concatenate([U.ravel(), V.ravel(), W.ravel()]) % p
    G_res = (gauge_G @ theta - gauge_g) % p  # n_gauge
    
    if np.all(F == 0) and np.all(G_res == 0):
        return U, V, W, True, cached_rows
    
    # Jacobian
    J = brent_jacobian(U, V, W, p)        # 729 × nvar
    
    # Augmented system
    n_gauge = gauge_G.shape[0]
    A_full = np.vstack([J, gauge_G]) % p   # (729+n_gauge) × nvar
    b_full = np.concatenate([(p - F) % p, (p - G_res) % p]) % p
    
    # Select nvar independent rows
    # Use gauge rows first (they're designed to fill the kernel)
    n_brent = 729
    # Take all gauge rows + first (nvar - n_gauge) Brent rows
    n_brent_needed = nvar - n_gauge
    rows = list(range(n_brent, n_brent + n_gauge))  # gauge rows first
    rows += list(range(min(n_brent_needed, n_brent)))  # then Brent rows
    if len(rows) < nvar:
        rows += list(range(n_brent_needed, n_brent))
    rows = rows[:nvar]
    
    A_sq = A_full[rows] % p
    b_sq = b_full[rows] % p
    
    delta = gauss_solve(A_sq, b_sq, p)
    if delta is None:
        # Try different row selection
        perm = np.random.permutation(n_brent + n_gauge)
        for start in range(0, len(perm) - nvar, 50):
            rows2 = sorted(perm[start:start+nvar])
            delta = gauss_solve(A_full[rows2] % p, b_full[rows2] % p, p)
            if delta is not None:
                break
        if delta is None:
            return U, V, W, False, cached_rows
    
    # Update
    theta_new = (theta + delta) % p
    U_new = theta_new[:9*r].reshape(r, 9)
    V_new = theta_new[9*r:18*r].reshape(r, 9)
    W_new = theta_new[18*r:].reshape(r, 9)
    return U_new % p, V_new % p, W_new % p, False, rows

# ---------- experiments ----------

def random_rank_r_tensor(r, p, rng):
    """Generate random rank-r tensor with known decomposition over F_p."""
    U = rng.integers(0, p, (r, 9)).astype(np.int64)
    V = rng.integers(0, p, (r, 9)).astype(np.int64)
    W = rng.integers(0, p, (r, 9)).astype(np.int64)
    T = np.zeros((9,9,9), dtype=np.int64)
    for i in range(r):
        T = (T + np.einsum('a,b,c->abc', U[i], V[i], W[i])) % p
    return T, U, V, W

def run_homotopy(T_start, U0, V0, W0, T_target, n_steps, max_newton, p, rng):
    """Track solution from T_start to T_target."""
    U, V, W = U0.copy(), V0.copy(), W0.copy()
    r = U.shape[0]
    nvar = 27 * r
    
    # Gauge: random linear, anchored at starting point
    n_gauge = 44
    gauge_G = rng.integers(0, p, (n_gauge, nvar)).astype(np.int64)
    theta0 = np.concatenate([U.ravel(), V.ravel(), W.ravel()]) % p
    gauge_g = (gauge_G @ theta0) % p
    
    # Verify starting solution
    res0 = brent_residual(U, V, W, T_start, p)
    if not np.all(res0 == 0):
        return {"status": "bad_start", "start_res": int(np.count_nonzero(res0))}
    
    inv_n = pow(n_steps, p-2, p)
    dT = (T_target.astype(np.int64) - T_start.astype(np.int64)) % p
    
    cache = None
    for k in range(1, n_steps + 1):
        t = k * inv_n % p
        T_cur = (T_start + t * dT) % p
        
        converged = False
        for nit in range(max_newton):
            U, V, W, converged, cache = newton_step(U, V, W, T_cur, gauge_G, gauge_g, p, cache)
            if converged:
                break
            # Check residual
            res = brent_residual(U, V, W, T_cur, p)
            if np.all(res == 0):
                converged = True
                break
        
        if not converged:
            return {"status": "newton_fail", "failed_at_step": k, "n_steps": n_steps,
                    "nonzero_residual": int(np.count_nonzero(brent_residual(U, V, W, T_cur, p)))}
    
    # Verify final solution
    res_final = brent_residual(U, V, W, T_target, p)
    if np.all(res_final == 0):
        return {"status": "SUCCESS", "U": U.tolist(), "V": V.tolist(), "W": W.tolist()}
    else:
        return {"status": "drift", "final_nonzero": int(np.count_nonzero(res_final))}

def run_multistart_newton(T_target, r, n_starts, max_newton, p, rng):
    """Random-start Newton on T_target."""
    nvar = 27 * r
    n_gauge = 44
    successes = []
    
    for trial in range(n_starts):
        U = rng.integers(0, p, (r, 9)).astype(np.int64)
        V = rng.integers(0, p, (r, 9)).astype(np.int64)
        W = rng.integers(0, p, (r, 9)).astype(np.int64)
        
        gauge_G = rng.integers(0, p, (n_gauge, nvar)).astype(np.int64)
        theta0 = np.concatenate([U.ravel(), V.ravel(), W.ravel()]) % p
        gauge_g = (gauge_G @ theta0) % p
        
        for nit in range(max_newton):
            U, V, W, conv, _ = newton_step(U, V, W, T_target, gauge_G, gauge_g, p)
            if conv:
                successes.append({"trial": trial, "nit": nit})
                break
            res = brent_residual(U, V, W, T_target, p)
            if np.all(res == 0):
                successes.append({"trial": trial, "nit": nit})
                break
    
    return successes

def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--prime', type=int, default=65521)
    parser.add_argument('--rank', type=int, default=22)
    parser.add_argument('--homotopy-paths', type=int, default=20)
    parser.add_argument('--homotopy-steps', type=int, default=100)
    parser.add_argument('--newton-starts', type=int, default=100)
    parser.add_argument('--max-newton', type=int, default=30)
    parser.add_argument('--seed', type=int, default=2026)
    parser.add_argument('--pilot', action='store_true')
    args = parser.parse_args()
    
    p = args.prime
    r = args.rank
    rng = np.random.default_rng(args.seed)
    
    if args.pilot:
        args.homotopy_paths = 2
        args.homotopy_steps = 20
        args.newton_starts = 10
    
    print(f"=== Modular Newton homotopy: p={p}, r={r} ===")
    
    T333 = build_T333(p)
    print(f"T333 nnz={np.count_nonzero(T333)}")
    
    # --- Timing pilot ---
    print("\n--- Timing pilot ---")
    t0 = time.time()
    T_rand, U_rand, V_rand, W_rand = random_rank_r_tensor(r, p, rng)
    n_gauge = 44; nvar = 27*r
    gauge_G = rng.integers(0, p, (n_gauge, nvar)).astype(np.int64)
    theta = np.concatenate([U_rand.ravel(), V_rand.ravel(), W_rand.ravel()]) % p
    gauge_g = (gauge_G @ theta) % p
    
    res = brent_residual(U_rand, V_rand, W_rand, T_rand, p)
    print(f"Random rank-{r} residual: {np.count_nonzero(res)} nonzero (expect 0)")
    
    # Time one Newton ARTIFACT
    t1 = time.time()
    U_pert = (U_rand + rng.integers(-10, 11, U_rand.shape)) % p
    V_pert = (V_rand + rng.integers(-10, 11, V_rand.shape)) % p
    W_pert = (W_rand + rng.integers(-10, 11, W_rand.shape)) % p
    U_n, V_n, W_n, conv, _ = newton_step(U_pert, V_pert, W_pert, T_rand, 
                                           gauge_G, gauge_g, p)
    t2 = time.time()
    print(f"One Newton ARTIFACT: {t2-t1:.3f}s, converged={conv}")
    
    # Verify Newton converges for known solution
    U_t, V_t, W_t = U_rand.copy(), V_rand.copy(), W_rand.copy()
    U_t = (U_t + rng.integers(-5, 6, U_t.shape)) % p
    V_t = (V_t + rng.integers(-5, 6, V_t.shape)) % p
    W_t = (W_t + rng.integers(-5, 6, W_t.shape)) % p
    for nit in range(30):
        U_t, V_t, W_t, conv, _ = newton_step(U_t, V_t, W_t, T_rand, gauge_G, gauge_g, p)
        res_t = brent_residual(U_t, V_t, W_t, T_rand, p)
        if np.all(res_t == 0):
            print(f"Newton converged for random rank-{r} control in {nit+1} iterations")
            break
    else:
        print(f"Newton did NOT converge for random rank-{r} control in 30 iterations!")
    
    step_time = t2 - t1
    total_est = (args.homotopy_paths * args.homotopy_steps * args.max_newton * step_time +
                 args.newton_starts * args.max_newton * step_time)
    print(f"ARTIFACT time: {step_time:.3f}s, estimated total: {total_est:.0f}s")
    
    # --- Homotopy experiments ---
    print(f"\n=== Homotopy: {args.homotopy_paths} paths × {args.homotopy_steps} steps ===")
    homotopy_results = []
    homotopy_successes = 0
    
    for path_idx in range(args.homotopy_paths):
        t_start = time.time()
        T_rand, U0, V0, W0 = random_rank_r_tensor(r, p, rng)
        
        result = run_homotopy(T_rand, U0, V0, W0, T333, args.homotopy_steps, 
                              args.max_newton, p, rng)
        elapsed = time.time() - t_start
        result["path_idx"] = path_idx
        result["elapsed_sec"] = elapsed
        homotopy_results.append(result)
        
        status = result["status"]
        if status == "SUCCESS":
            homotopy_successes += 1
            print(f"  path {path_idx}: *** SUCCESS *** in {elapsed:.1f}s")
        elif status == "newton_fail":
            print(f"  path {path_idx}: Newton fail at ARTIFACT {result['failed_at_step']}/{args.homotopy_steps} "
                  f"({result['nonzero_residual']} nonzero) in {elapsed:.1f}s")
        else:
            print(f"  path {path_idx}: {status} in {elapsed:.1f}s")
    
    print(f"\nHomotopy: {homotopy_successes}/{args.homotopy_paths} successes")
    
    # --- Multi-start Newton on T333 ---
    print(f"\n=== Multi-start Newton: {args.newton_starts} random starts ===")
    t_ms = time.time()
    ms_successes = run_multistart_newton(T333, r, args.newton_starts, args.max_newton, p, rng)
    ms_time = time.time() - t_ms
    print(f"Multi-start: {len(ms_successes)}/{args.newton_starts} successes in {ms_time:.1f}s")
    
    # --- Multi-start Newton on random rank-22 tensor (positive control) ---
    print(f"\n=== Positive control: multi-start on random rank-{r} ===")
    T_ctrl, _, _, _ = random_rank_r_tensor(r, p, rng)
    ctrl_succ = run_multistart_newton(T_ctrl, r, min(args.newton_starts, 50), 
                                       args.max_newton, p, rng)
    print(f"Control: {len(ctrl_succ)}/{min(args.newton_starts, 50)} successes")
    
    # --- Summary ---
    summary = {
        "prime": p, "rank": r, "seed": args.seed,
        "homotopy": {
            "n_paths": args.homotopy_paths, "n_steps": args.homotopy_steps,
            "max_newton": args.max_newton,
            "successes": homotopy_successes,
            "details": homotopy_results
        },
        "multistart_T333": {
            "n_starts": args.newton_starts, "max_newton": args.max_newton,
            "successes": len(ms_successes), "details": ms_successes
        },
        "positive_control": {
            "n_starts": min(args.newton_starts, 50),
            "successes": len(ctrl_succ)
        },
        "step_time_sec": step_time,
        "total_time_sec": time.time() - t0
    }
    
    tag = f"p{p}_r{r}"
    if args.pilot: tag += "_pilot"
    fp = OUT / f'modular_newton_{tag}.json'
    fp.write_text(json.dumps(summary, indent=2, default=str) + '\n')
    print(f"\nSaved to {fp}")
    
    if homotopy_successes > 0:
        print("\n*** RANK-22 DECOMPOSITION FOUND! ***")
    elif len(ctrl_succ) == 0:
        print("\n** Warning: positive control also failed — solver may be miscalibrated **")
    else:
        print(f"\n** T333 rank-22 not found (0/{args.homotopy_paths} homotopy, "
              f"0/{args.newton_starts} random starts), "
              f"but positive control works ({len(ctrl_succ)} successes) **")

if __name__ == '__main__':
    main()
