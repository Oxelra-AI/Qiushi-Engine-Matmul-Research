#!/usr/bin/env python3
r"""analysis: Modular search for rank-22 decomposition of T⟨3,3,3⟩.

Combines three methods:
  1. ALS (alternating least squares) from random starts over F_p
  2. ALS-homotopy: warm-start from rank-r of random tensor toward T333
  3. Gauge-fixed Newton on the full Brent system

Rank 23 and random-tensor rank 22 serve as positive controls.
"""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
import rank22_singular_stratum_v2 as s19

WS = SCRIPT_DIR.parent
OUT = WS / 'data' / 'modular_search'
OUT.mkdir(parents=True, exist_ok=True)

# ────────── core utilities ──────────

def make_unfoldings(T, p):
    """Mode-1/2/3 unfoldings of a (9,9,9) tensor, each (81,9) over F_p."""
    T = T % p
    T_C = T.reshape(81, 9)                       # T[9a+b, c]
    T_A = T.transpose(1, 2, 0).reshape(81, 9)    # T[9b+c, a]
    T_B = T.transpose(0, 2, 1).reshape(81, 9)    # T[9a+c, b]
    return T_C, T_A, T_B

def kr_matrix(A, B, p):
    """Khatri-Rao product: column i = A[i] ⊗ B[i].  A,B: (r,9). Returns (81,r)."""
    r = A.shape[0]
    P = np.empty((81, r), dtype=np.int64)
    for i in range(r):
        P[:, i] = np.outer(A[i] % p, B[i] % p).ravel() % p
    return P

def find_pivot_rows(P, p, r):
    """Find r independent rows of P (81×r) over F_p.  Returns row indices or None."""
    pivs = s19.pivot_columns_rref(P.T % p, p)
    return pivs[:r] if len(pivs) >= r else None

def als_solve(P, T_unfold, p, r):
    """Solve  P @ Factor = T_unfold  via an r-row minor.
    P:(81,r), T_unfold:(81,9).  Returns (Factor (r,9), residual_nnz) or (None,-1)."""
    rows = find_pivot_rows(P, p, r)
    if rows is None:
        return None, -1
    try:
        F = s19.solve_mod(P[rows] % p, T_unfold[rows] % p, p)   # (r,9)
    except ValueError:
        return None, -1
    res = (T_unfold - P @ F % p) % p
    return F, int(np.count_nonzero(res))

def full_brent_check(U, V, W, T, p):
    """Return number of nonzero Brent residual entries (729 total)."""
    return int(np.count_nonzero(s19.brent_residual(U, V, W, T, p)))

# ────────── ALS search ──────────

def als_sweep(U, V, W, T_C, T_A, T_B, p, r):
    """One full ALS sweep: update W, U, V.  Returns (U,V,W, residuals)."""
    # W update
    P = kr_matrix(U, V, p)
    Wn, rw = als_solve(P, T_C, p, r)
    if Wn is not None: W = Wn
    # U update
    P = kr_matrix(V, W, p)
    Un, ru = als_solve(P, T_A, p, r)
    if Un is not None: U = Un
    # V update
    P = kr_matrix(U, W, p)
    Vn, rv = als_solve(P, T_B, p, r)
    if Vn is not None: V = Vn
    return U, V, W, (rw, ru, rv)

def als_search(T, p, r, num_starts, max_iters, rng_seed=0, verbose=False):
    """Run ALS from random starts.  Returns (found_list, stats)."""
    T_C, T_A, T_B = make_unfoldings(T, p)
    found, stats = [], {'min_rv': 729, 'degen': 0, 'checked': 0}
    t0 = time.time()
    for trial in range(num_starts):
        rng = np.random.RandomState(rng_seed + trial)
        U = rng.randint(0, p, (r, 9)).astype(np.int64)
        V = rng.randint(0, p, (r, 9)).astype(np.int64)
        W = rng.randint(0, p, (r, 9)).astype(np.int64)
        for it in range(max_iters):
            U, V, W, (rw, ru, rv) = als_sweep(U, V, W, T_C, T_A, T_B, p, r)
            if rv == -1 or ru == -1 or rw == -1:
                stats['degen'] += 1
                break
            low = min(rw, ru, rv)
            if low < stats['min_rv']:
                stats['min_rv'] = low
                if verbose:
                    print(f'  trial {trial} it {it}: min_res={low}  (rw={rw} ru={ru} rv={rv})')
            if rv == 0:
                nnz = full_brent_check(U, V, W, T, p)
                if nnz == 0:
                    found.append({'trial': trial, 'iter': it})
                    if verbose:
                        print(f'  *** FOUND r={r} at trial {trial} iter {it} ***')
                    break
        stats['checked'] = trial + 1
    stats['elapsed'] = round(time.time() - t0, 2)
    return found, stats

# ────────── ALS homotopy from random rank-r ──────────

def random_rank_r_tensor(p, r, rng):
    """Generate random rank-r tensor with known decomposition."""
    U = rng.randint(0, p, (r, 9)).astype(np.int64)
    V = rng.randint(0, p, (r, 9)).astype(np.int64)
    W = rng.randint(0, p, (r, 9)).astype(np.int64)
    T = s19.tensor_from_factors(U, V, W, p)
    return T, U, V, W

def als_homotopy(T_target, p, r, num_paths, steps_per_path, als_iters, rng_seed=0, verbose=False):
    """ALS homotopy: from random rank-r tensor, linear deformation toward T_target."""
    T_C_target, T_A_target, T_B_target = make_unfoldings(T_target, p)
    found, stats = [], {'best_final_res': 729, 'paths_completed': 0, 'paths_broken': 0}
    t0 = time.time()
    for path in range(num_paths):
        rng = np.random.RandomState(rng_seed + 100000 + path)
        T0, U, V, W = random_rank_r_tensor(p, r, rng)
        path_ok = True
        for step in range(1, steps_per_path + 1):
            # T_t = T0 + (ARTIFACT/steps) * (T_target - T0)  mod p
            # = T0 * (1 - ARTIFACT*inv(steps)) + T_target * ARTIFACT*inv(steps)
            t_num = step
            t_den_inv = pow(steps_per_path, p - 2, p)
            alpha = t_num * t_den_inv % p          # = ARTIFACT/steps mod p
            T_t = ((1 + p - alpha) % p * T0 + alpha * T_target) % p
            T_C, T_A, T_B = make_unfoldings(T_t, p)
            # ALS from current decomposition
            for it in range(als_iters):
                U, V, W, (rw, ru, rv) = als_sweep(U, V, W, T_C, T_A, T_B, p, r)
                if rv == 0:
                    break
                if rv == -1:
                    path_ok = False
                    break
            if not path_ok or rv != 0:
                path_ok = False
                break
        # Check final
        if path_ok:
            nnz = full_brent_check(U, V, W, T_target, p)
            stats['best_final_res'] = min(stats['best_final_res'], nnz)
            stats['paths_completed'] += 1
            if nnz == 0:
                found.append({'path': path})
                if verbose:
                    print(f'  *** HOMOTOPY FOUND r={r} path {path} ***')
        else:
            stats['paths_broken'] += 1
        if verbose and (path + 1) % 50 == 0:
            print(f'  homotopy: {path+1}/{num_paths} done, {stats["paths_completed"]} completed, '
                  f'{len(found)} found, best_final_res={stats["best_final_res"]}')
    stats['elapsed'] = round(time.time() - t0, 2)
    return found, stats

# ────────── projected-kernel diagnostic ──────────

def projected_kernel_check(U, V, T, p):
    """Check rank(pi X) against the projected-kernel model."""
    from projected_kernel_model import sparse_t333_quotient_matrix, X_from_UV
    Q = sparse_t333_quotient_matrix(p)
    X = s19.pairing_matrix(U, V, p)
    QX = Q @ X % p
    return int(s19.rank_mod(QX, p))

# ────────── gauge-fixed Newton ──────────

def newton_step(U, V, W, T, p, r):
    """One Newton ARTIFACT on the full Brent system (no gauge, underdetermined).
    Selects r*27 independent rows, solves the square system."""
    res = s19.brent_residual(U, V, W, T, p)
    if np.count_nonzero(res) == 0:
        return U, V, W, 0
    J = s19.brent_jacobian(U, V, W, p)   # 729 × 27r
    # pick independent rows
    pivs = s19.pivot_columns_rref(J, p)
    n = 27 * r
    if len(pivs) < n:
        # underdetermined: use all pivot rows
        rows = pivs
    else:
        rows = pivs[:n]
    if len(rows) < n:
        # pad with arbitrary rows
        used = set(rows)
        for i in range(729):
            if i not in used:
                rows.append(i)
                if len(rows) == n:
                    break
    rows = rows[:n]
    # Newton: J δ = f(x)-T = -res.  Since J = -∂f/∂x from s19 convention.
    neg_res = (p - res) % p
    try:
        delta = s19.solve_mod(J[rows] % p, neg_res[rows].reshape(-1, 1) % p, p)
    except ValueError:
        return U, V, W, int(np.count_nonzero(res))
    delta = delta.ravel() % p
    # apply correction
    U2 = (U + delta[:9*r].reshape(r, 9)) % p
    V2 = (V + delta[9*r:18*r].reshape(r, 9)) % p
    W2 = (W + delta[18*r:27*r].reshape(r, 9)) % p
    res2 = s19.brent_residual(U2, V2, W2, T, p)
    return U2, V2, W2, int(np.count_nonzero(res2))

def newton_search(T, p, r, num_starts, max_newton, rng_seed=0, verbose=False):
    """Newton from random starts on full Brent system."""
    found, stats = [], {'min_res': 729, 'checked': 0}
    t0 = time.time()
    for trial in range(num_starts):
        rng = np.random.RandomState(rng_seed + 200000 + trial)
        U = rng.randint(0, p, (r, 9)).astype(np.int64)
        V = rng.randint(0, p, (r, 9)).astype(np.int64)
        W = rng.randint(0, p, (r, 9)).astype(np.int64)
        for it in range(max_newton):
            U, V, W, nnz = newton_step(U, V, W, T, p, r)
            if nnz < stats['min_res']:
                stats['min_res'] = nnz
                if verbose:
                    print(f'  newton trial {trial} it {it}: nnz={nnz}')
            if nnz == 0:
                found.append({'trial': trial, 'iter': it})
                if verbose:
                    print(f'  *** NEWTON FOUND r={r} trial {trial} ***')
                break
        stats['checked'] = trial + 1
    stats['elapsed'] = round(time.time() - t0, 2)
    return found, stats

# ────────── main ──────────

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--prime', type=int, default=65521)
    ap.add_argument('--als-starts', type=int, default=3000)
    ap.add_argument('--als-iters', type=int, default=80)
    ap.add_argument('--homotopy-paths', type=int, default=200)
    ap.add_argument('--homotopy-steps', type=int, default=20)
    ap.add_argument('--homotopy-als', type=int, default=30)
    ap.add_argument('--newton-starts', type=int, default=20)
    ap.add_argument('--newton-iters', type=int, default=8)
    args = ap.parse_args()

    p = args.prime
    T333 = s19.make_T333() % p
    result = {'prime': p, 'tensor': 'T333', 'tests': {}}

    # ── Positive control: ALS finds rank-22 of RANDOM rank-22 tensor ──
    print('=== Control: ALS on random rank-22 tensor ===')
    rng_ctrl = np.random.RandomState(42)
    T_rand, _, _, _ = random_rank_r_tensor(p, 22, rng_ctrl)
    ctrl_found, ctrl_stats = als_search(T_rand, p, 22, num_starts=500,
                                        max_iters=80, rng_seed=500000, verbose=True)
    result['tests']['control_random_r22'] = {
        'found': len(ctrl_found), 'stats': ctrl_stats,
        'interpretation': 'ALS on random rank-22 tensor calibrates whether ALS can find decompositions at all'
    }
    print(f'  Control: found={len(ctrl_found)}, min_res={ctrl_stats["min_rv"]}, '
          f'elapsed={ctrl_stats["elapsed"]}s')

    # ── ALS search for T333 rank 23 (known to exist) ──
    print('\n=== ALS: T333 rank 23 ===')
    found23, stats23 = als_search(T333, p, 23, args.als_starts, args.als_iters,
                                  rng_seed=0, verbose=True)
    result['tests']['T333_r23_als'] = {'found': len(found23), 'stats': stats23}
    print(f'  r=23: found={len(found23)}, min_res={stats23["min_rv"]}, elapsed={stats23["elapsed"]}s')

    # ── ALS search for T333 rank 22 ──
    print('\n=== ALS: T333 rank 22 ===')
    found22, stats22 = als_search(T333, p, 22, args.als_starts, args.als_iters,
                                  rng_seed=10000, verbose=True)
    result['tests']['T333_r22_als'] = {'found': len(found22), 'stats': stats22}
    print(f'  r=22: found={len(found22)}, min_res={stats22["min_rv"]}, elapsed={stats22["elapsed"]}s')

    # ── ALS homotopy for T333 rank 22 ──
    print('\n=== ALS homotopy: T333 rank 22 ===')
    hfound22, hstats22 = als_homotopy(T333, p, 22, args.homotopy_paths,
                                       args.homotopy_steps, args.homotopy_als,
                                       rng_seed=0, verbose=True)
    result['tests']['T333_r22_homotopy'] = {'found': len(hfound22), 'stats': hstats22}
    print(f'  homotopy r=22: found={len(hfound22)}, best_final={hstats22["best_final_res"]}, '
          f'completed={hstats22["paths_completed"]}, elapsed={hstats22["elapsed"]}s')

    # ── ALS homotopy for T333 rank 23 (control) ──
    print('\n=== ALS homotopy: T333 rank 23 (control) ===')
    hfound23, hstats23 = als_homotopy(T333, p, 23, min(args.homotopy_paths, 100),
                                       args.homotopy_steps, args.homotopy_als,
                                       rng_seed=0, verbose=True)
    result['tests']['T333_r23_homotopy'] = {'found': len(hfound23), 'stats': hstats23}
    print(f'  homotopy r=23: found={len(hfound23)}, best_final={hstats23["best_final_res"]}, '
          f'completed={hstats23["paths_completed"]}, elapsed={hstats23["elapsed"]}s')

    # ── Newton search for T333 rank 22 ──
    print('\n=== Newton: T333 rank 22 ===')
    nfound22, nstats22 = newton_search(T333, p, 22, args.newton_starts,
                                        args.newton_iters, rng_seed=0, verbose=True)
    result['tests']['T333_r22_newton'] = {'found': len(nfound22), 'stats': nstats22}
    print(f'  newton r=22: found={len(nfound22)}, min_res={nstats22["min_res"]}, '
          f'elapsed={nstats22["elapsed"]}s')

    # ── Summary ──
    result['summary'] = {
        'rank22_found_any_method': len(found22) + len(hfound22) + len(nfound22) > 0,
        'rank23_found_any_method': len(found23) + len(hfound23) > 0,
        'control_rank22_random_found': len(ctrl_found) > 0,
        'interpretation': (
            'If control_rank22_random_found=false, ALS/Newton is ineffective for this size. '
            'If rank23_found but not rank22: evidence (not proof) that T333 rank > 22 over F_p. '
            'If rank22_found: candidate for verification and Hensel lifting.'
        )
    }
    
    out = OUT / 'modular_search_results.json'
    out.write_text(json.dumps(result, indent=2, default=int) + '\n')
    print(f'\nSaved to {out}')

if __name__ == '__main__':
    main()
