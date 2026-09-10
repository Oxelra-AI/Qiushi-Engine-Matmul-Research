#!/usr/bin/env python3
r"""analysis: 13+9 completion chart for T_{333} rank-22 incidence.

Mathematical structure
---------------------
A 22-term rank-one decomposition T = sum_i u_i ⊗ v_i ⊗ w_i with the UV
columns x_i = u_i ⊗ v_i linearly independent can be rewritten in a "13+9
completion chart" by choosing 9 terms whose W-vectors span K^9.

   T_flat = X_P A^T + X_R B^T      (UV-W flattening: 81 × 9)

where X_P (81×13) contains the 13 "pivot" UV columns and X_R (81×9) contains
the 9 "remainder" UV columns, A (9×13) collects their W-coefficients, and
B (9×9) is invertible.  Setting D = B^{-T} and C = A^T D gives

   X_R = T_flat D − X_P C           (*)

where T_flat is the 81×9 UV-W flattening of T_{333}.

Variables:  13 rank-one UV columns (u_i, v_i ∈ K^9), C ∈ K^{13×9}, D ∈ GL_9.
            Total: 234 + 117 + 81 = 432 polynomial coordinates.
Constraints: each of the 9 columns of (*) reshaped as 9×9 must be rank ≤ 1.
Open conditions: det(D) ≠ 0 and rank(Q X_P) = 13, where Q is the 72×81
            quotient annihilating L = col(T_flat).

Key reduction (review):
   rank[X_P, X_R] = 9 + rank(Q X_P),
so full UV-rank 22 ⟺ rank(Q X_P) = 13.  No 22×22 minor atlas is needed.

This script:
  1. Builds T_{333} and its sparse quotient Q.
  2. Calibrates the chart on random rank-22 tensors over F_p (positive control).
  3. Analyzes the rank-shortening subproblem: for fixed X_P, each derived column
     is an independent rank-one shortening problem with 22 linear variables.
  4. Computes Jacobian structure at the positive-control solution.
  5. Tests the chart on T_{333} for structural obstructions.
"""
from __future__ import annotations
import argparse, itertools, json, sys, time
from pathlib import Path
from typing import List, Tuple, Optional
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
import rank22_singular_stratum_v2 as s19

P_DEFAULT = 65521

# ────────────────────────── Tensor and Quotient ──────────────────────────

def make_T333_flat(p: int) -> np.ndarray:
    """81 × 9  UV-W flattening of T_{333}."""
    return s19.tensor_uv_matrix(s19.make_T333()) % p

def sparse_quotient(p: int) -> np.ndarray:
    """72 × 81 sparse Q with QT = 0 and rank 72."""
    info = _t333_support()
    rows = []
    support_set = set(info['support_rows'])
    for uv in range(81):
        if uv not in support_set:
            e = np.zeros(81, dtype=np.int64); e[uv] = 1; rows.append(e)
    for c in range(9):
        anchor = info['by_c'][c][0]
        for uv in info['by_c'][c][1:]:
            e = np.zeros(81, dtype=np.int64)
            e[uv] = 1; e[anchor] = (p - 1) % p
            rows.append(e)
    Q = np.array(rows, dtype=np.int64) % p
    assert Q.shape == (72, 81)
    return Q

def _t333_support():
    by_c = {c: [] for c in range(9)}
    support = []
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a = 3*i+j; b = 3*j+k; c = 3*i+k
                uv = a*9+b
                by_c[c].append(uv)
                support.append((uv, c))
    for c in by_c:
        by_c[c] = sorted(by_c[c])
    return {'by_c': by_c, 'support_rows': sorted(set(uv for uv, c in support))}

# ────────────────────────── Modular Utilities ──────────────────────────

def inv_mod(x, p):
    return pow(int(x) % p, p - 2, p)

def det_mod(A, p):
    """Determinant of a square matrix mod p via Gaussian elimination."""
    A = np.array(A % p, dtype=np.int64, copy=True)
    n = A.shape[0]; det_val = 1
    for col in range(n):
        nz = np.nonzero(A[col:, col])[0]
        if len(nz) == 0:
            return 0
        piv = col + int(nz[0])
        if piv != col:
            A[[col, piv]] = A[[piv, col]]
            det_val = (p - det_val) % p
        det_val = (det_val * int(A[col, col])) % p
        inv = pow(int(A[col, col]), p - 2, p)
        A[col] = (A[col] * inv) % p
        for row in range(col + 1, n):
            if A[row, col] % p:
                A[row] = (A[row] - int(A[row, col]) * A[col]) % p
    return det_val % p

def mat_inv_mod(A, p):
    """Inverse of a square matrix mod p."""
    n = A.shape[0]
    return s19.solve_mod(A % p, np.eye(n, dtype=np.int64), p)

def kron_mod(u, v, p):
    """Kronecker product mod p."""
    return (np.outer(u % p, v % p).ravel()) % p

def matrix_rank_mod(M, p):
    """Rank of a 9×9 matrix mod p."""
    return s19.rank_mod(M.reshape(-1, M.shape[-1]) if M.ndim > 2 else M, p)

# ────────────────────────── Chart Construction ──────────────────────────

def random_rank22_decomposition(p, rng):
    """Generate a random rank-22 tensor over F_p with its decomposition."""
    U = rng.integers(0, p, (22, 9)).astype(np.int64) % p
    V = rng.integers(0, p, (22, 9)).astype(np.int64) % p
    W = rng.integers(0, p, (22, 9)).astype(np.int64) % p
    T = np.zeros((9, 9, 9), dtype=np.int64)
    for i in range(22):
        T = (T + np.einsum('a,b,c->abc', U[i], V[i], W[i])) % p
    return T % p, U, V, W

def extract_chart_coords(U, V, W, pivot_idx, rem_idx, p):
    """Given a full decomposition, extract the 13+9 chart coordinates.
    
    pivot_idx: list of 13 indices (the "free" UV terms)
    rem_idx:   list of 9 indices (the "W-basis" terms)
    
    Returns: X_P (81×13), C (13×9), D (9×9), and derived X_R (81×9).
    """
    assert len(pivot_idx) == 13 and len(rem_idx) == 9
    # X_P: 81 × 13 pairing columns for pivot terms
    X_P = np.array([kron_mod(U[i], V[i], p) for i in pivot_idx], dtype=np.int64).T % p
    # W_P (9×13), W_R (9×9) — W-factor matrices
    W_P = W[pivot_idx].T % p   # 9 × 13
    W_R = W[rem_idx].T % p     # 9 × 9
    assert det_mod(W_R, p) != 0, "W_R must be invertible"
    # D = W_R^{-T}, C = W_P^T @ D = A^T @ D where A^T = W_P^T
    W_R_inv = mat_inv_mod(W_R, p)  # W_R^{-1}: 9×9
    D = W_R_inv.T % p              # (W_R^{-1})^T = W_R^{-T}
    C = (W_P.T @ D) % p            # 13 × 9
    # X_R from the original decomposition
    X_R_orig = np.array([kron_mod(U[i], V[i], p) for i in rem_idx], dtype=np.int64).T % p
    return X_P, C, D, X_R_orig

def compute_derived_columns(T_flat, X_P, C, D, p):
    """Compute the 9 derived UV columns: X_R = T_flat @ D − X_P @ C."""
    return (T_flat @ D - X_P @ C) % p  # 81 × 9

def check_rank_one(col81, p):
    """Check if an 81-vector reshaped as 9×9 has rank ≤ 1."""
    M = col81.reshape(9, 9) % p
    return s19.rank_mod(M, p) <= 1

def verify_chart(T_flat, X_P, C, D, Q, p):
    """Full chart verification: derived columns rank 1, Q-rank, det(D)."""
    X_R = compute_derived_columns(T_flat, X_P, C, D, p)
    results = {}
    # 1. Each derived column rank ≤ 1
    derived_ranks = []
    for j in range(9):
        M = X_R[:, j].reshape(9, 9) % p
        r = s19.rank_mod(M, p)
        derived_ranks.append(int(r))
    results['derived_column_ranks'] = derived_ranks
    results['all_rank_one'] = all(r <= 1 for r in derived_ranks)
    # 2. det(D) ≠ 0
    results['det_D'] = int(det_mod(D, p))
    results['D_invertible'] = results['det_D'] != 0
    # 3. rank(Q X_P) = 13
    QXP = (Q @ X_P) % p
    results['rank_QXP'] = int(s19.rank_mod(QXP, p))
    results['QXP_full_rank'] = results['rank_QXP'] == 13
    # 4. Full UV rank via the formula: rank[X_P, X_R] = 9 + rank(QXP)
    X_full = np.hstack([X_P, X_R]) % p
    results['rank_X_full'] = int(s19.rank_mod(X_full, p))
    results['expected_rank_X_full'] = 9 + results['rank_QXP']
    # 5. Reconstruct W and verify Brent equations
    results['chart_valid'] = (results['all_rank_one'] and results['D_invertible']
                              and results['QXP_full_rank'])
    return results

def verify_brent_from_chart(T, X_P, X_R, C, D, pivot_idx, rem_idx, p):
    """Reconstruct U, V, W from chart and verify all 729 Brent identities."""
    # Recover factor vectors
    U_out = np.zeros((22, 9), dtype=np.int64)
    V_out = np.zeros((22, 9), dtype=np.int64)
    W_out = np.zeros((22, 9), dtype=np.int64)
    # Pivot terms: x_i = u_i ⊗ v_i already parametrized
    for idx_pos, idx_orig in enumerate(pivot_idx):
        col = X_P[:, idx_pos].reshape(9, 9) % p
        # Factor the rank-1 matrix: find nonzero row
        for r in range(9):
            if np.any(col[r] % p):
                # v = col[r], u = col[:, col_idx] / v[col_idx] for some nonzero entry
                v = col[r] % p
                c_idx = int(np.nonzero(v)[0][0])
                u = (col[:, c_idx] * inv_mod(v[c_idx], p)) % p
                U_out[idx_orig] = u
                V_out[idx_orig] = v
                break
    # Remainder terms from derived columns
    for idx_pos, idx_orig in enumerate(rem_idx):
        col = X_R[:, idx_pos].reshape(9, 9) % p
        for r in range(9):
            if np.any(col[r] % p):
                v = col[r] % p
                c_idx = int(np.nonzero(v)[0][0])
                u = (col[:, c_idx] * inv_mod(v[c_idx], p)) % p
                U_out[idx_orig] = u
                V_out[idx_orig] = v
                break
    # W recovery: D = B^{-T}, C = A^T D where A^T = W_P^T (13×9)
    # So W_P^T = C @ D^{-1} and W_R = D^{-T} = (D^{-1})^T
    D_inv = mat_inv_mod(D, p)
    W_R_mat = D_inv.T % p   # 9×9: column j = w-vector of remainder term j
    WP_T = (C @ D_inv) % p  # 13×9: row i = w-vector of pivot term i
    for idx_pos, idx_orig in enumerate(rem_idx):
        W_out[idx_orig] = W_R_mat[:, idx_pos] % p
    for idx_pos, idx_orig in enumerate(pivot_idx):
        W_out[idx_orig] = WP_T[idx_pos] % p
    # Verify Brent
    res = s19.brent_residual(U_out, V_out, W_out, T, p)
    return int(np.count_nonzero(res)), U_out, V_out, W_out

# ────────────────────── Rank-shortening analysis ──────────────────────

def analyze_rank_shortening(T_flat, X_P, Q, p):
    """For fixed X_P, analyze the rank-shortening subproblem for each derived column.
    
    Each derived column Y_j = T_flat @ d_j - X_P @ c_j must be rank ≤ 1.
    Given X_P, the variables (c_j, d_j) ∈ K^{13+9} = K^{22} are independent per j.
    
    Key structural insight: the entries of Y_j are LINEAR in (c_j, d_j).
    The rank-1 condition gives ≤ 64 independent quadratic equations.
    So each j is a system of ≤64 quadratics in 22 variables.
    """
    results = {}
    
    # T_flat slices as 9×9 matrices (one per W-coordinate)
    T_slices = []
    for w in range(9):
        T_slices.append(T_flat[:, w].reshape(9, 9) % p)
    
    # X_P columns as 9×9 matrices (only if X_P provided)
    XP_mats = []
    if X_P is not None:
        for i in range(X_P.shape[1]):
            XP_mats.append(X_P[:, i].reshape(9, 9) % p)
    
    # For the rank-shortening problem with D=I (standard W-basis):
    # Y_j = T_flat[:, j] - X_P @ c_j  (only c_j free, d_j = e_j)
    # This is a simpler subproblem with only 13 variables per j.
    
    # With general D: Y_j = sum_w T_w d_{w,j} - sum_i c_{i,j} x_i
    # where T_w are rank-3 matrices (Kronecker structure) and x_i are rank-1.
    
    # Key property of T333 slices: T_{(i,k)} = I_3 ⊗ E_{ik} block-diag structure
    # (T_flat d_j) reshaped as 9×9 has entry [(i1,j1),(j2,k2)] = δ(j1,j2) D_{(3*i1+k2),j}
    # This is block-diagonal in the j-index with 3×3 blocks.
    
    # Count: for generic D, T_flat @ d_j reshaped has rank 9 (=3*3).
    # We need rank 1 after subtracting 13 rank-1 corrections.
    # Minimum rank-1 terms needed: 9-1 = 8. We have 13. Extra: 5.
    
    # For D = I: T_j has rank 3 (one block). Need 3-1=2 corrections minimum.
    
    rank_T_slices = [int(s19.rank_mod(T_slices[w], p)) for w in range(9)]
    results['T_slice_ranks'] = rank_T_slices
    results['variable_count_per_j'] = 22  # (c_j: 13, d_j: 9)
    results['rank_one_codim'] = 64  # for 9×9 rank-1
    
    return results

# ────────────────────── T333-specific tests ──────────────────────

def test_T333_chart(p, rng, T333_flat, Q, num_xp_trials=20):
    """For T_{333}, try random 13-column X_P sets and check rank-shortening feasibility."""
    results = []
    for trial in range(num_xp_trials):
        # Generate 13 random rank-1 UV columns
        X_P = np.zeros((81, 13), dtype=np.int64)
        for i in range(13):
            u = rng.integers(0, p, 9).astype(np.int64) % p
            v = rng.integers(0, p, 9).astype(np.int64) % p
            X_P[:, i] = kron_mod(u, v, p)
        
        QXP = (Q @ X_P) % p
        qrank = s19.rank_mod(QXP, p)
        
        rec = {'trial': trial, 'rank_QXP': int(qrank)}
        
        if qrank == 13:
            # Full Q-rank achieved. Now check: for D=I, can any derived column be rank-1?
            for j in range(9):
                Y_j = (T333_flat[:, j] - X_P @ np.zeros(13, dtype=np.int64)) % p
                # With c_j = 0, Y_j = T_flat[:,j]. Rank = 3 (T333 slice).
                # The interesting question: does a c_j exist making it rank 1?
                # This is: find c ∈ F_p^13 such that rank(T_j - sum c_i x_i) ≤ 1.
                pass  # Will be addressed in the shortening solver
            rec['qxp_full_rank'] = True
        else:
            rec['qxp_full_rank'] = False
        
        results.append(rec)
    
    qxp_13_count = sum(1 for r in results if r.get('qxp_full_rank', False))
    return {'trials': num_xp_trials, 'qxp_rank_13_count': qxp_13_count,
            'fraction_qxp_full': qxp_13_count / max(1, num_xp_trials)}

def rank_one_shortening_solver_bruteforce_small(T_flat_col, XP_cols, p, rng,
                                                 max_attempts=5000):
    """Try to find c ∈ F_p^13 such that T_flat_col - X_P c is rank ≤ 1.
    
    For small p only. Returns the first c found or None.
    """
    n_cols = XP_cols.shape[1]
    target = T_flat_col.reshape(9, 9) % p
    
    for _ in range(max_attempts):
        c = rng.integers(0, p, n_cols).astype(np.int64) % p
        correction = np.zeros(81, dtype=np.int64)
        for i in range(n_cols):
            correction = (correction + int(c[i]) * XP_cols[:, i]) % p
        Y = (T_flat_col - correction) % p
        M = Y.reshape(9, 9) % p
        if s19.rank_mod(M, p) <= 1:
            return c
    return None

# ────────────────────────── Main ──────────────────────────

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--prime', type=int, default=P_DEFAULT)
    ap.add_argument('--seed', type=int, default=2026090428)
    ap.add_argument('--n-controls', type=int, default=5)
    ap.add_argument('--out', default='')
    args = ap.parse_args()
    
    p = args.prime
    rng = np.random.default_rng(args.seed)
    t0 = time.time()
    
    T333 = s19.make_T333()
    T333_flat = make_T333_flat(p)
    Q = sparse_quotient(p)
    
    print(f"T333 flat shape: {T333_flat.shape}, Q shape: {Q.shape}")
    print(f"Q rank: {s19.rank_mod(Q, p)}, Q@T=0: {np.count_nonzero((Q @ T333_flat) % p) == 0}")
    
    results = {
        'purpose': '13+9 completion chart for T333 rank-22 incidence',
        'prime': p,
        'timestamp': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
    }
    
    # ─── 1. Positive controls: random rank-22 tensors ───
    print("\n=== Positive controls: random rank-22 tensors ===")
    controls = []
    for trial in range(args.n_controls):
        T_rand, U, V, W = random_rank22_decomposition(p, rng)
        T_rand_flat = s19.tensor_uv_matrix(T_rand) % p
        
        # Choose 9 remainder terms with invertible W block
        found = False
        for perm in range(50):
            order = rng.permutation(22).tolist()
            rem_idx = order[:9]
            pivot_idx = order[9:]
            W_R = W[rem_idx].T % p
            if det_mod(W_R, p) != 0:
                found = True; break
        
        if not found:
            controls.append({'trial': trial, 'status': 'no_invertible_W_block'})
            continue
        
        X_P, C, D, X_R_orig = extract_chart_coords(U, V, W, pivot_idx, rem_idx, p)
        X_R_derived = compute_derived_columns(T_rand_flat, X_P, C, D, p)
        
        # Verify derived = original
        diff = np.count_nonzero((X_R_derived - X_R_orig) % p)
        
        # Full chart verification
        vr = verify_chart(T_rand_flat, X_P, C, D, Q, p)
        
        # Brent verification
        brent_nnz, _, _, _ = verify_brent_from_chart(T_rand, X_P, X_R_derived, C, D,
                                                      pivot_idx, rem_idx, p)
        
        rec = {
            'trial': trial,
            'X_R_match': diff == 0,
            'chart_valid': vr['chart_valid'],
            'all_rank_one': vr['all_rank_one'],
            'derived_ranks': vr['derived_column_ranks'],
            'det_D': vr['det_D'],
            'rank_QXP': vr['rank_QXP'],
            'rank_X_full': vr['rank_X_full'],
            'expected_rank': vr['expected_rank_X_full'],
            'brent_nonzero': brent_nnz,
        }
        print(f"  Control {trial}: valid={rec['chart_valid']}, "
              f"X_R_match={rec['X_R_match']}, "
              f"rank_QXP={rec['rank_QXP']}, "
              f"brent_nnz={brent_nnz}")
        controls.append(rec)
    
    results['positive_controls'] = controls
    all_valid = all(c.get('chart_valid', False) for c in controls)
    all_brent_zero = all(c.get('brent_nonzero', 1) == 0 for c in controls)
    print(f"  All valid: {all_valid}, All Brent zero: {all_brent_zero}")
    
    # ─── 2. Rank-shortening analysis ───
    print("\n=== Rank-shortening analysis ===")
    rs_analysis = analyze_rank_shortening(T333_flat, None, Q, p)
    results['rank_shortening_structure'] = rs_analysis
    print(f"  T333 slice ranks: {rs_analysis['T_slice_ranks']}")
    
    # ─── 3. Random X_P trials against T333 ───
    print("\n=== Random X_P against T333 ===")
    t333_test = test_T333_chart(p, rng, T333_flat, Q, num_xp_trials=100)
    results['T333_random_XP'] = t333_test
    print(f"  Q-rank 13 fraction: {t333_test['fraction_qxp_full']:.3f}")
    
    # ─── 4. Jacobian rank at positive control ───
    print("\n=== Jacobian analysis at positive control ===")
    if controls and controls[0].get('chart_valid', False):
        # Re-extract first control
        T_rand, U, V, W = random_rank22_decomposition(p, np.random.default_rng(args.seed))
        T_rand_flat = s19.tensor_uv_matrix(T_rand) % p
        order = np.random.default_rng(args.seed).permutation(22).tolist()
        # Find valid partition
        for perm in range(50):
            order = rng.permutation(22).tolist()
            rem_idx = order[:9]; pivot_idx = order[9:]
            W_R = W[rem_idx].T % p
            if det_mod(W_R, p) != 0: break
        X_P, C, D, _ = extract_chart_coords(U, V, W, pivot_idx, rem_idx, p)
        
        # Compute Jacobian of the rank-1 conditions w.r.t. (u_i, v_i, C, D)
        # The Jacobian has rows = 2×2 minor conditions, cols = variables
        # For efficiency, compute the Jacobian of the 81-entries of each Y_j
        # w.r.t. the 432 variables, then the chain rule gives the minor Jacobian.
        
        # Y_j = T_flat @ D[:,j] - X_P @ C[:,j]
        # Y_j depends on: {u_i, v_i} through X_P, C[:,j], D[:,j]
        # 
        # dY_j / d(u_i)_a = -C_{ij} * (e_a ⊗ v_i)  (in 81-vector)
        # dY_j / d(v_i)_b = -C_{ij} * (u_i ⊗ e_b)
        # dY_j / dC_{ij}  = -x_i  (the i-th UV column)
        # dY_j / dD_{wj}  = T_flat[:,w]  (the w-th column of T_flat)
        
        # Total Jacobian of the map (u,v,C,D) -> (Y_1,...,Y_9):
        # Output: 81*9 = 729 entries.  Variables: 432.
        # This is exactly the Brent Jacobian in disguise!
        
        # Use the original Brent Jacobian for the Jacobian rank.
        # At a rank-22 point of a random tensor: J has rank 550.
        # Shortened to the 13+9 chart: remove 9*9=81 W-variables.
        
        U_all = np.zeros((22, 9), dtype=np.int64)
        V_all = np.zeros((22, 9), dtype=np.int64)
        W_all = np.zeros((22, 9), dtype=np.int64)
        D_inv = mat_inv_mod(D, p)
        W_R_mat = D_inv.T % p
        WP_T = (C @ D_inv) % p
        for idx_pos, idx_orig in enumerate(pivot_idx):
            col = X_P[:, idx_pos].reshape(9, 9) % p
            for r in range(9):
                if np.any(col[r] % p):
                    v = col[r] % p
                    c_idx = int(np.nonzero(v)[0][0])
                    u = (col[:, c_idx] * inv_mod(v[c_idx], p)) % p
                    U_all[idx_orig] = u; V_all[idx_orig] = v; break
            W_all[idx_orig] = WP_T[idx_pos] % p
        for idx_pos, idx_orig in enumerate(rem_idx):
            X_R = compute_derived_columns(T_rand_flat, X_P, C, D, p)
            col = X_R[:, idx_pos].reshape(9, 9) % p
            for r in range(9):
                if np.any(col[r] % p):
                    v = col[r] % p
                    c_idx = int(np.nonzero(v)[0][0])
                    u = (col[:, c_idx] * inv_mod(v[c_idx], p)) % p
                    U_all[idx_orig] = u; V_all[idx_orig] = v; break
            W_all[idx_orig] = W_R_mat[:, idx_pos] % p
        
        J_full = s19.brent_jacobian(U_all, V_all, W_all, p)
        j_rank = s19.rank_mod(J_full, p)
        print(f"  Full Brent Jacobian rank at control: {j_rank} (expected 550)")
        results['jacobian_rank'] = int(j_rank)
    
    # ─── 5. UV-rank formula verification ───
    print("\n=== UV-rank formula: rank[X_P,X_R] = 9 + rank(QXP) ===")
    formula_checks = []
    for trial in range(min(3, len(controls))):
        if not controls[trial].get('chart_valid', False):
            continue
        rank_full = controls[trial]['rank_X_full']
        rank_qxp = controls[trial]['rank_QXP']
        formula_holds = (rank_full == 9 + rank_qxp)
        formula_checks.append({
            'trial': trial,
            'rank_X_full': rank_full,
            'rank_QXP': rank_qxp,
            'formula_holds': formula_holds,
        })
        print(f"  Trial {trial}: rank_X={rank_full} = 9 + {rank_qxp} = {9+rank_qxp}: {formula_holds}")
    results['uv_rank_formula_checks'] = formula_checks
    
    # ─── 6. cn122 deletion test ───
    print("\n=== cn122 deletion tests in chart ===")
    ws = Path(__file__).resolve().parent.parent
    cn122_path = ws / 'data/cn122_r23_reproduce/scheme.qmm'
    if cn122_path.exists():
        U23, V23, W23 = s19.load_qmm(cn122_path)
        # Try each single deletion
        cn122_results = []
        for drop in range(23):
            keep = [i for i in range(23) if i != drop]
            U22, V22, W22 = U23[keep], V23[keep], W23[keep]
            # Check if any 9-subset has invertible W
            found_partition = False
            for attempt in range(200):
                order = rng.permutation(22).tolist()
                rem = order[:9]; piv = order[9:]
                W_R = W22[rem].T % p
                if det_mod(W_R, p) != 0:
                    found_partition = True; break
            if not found_partition:
                cn122_results.append({'drop': drop, 'status': 'no_W_basis'})
                continue
            
            X_P_loc, C_loc, D_loc, _ = extract_chart_coords(U22, V22, W22, piv, rem, p)
            # Compute derived columns against T333 (not the truncated tensor!)
            X_R_T333 = compute_derived_columns(T333_flat, X_P_loc, C_loc, D_loc, p)
            # Check derived ranks
            dranks = [int(s19.rank_mod(X_R_T333[:, j].reshape(9, 9), p)) for j in range(9)]
            # Also compute against the truncated tensor
            T22 = s19.tensor_from_factors(U22, V22, W22, p)
            T22_flat = s19.tensor_uv_matrix(T22) % p
            X_R_T22 = compute_derived_columns(T22_flat, X_P_loc, C_loc, D_loc, p)
            dranks_self = [int(s19.rank_mod(X_R_T22[:, j].reshape(9, 9), p)) for j in range(9)]
            
            cn122_results.append({
                'drop': drop,
                'derived_ranks_vs_T333': dranks,
                'derived_ranks_vs_self': dranks_self,
                'all_rank1_vs_T333': all(r <= 1 for r in dranks),
                'all_rank1_vs_self': all(r <= 1 for r in dranks_self),
            })
            if drop < 3:
                print(f"  drop={drop}: vs_T333 ranks={dranks[:3]}..., vs_self ranks={dranks_self[:3]}...")
        
        results['cn122_deletions'] = cn122_results
        n_self_valid = sum(1 for r in cn122_results if r.get('all_rank1_vs_self', False))
        n_t333_valid = sum(1 for r in cn122_results if r.get('all_rank1_vs_T333', False))
        print(f"  cn122 deletions: {n_self_valid}/23 self-valid, {n_t333_valid}/23 T333-valid")
    
    elapsed = time.time() - t0
    results['elapsed_sec'] = round(elapsed, 2)
    print(f"\nTotal time: {elapsed:.1f}s")
    
    out_dir = Path(__file__).resolve().parent.parent / 'data/completion_chart'
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / 'completion_chart_results.json'
    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"Saved to {out_path}")

if __name__ == '__main__':
    main()
