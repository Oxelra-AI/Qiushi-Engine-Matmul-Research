#!/usr/bin/env python3
"""Rigorous second-order obstruction via Kuranishi ideal and Macaulay certificate.

Corrects the initial analysis by:
1. Verifying every stabilizer vector J·s ≈ 0 (sanity check)
2. Computing the FULL Kuranishi quadratic ideal on the residual space
3. Checking V_P(I) = ∅ via Macaulay matrix rank (not just basis vectors)

The Kuranishi ideal: for residual basis r_1,...,r_m and cokernel basis L,
  f_ℓ(x) = L_ℓ^T · Q(Σ x_j r_j, Σ x_j r_j) = Σ_{j≤k} c_{ℓjk} x_j x_k

V_P(I) = ∅ iff the ideal I=(f_1,...,f_c) contains all sufficiently high-degree forms.
Certificate: the Macaulay matrix M_D has full row rank at some degree D.

At degree D, M_D maps {g_ℓ · h : deg h = D-2, ℓ=1..c} → {monomials of degree D}.
If rank(M_D) = binomial(m+D-1, D), then V_P(I) = ∅.
"""
import argparse, json, sys
from pathlib import Path
import numpy as np
from itertools import combinations_with_replacement
from math import comb


def parse_qmm(path):
    dims = None; rank = None; terms = []
    cur = None
    for raw in Path(path).read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith('#'):
            continue
        parts = line.split()
        if parts[0] == 'dimensions':
            dims = tuple(map(int, parts[1:4]))
        elif parts[0] == 'rank':
            rank = int(parts[1])
        elif parts[0] == 'term':
            if cur is not None: terms.append(cur)
            cur = {'index': int(parts[1])}
        elif parts[0] in ('u', 'v', 'w'):
            cur[parts[0]] = [int(x) for x in parts[1:]]
    if cur is not None: terms.append(cur)
    return {'dimensions': dims, 'rank': rank, 'terms': terms}


def build_jacobian(terms, n=9):
    r = len(terms)
    J = np.zeros((n**3, 3*n*r), dtype=np.float64)
    for i, t in enumerate(terms):
        u = np.array(t['u'], dtype=np.float64)
        v = np.array(t['v'], dtype=np.float64)
        w = np.array(t['w'], dtype=np.float64)
        cb = 27 * i
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    row = a*81 + b*9 + c
                    J[row, cb + a] += v[b] * w[c]
                    J[row, cb + 9 + b] += u[a] * w[c]
                    J[row, cb + 18 + c] += u[a] * v[b]
    return J


def build_rescaling(terms):
    r = len(terms)
    vecs = []
    for i, t in enumerate(terms):
        u, v, w = [np.array(t[k], dtype=np.float64) for k in 'uvw']
        d1 = np.zeros(27*r); d1[27*i:27*i+9] = u; d1[27*i+18:27*i+27] = -w
        d2 = np.zeros(27*r); d2[27*i+9:27*i+18] = v; d2[27*i+18:27*i+27] = -w
        vecs.extend([d1, d2])
    return np.array(vecs)


def build_stabilizer(terms, n=3):
    """Correct sandwich stabilizer: δU=pU-Uq, δV=qV-Vr, δW=pW-Wr"""
    r = len(terms)
    all_vecs = []
    for jj in range(n):
        for kk in range(n):
            E = np.zeros((n, n)); E[jj, kk] = 1.0
            # dP = E
            dp = np.zeros(27*r)
            for i, t in enumerate(terms):
                U = np.array(t['u']).reshape(n,n).astype(float)
                W = np.array(t['w']).reshape(n,n).astype(float)
                dp[27*i:27*i+9] += (E @ U).flatten()      # pU
                dp[27*i+18:27*i+27] += (E @ W).flatten()   # pW
            all_vecs.append(dp)
            # dQ = E
            dq = np.zeros(27*r)
            for i, t in enumerate(terms):
                U = np.array(t['u']).reshape(n,n).astype(float)
                V = np.array(t['v']).reshape(n,n).astype(float)
                dq[27*i:27*i+9] += -(U @ E).flatten()      # -Uq
                dq[27*i+9:27*i+18] += (E @ V).flatten()    # qV
            all_vecs.append(dq)
            # dR = E
            dr = np.zeros(27*r)
            for i, t in enumerate(terms):
                V = np.array(t['v']).reshape(n,n).astype(float)
                W = np.array(t['w']).reshape(n,n).astype(float)
                dr[27*i+9:27*i+18] += -(V @ E).flatten()   # -Vr
                dr[27*i+18:27*i+27] += -(W @ E).flatten()   # -Wr
            all_vecs.append(dr)
    return np.array(all_vecs)


def verify_stabilizer_in_kernel(J, stab_vecs):
    """Verify each stabilizer vector is (approximately) in ker(J)."""
    residuals = []
    for idx, s in enumerate(stab_vecs):
        r = np.linalg.norm(J @ s) / max(np.linalg.norm(s), 1e-15)
        residuals.append(float(r))
    return residuals


def compute_bilinear_Q(terms, d1, d2, n=9):
    """Symmetric bilinear form Q(d1,d2): the polarization of the quadratic Brent error."""
    r = len(terms)
    Q = np.zeros(n**3)
    for i, t in enumerate(terms):
        u, v, w = [np.array(t[k], dtype=np.float64) for k in 'uvw']
        du1, dv1, dw1 = d1[27*i:27*i+9], d1[27*i+9:27*i+18], d1[27*i+18:27*i+27]
        du2, dv2, dw2 = d2[27*i:27*i+9], d2[27*i+9:27*i+18], d2[27*i+18:27*i+27]
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    idx = a*81 + b*9 + c
                    # Symmetrized: (Q(d1,d2) + Q(d2,d1))/2
                    Q[idx] += 0.5*(du1[a]*dv2[b]*w[c] + du2[a]*dv1[b]*w[c])
                    Q[idx] += 0.5*(du1[a]*v[b]*dw2[c] + du2[a]*v[b]*dw1[c])
                    Q[idx] += 0.5*(u[a]*dv1[b]*dw2[c] + u[a]*dv2[b]*dw1[c])
    return Q


def build_kuranishi_coefficients(terms, residual_dirs, left_null):
    """Build the Kuranishi quadratic ideal coefficients.
    
    For residual basis r_1,...,r_m and left null space basis L:
      f_ℓ(x) = Σ_{j,k} c_{ℓjk} x_j x_k
    where c_{ℓjk} = L_ℓ^T Q(r_j, r_k)
    
    Returns coefficient tensor C[ℓ, j, k] (symmetric in j,k)
    """
    m = residual_dirs.shape[1]
    c_dim = left_null.shape[1]
    
    # Precompute all Q(r_j, r_k) projected to cokernel
    C = np.zeros((c_dim, m, m))
    for j in range(m):
        for k in range(j, m):
            Q_jk = compute_bilinear_Q(terms, residual_dirs[:, j], residual_dirs[:, k])
            proj = left_null.T @ Q_jk  # (c_dim,)
            C[:, j, k] = proj
            C[:, k, j] = proj
    return C


def build_macaulay_matrix_degree3(C, m, c_dim):
    """Build the degree-3 Macaulay matrix.
    
    Rows: degree-3 monomials x^α with |α|=3, indexed by sorted tuples
    Columns: f_ℓ * x_s for ℓ=1..c_dim, s=1..m
    
    The entry at (monomial x^α, column (ℓ,s)) is the coefficient of x^α in f_ℓ·x_s.
    f_ℓ·x_s = Σ_{j≤k} c_{ℓjk}·x_j·x_k·x_s
    """
    # Generate degree-3 monomial index: sorted tuples (i,j,k) with 0≤i≤j≤k<m
    mono3 = list(combinations_with_replacement(range(m), 3))
    n_mono3 = len(mono3)
    n_cols = c_dim * m
    
    # Build monomial lookup
    mono_idx = {tuple(sorted(mono)): idx for idx, mono in enumerate(mono3)}
    
    M = np.zeros((n_mono3, n_cols))
    
    for ell in range(c_dim):
        for s in range(m):
            col = ell * m + s
            # f_ℓ * x_s = Σ_{j,k} c_{ℓjk} x_j x_k x_s
            for j in range(m):
                for k in range(m):
                    coeff = C[ell, j, k]
                    if abs(coeff) < 1e-15:
                        continue
                    mono = tuple(sorted([j, k, s]))
                    row = mono_idx[mono]
                    # Count multiplicity for symmetric tensor
                    M[row, col] += coeff
    
    return M, mono3


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('scheme')
    ap.add_argument('--json-out')
    args = ap.parse_args()
    
    S = parse_qmm(args.scheme)
    terms = S['terms']
    r = S['rank']
    n = 9
    print(f"Scheme: {args.scheme}, rank={r}")
    
    # Build Jacobian
    J = build_jacobian(terms)
    jrank = np.linalg.matrix_rank(J, tol=1e-10)
    U_j, S_j, Vt_j = np.linalg.svd(J, full_matrices=True)
    kernel_basis = Vt_j[jrank:].T
    image_basis = U_j[:, :jrank]
    left_null = U_j[:, jrank:]
    nullity = kernel_basis.shape[1]
    coker_dim = left_null.shape[1]
    print(f"J rank={jrank}, ker={nullity}, coker={coker_dim}")
    
    # Verify stabilizer
    stab_vecs = build_stabilizer(terms)
    stab_residuals = verify_stabilizer_in_kernel(J, stab_vecs)
    n_in_ker = sum(1 for r in stab_residuals if r < 1e-8)
    max_res = max(stab_residuals)
    print(f"Stabilizer: {n_in_ker}/27 in kernel (max relative residual: {max_res:.2e})")
    
    # Report which are NOT in kernel
    for idx, res in enumerate(stab_residuals):
        if res > 1e-8:
            kind = ['dP', 'dQ', 'dR'][idx % 3]
            entry = idx // 3
            j, k = divmod(entry, 3)
            print(f"  NOT in ker: stab vec {idx} ({kind} E_{j}{k}), rel residual = {res:.6e}")
    
    # Build rescaling
    resc_vecs = build_rescaling(terms)
    
    # Project all to kernel coordinates
    R_in_ker = kernel_basis.T @ resc_vecs.T
    S_in_ker = kernel_basis.T @ stab_vecs.T
    combined = np.hstack([R_in_ker, S_in_ker])
    combined_rank = np.linalg.matrix_rank(combined, tol=1e-10)
    residual_dim = nullity - combined_rank
    print(f"Rescaling in ker: {np.linalg.matrix_rank(R_in_ker, tol=1e-10)}/46")
    print(f"Stab in ker: {np.linalg.matrix_rank(S_in_ker, tol=1e-10)}/27")
    print(f"Combined rank: {combined_rank}, residual dim: {residual_dim}")
    
    if residual_dim == 0:
        print("No residual directions.")
        return
    
    # Extract residual basis
    U_c, S_c, _ = np.linalg.svd(combined, full_matrices=True)
    residual_in_ker = U_c[:, combined_rank:]
    residual_dirs = kernel_basis @ residual_in_ker
    
    # Build FULL Kuranishi coefficient tensor
    print(f"\nBuilding Kuranishi ideal ({coker_dim} generators, {residual_dim} variables)...")
    C = build_kuranishi_coefficients(terms, residual_dirs, left_null)
    
    # Check individual basis vectors (for comparison with old results)
    n_basis_obstructed = 0
    for j in range(residual_dim):
        proj = C[:, j, j]
        if np.linalg.norm(proj) > 1e-10:
            n_basis_obstructed += 1
    print(f"Basis vectors obstructed: {n_basis_obstructed}/{residual_dim}")
    
    # Build degree-3 Macaulay matrix
    n_mono3 = comb(residual_dim + 2, 3)
    n_cols = coker_dim * residual_dim
    print(f"\nMacaulay degree 3: {n_mono3} monomials × {n_cols} columns")
    
    if n_cols < n_mono3:
        print(f"WARNING: columns ({n_cols}) < rows ({n_mono3}), degree 3 cannot certify emptiness")
        can_certify_3 = False
    else:
        can_certify_3 = True
    
    M3, mono3 = build_macaulay_matrix_degree3(C, residual_dim, coker_dim)
    mac3_rank = np.linalg.matrix_rank(M3, tol=1e-10)
    print(f"Macaulay degree 3: rank {mac3_rank} / {n_mono3} (need {n_mono3} for certificate)")
    
    if mac3_rank == n_mono3:
        print("*** DEGREE-3 MACAULAY CERTIFICATE: V_P(I) = ∅ ***")
        print("*** All second-order obstructions are universal — no direction escapes ***")
        certificate = "degree_3_macaulay_fullrank"
    elif mac3_rank < n_mono3:
        defect = n_mono3 - mac3_rank
        print(f"Degree-3 Macaulay defect: {defect} (ideal does NOT contain all degree-3 forms)")
        print("Need to check degree 4 or use Gröbner basis for conclusive result")
        certificate = "inconclusive_degree3"
    
    results = {
        'scheme': args.scheme,
        'rank': r,
        'jacobian_rank': int(jrank),
        'kernel_dim': int(nullity),
        'cokernel_dim': int(coker_dim),
        'stabilizer_in_kernel': int(n_in_ker),
        'stabilizer_max_residual': float(max_res),
        'rescaling_in_kernel': int(np.linalg.matrix_rank(R_in_ker, tol=1e-10)),
        'combined_rank': int(combined_rank),
        'residual_dim': int(residual_dim),
        'basis_obstructed': int(n_basis_obstructed),
        'macaulay_degree3': {
            'n_monomials': int(n_mono3),
            'n_columns': int(n_cols),
            'rank': int(mac3_rank),
            'certificate': certificate,
        }
    }
    
    txt = json.dumps(results, indent=2)
    print(f"\n{txt}")
    if args.json_out:
        Path(args.json_out).write_text(txt + '\n')


if __name__ == '__main__':
    main()
