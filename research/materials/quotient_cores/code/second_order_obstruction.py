#!/usr/bin/env python3
"""Second-order Brent-equation obstruction analysis for tensor rank deformations.

For a rank-r decomposition T = sum_i u_i ⊗ v_i ⊗ w_i, a first-order
deformation direction d = (δu_1,...,δw_r) in ker(J) represents an
infinitesimal movement preserving T at order ε. The second-order condition is:

  Q(d,d) + J · d2 = 0   where d2 = (δ²u_1,...,δ²w_r)/2

i.e., Q(d,d) must lie in the image of J, where

  Q(d,d)_{abc} = sum_i [δu_i[a]·δv_i[b]·w_i[c] + δu_i[a]·v_i[b]·δw_i[c]
                       + u_i[a]·δv_i[b]·δw_i[c]]

If Q(d,d) ∉ Im(J), then d is OBSTRUCTED at second order: no smooth
deformation path preserving the tensor exists in this direction. If
Q(d,d) ∈ Im(J) for all d in the residual kernel, the deformation space
is unobstructed at second order.

This is the critical test for whether rank-23 decompositions can deform
toward rank-22.
"""
import argparse, json, sys
from pathlib import Path
import numpy as np


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
            if cur is not None:
                terms.append(cur)
            cur = {'index': int(parts[1])}
        elif parts[0] in ('u', 'v', 'w'):
            cur[parts[0]] = [int(x) for x in parts[1:]]
    if cur is not None:
        terms.append(cur)
    return {'dimensions': dims, 'rank': rank, 'terms': terms}


def build_jacobian(terms, n=9):
    r = len(terms)
    J = np.zeros((n**3, 3*n*r), dtype=np.float64)
    for i, t in enumerate(terms):
        u = np.array(t['u'], dtype=np.float64)
        v = np.array(t['v'], dtype=np.float64)
        w = np.array(t['w'], dtype=np.float64)
        col_base = 27 * i
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    row = a*81 + b*9 + c
                    J[row, col_base + a] += v[b] * w[c]
                    J[row, col_base + 9 + b] += u[a] * w[c]
                    J[row, col_base + 18 + c] += u[a] * v[b]
    return J


def build_rescaling_vectors(terms):
    r = len(terms)
    vecs = []
    for i, t in enumerate(terms):
        u = np.array(t['u'], dtype=np.float64)
        v = np.array(t['v'], dtype=np.float64)
        w = np.array(t['w'], dtype=np.float64)
        d1 = np.zeros(27 * r); d1[27*i:27*i+9] = u; d1[27*i+18:27*i+27] = -w
        d2 = np.zeros(27 * r); d2[27*i+9:27*i+18] = v; d2[27*i+18:27*i+27] = -w
        vecs.extend([d1, d2])
    return np.array(vecs)


def build_stabilizer_vectors(terms, n=3):
    r = len(terms)
    p_vecs = [np.zeros(27*r) for _ in range(n*n)]
    q_vecs = [np.zeros(27*r) for _ in range(n*n)]
    r_vecs = [np.zeros(27*r) for _ in range(n*n)]
    for i_term, t in enumerate(terms):
        U = np.array(t['u'], dtype=np.float64).reshape(n, n)
        V = np.array(t['v'], dtype=np.float64).reshape(n, n)
        W = np.array(t['w'], dtype=np.float64).reshape(n, n)
        for j in range(n):
            for k in range(n):
                E = np.zeros((n, n)); E[j, k] = 1.0
                idx = j * n + k
                p_vecs[idx][27*i_term:27*i_term+9] += (E @ U).flatten()
                p_vecs[idx][27*i_term+18:27*i_term+27] += (E @ W).flatten()
                q_vecs[idx][27*i_term:27*i_term+9] += -(U @ E).flatten()
                q_vecs[idx][27*i_term+9:27*i_term+18] += (E @ V).flatten()
                r_vecs[idx][27*i_term+9:27*i_term+18] += -(V @ E).flatten()
                r_vecs[idx][27*i_term+18:27*i_term+27] += -(W @ E).flatten()
    return np.array(p_vecs + q_vecs + r_vecs)


def compute_Q(terms, d, n=9):
    """Compute the quadratic term Q(d,d) for second-order obstruction.
    
    Q(d,d)_{abc} = sum_i [δu_i[a]δv_i[b]w_i[c] + δu_i[a]v_i[b]δw_i[c] + u_i[a]δv_i[b]δw_i[c]]
    """
    r = len(terms)
    Q = np.zeros(n**3)
    for i, t in enumerate(terms):
        u = np.array(t['u'], dtype=np.float64)
        v = np.array(t['v'], dtype=np.float64)
        w = np.array(t['w'], dtype=np.float64)
        du = d[27*i:27*i+9]
        dv = d[27*i+9:27*i+18]
        dw = d[27*i+18:27*i+27]
        # Three cross-terms
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    idx = a*81 + b*9 + c
                    Q[idx] += du[a]*dv[b]*w[c] + du[a]*v[b]*dw[c] + u[a]*dv[b]*dw[c]
    return Q


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('scheme', help='QMM scheme file')
    ap.add_argument('--json-out', help='Output JSON file')
    args = ap.parse_args()
    
    S = parse_qmm(args.scheme)
    terms = S['terms']
    r = S['rank']
    n = 9
    print(f"Scheme: {args.scheme}, rank={r}")
    
    # Build Jacobian and find kernel
    J = build_jacobian(terms)
    jrank = np.linalg.matrix_rank(J, tol=1e-10)
    U_j, S_j, Vt_j = np.linalg.svd(J, full_matrices=True)
    kernel_basis = Vt_j[jrank:].T  # (27r x nullity)
    nullity = kernel_basis.shape[1]
    print(f"Jacobian rank={jrank}, nullity={nullity}")
    
    # Image basis (for checking Q(d,d) ∈ Im(J))
    image_basis = U_j[:, :jrank]  # (729 x jrank)
    
    # Build known symmetry subspace
    R_vecs = build_rescaling_vectors(terms)
    stab_vecs = build_stabilizer_vectors(terms)
    R_in_kernel = kernel_basis.T @ R_vecs.T
    S_in_kernel = kernel_basis.T @ stab_vecs.T
    combined = np.hstack([R_in_kernel, S_in_kernel])
    combined_rank = np.linalg.matrix_rank(combined, tol=1e-10)
    residual_dim = nullity - combined_rank
    print(f"Combined symmetry rank={combined_rank}, residual deformation dim={residual_dim}")
    
    if residual_dim == 0:
        print("No residual deformation directions — all kernel is symmetry.")
        results = {'scheme': args.scheme, 'rank': r, 'residual_dim': 0, 'obstructed': 'N/A'}
        if args.json_out:
            Path(args.json_out).write_text(json.dumps(results, indent=2) + '\n')
        return
    
    # Extract residual directions
    U_c, S_c, Vt_c = np.linalg.svd(combined, full_matrices=True)
    residual_in_kernel = U_c[:, combined_rank:]  # (nullity x residual_dim)
    residual_dirs = kernel_basis @ residual_in_kernel  # (27r x residual_dim)
    
    # For each residual direction, compute Q(d,d) and check if it's in Im(J)
    print(f"\n=== Second-order obstruction analysis ===")
    obstruction_results = []
    
    for d_idx in range(residual_dim):
        d = residual_dirs[:, d_idx]
        Q_dd = compute_Q(terms, d)
        
        # Project Q onto the orthogonal complement of Im(J)
        Q_in_image = image_basis @ (image_basis.T @ Q_dd)
        Q_residual = Q_dd - Q_in_image
        residual_norm = np.linalg.norm(Q_residual)
        Q_norm = np.linalg.norm(Q_dd)
        relative_residual = residual_norm / max(Q_norm, 1e-15)
        
        is_obstructed = relative_residual > 1e-8
        obstruction_results.append({
            'direction': d_idx,
            'Q_norm': float(Q_norm),
            'residual_norm': float(residual_norm),
            'relative_residual': float(relative_residual),
            'obstructed': bool(is_obstructed),
        })
        
        status = "OBSTRUCTED" if is_obstructed else "UNOBSTRUCTED"
        print(f"  dir {d_idx:2d}: |Q|={Q_norm:.6e}, |Q-proj|={residual_norm:.6e}, rel={relative_residual:.6e} → {status}")
    
    n_obstructed = sum(1 for r in obstruction_results if r['obstructed'])
    n_unobstructed = residual_dim - n_obstructed
    print(f"\nSummary: {n_obstructed} obstructed, {n_unobstructed} unobstructed out of {residual_dim}")
    
    # Also check mixed second-order: Q(d1, d2) for pairs
    if residual_dim >= 2:
        print(f"\n=== Cross-direction Q(d_i, d_j) obstruction (sample) ===")
        cross_obstructed = 0
        cross_total = 0
        for i in range(min(residual_dim, 10)):
            for j in range(i+1, min(residual_dim, 10)):
                d_mix = residual_dirs[:, i] + residual_dirs[:, j]
                Q_mix = compute_Q(terms, d_mix)
                # Q(d_i+d_j, d_i+d_j) = Q(d_i,d_i) + 2*Q(d_i,d_j) + Q(d_j,d_j)
                Q_ii = compute_Q(terms, residual_dirs[:, i])
                Q_jj = compute_Q(terms, residual_dirs[:, j])
                Q_cross = (Q_mix - Q_ii - Q_jj) / 2  # This is Q(d_i, d_j)
                Q_cross_in_im = image_basis @ (image_basis.T @ Q_cross)
                cross_res = np.linalg.norm(Q_cross - Q_cross_in_im)
                cross_norm = np.linalg.norm(Q_cross)
                rel = cross_res / max(cross_norm, 1e-15)
                if rel > 1e-8:
                    cross_obstructed += 1
                cross_total += 1
        print(f"  {cross_obstructed}/{cross_total} cross-terms obstructed")
    
    results = {
        'scheme': args.scheme,
        'rank': r,
        'jacobian_rank': int(jrank),
        'kernel_dim': int(nullity),
        'symmetry_dim': int(combined_rank),
        'residual_dim': int(residual_dim),
        'n_obstructed': int(n_obstructed),
        'n_unobstructed': int(n_unobstructed),
        'obstruction_details': obstruction_results,
    }
    
    txt = json.dumps(results, indent=2)
    print(f"\n{txt}")
    if args.json_out:
        Path(args.json_out).write_text(txt + '\n')
        print(f"Saved to {args.json_out}")


if __name__ == '__main__':
    main()
