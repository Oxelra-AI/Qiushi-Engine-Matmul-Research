#!/usr/bin/env python3
"""Deep tangent space analysis for rank-r decompositions of the 3x3 matmul tensor.

Decomposes the Jacobian kernel at a rank-r decomposition point into:
  1. Rescaling directions (2r-dimensional torus action)
  2. Stabilizer directions (GL_3 x GL_3 x GL_3 sandwich action on decomp)
  3. Residual deformation directions

Then for each residual direction, tests whether it moves the two-factor
pairing ranks (necessary condition for rank shortening).

For the matmul tensor T_{3,3,3}:
  T(A,B) = AB  where A,B are 3x3 matrices
  Stabilizer in GL_9 x GL_9 x GL_9 includes GL_3 x GL_3 x GL_3 acting by:
    (P,Q,R): A -> PAQ^{-1}, B -> QBR^{-1}, C=AB -> PCBR^{-1} = PAR^{-1}
  In tensor coordinates:
    u_i -> (P otimes Q^{-T}) u_i
    v_i -> (Q otimes R^{-T}) v_i  
    w_i -> (P otimes R^{-T}) w_i
"""
import argparse, json, sys
from fractions import Fraction
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
    """Build the 729 x 27r Jacobian of F(params) = sum u_i ⊗ v_i ⊗ w_i.
    
    For term i, the three blocks of 9 columns each correspond to:
      d/du_{i,a}: e_a ⊗ v_i ⊗ w_i  for a=0..8
      d/dv_{i,b}: u_i ⊗ e_b ⊗ w_i  for b=0..8
      d/dw_{i,c}: u_i ⊗ v_i ⊗ e_c  for c=0..8
    
    Row index: (a,b,c) -> a*81 + b*9 + c
    """
    r = len(terms)
    rows = n**3  # 729
    cols = 3 * n * r  # 27r
    J = np.zeros((rows, cols), dtype=np.float64)
    
    for i, t in enumerate(terms):
        u = np.array(t['u'], dtype=np.float64)
        v = np.array(t['v'], dtype=np.float64)
        w = np.array(t['w'], dtype=np.float64)
        col_base = 27 * i
        
        # d/du_{i,a}: tensor e_a ⊗ v ⊗ w
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    J[a*81 + b*9 + c, col_base + a] += v[b] * w[c]
        
        # d/dv_{i,b}: tensor u ⊗ e_b ⊗ w
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    J[a*81 + b*9 + c, col_base + 9 + b] += u[a] * w[c]
        
        # d/dw_{i,c}: tensor u ⊗ v ⊗ e_c
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    J[a*81 + b*9 + c, col_base + 18 + c] += u[a] * v[b]
    
    return J


def build_rescaling_vectors(terms):
    """Build the 2r rescaling kernel vectors.
    
    For term i, two independent rescaling directions:
      dir1: (u_i, 0, -w_i)  in term i's 27-block
      dir2: (0, v_i, -w_i)  in term i's 27-block
    These correspond to (λu_i, v_i, w_i/λ) and (u_i, μv_i, w_i/μ).
    """
    r = len(terms)
    vecs = []
    for i, t in enumerate(terms):
        u = np.array(t['u'], dtype=np.float64)
        v = np.array(t['v'], dtype=np.float64)
        w = np.array(t['w'], dtype=np.float64)
        
        # Direction 1: (u_i, 0, -w_i) in block i
        d1 = np.zeros(27 * r)
        d1[27*i:27*i+9] = u
        d1[27*i+18:27*i+27] = -w
        vecs.append(d1)
        
        # Direction 2: (0, v_i, -w_i) in block i
        d2 = np.zeros(27 * r)
        d2[27*i+9:27*i+18] = v
        d2[27*i+18:27*i+27] = -w
        vecs.append(d2)
    
    return np.array(vecs)


def build_stabilizer_vectors(terms, n=3):
    """Build the 27 stabilizer kernel vectors from GL_3 x GL_3 x GL_3.
    
    The matmul tensor T has stabilizer containing GL_3 x GL_3 x GL_3
    acting as (P,Q,R) on each decomposition term:
      u_i (as 3x3 matrix) -> P * U_i * Q^{-1}   => du_i = dP*U_i - U_i*dQ
      v_i (as 3x3 matrix) -> Q * V_i * R^{-1}    => dv_i = dQ*V_i - V_i*dR
      w_i (as 3x3 matrix) -> P * W_i * R^{-1}    => dw_i = dP*W_i - W_i*dR
    
    where dP, dQ, dR are 3x3 matrices (27 parameters total).
    For each basis element E_{jk} of the 3x3 Lie algebra:
      dP = E_{jk}: du_i = E_{jk}*U_i, dv_i = 0, dw_i = E_{jk}*W_i
      dQ = E_{jk}: du_i = -U_i*E_{jk}, dv_i = E_{jk}*V_i, dw_i = 0
      dR = E_{jk}: du_i = 0, dv_i = -V_i*E_{jk}, dw_i = -W_i*E_{jk}
    """
    r = len(terms)
    vecs = []
    
    for i_term, t in enumerate(terms):
        U = np.array(t['u'], dtype=np.float64).reshape(n, n)
        V = np.array(t['v'], dtype=np.float64).reshape(n, n)
        W = np.array(t['w'], dtype=np.float64).reshape(n, n)
        if i_term == 0:
            # Initialize lists for accumulating over terms
            p_vecs = [np.zeros(27*r) for _ in range(n*n)]
            q_vecs = [np.zeros(27*r) for _ in range(n*n)]
            r_vecs = [np.zeros(27*r) for _ in range(n*n)]
        
        for j in range(n):
            for k in range(n):
                E = np.zeros((n, n))
                E[j, k] = 1.0
                idx = j * n + k
                
                # dP = E: du_i = E*U_i, dw_i = E*W_i
                du = (E @ U).flatten()
                dw = (E @ W).flatten()
                p_vecs[idx][27*i_term:27*i_term+9] += du
                p_vecs[idx][27*i_term+18:27*i_term+27] += dw
                
                # dQ = E: du_i = -U_i*E, dv_i = E*V_i
                du = -(U @ E).flatten()
                dv = (E @ V).flatten()
                q_vecs[idx][27*i_term:27*i_term+9] += du
                q_vecs[idx][27*i_term+9:27*i_term+18] += dv
                
                # dR = E: dv_i = -V_i*E, dw_i = -W_i*E
                dv = -(V @ E).flatten()
                dw = -(W @ E).flatten()
                r_vecs[idx][27*i_term+9:27*i_term+18] += dv
                r_vecs[idx][27*i_term+18:27*i_term+27] += dw
    
    all_stab = p_vecs + q_vecs + r_vecs  # 27 vectors
    return np.array(all_stab)


def pairing_rank_derivative(terms, direction, pair='uv'):
    """Compute the first-order effect on the two-factor pairing matrix rank.
    
    For pair='uv', the pairing matrix has columns u_i ⊗ v_i.
    A direction δ = (δu_1,...,δu_r, δv_1,...,δv_r, δw_1,...,δw_r)
    changes column i to (u_i+εδu_i) ⊗ (v_i+εδv_i) ≈ u_i⊗v_i + ε(δu_i⊗v_i + u_i⊗δv_i).
    
    The pairing matrix M has full rank iff no column is in the span of others.
    If M has rank 23 (full), then for M(ε) to drop to rank 22, we need
    det of some 23x23 submatrix to vanish at first order.
    
    Returns the rank of the derivative matrix [δu_i⊗v_i + u_i⊗δv_i]_i
    projected onto the kernel of M^T.
    """
    r = len(terms)
    
    if pair == 'uv':
        ki, kj = 'u', 'v'
    elif pair == 'uw':
        ki, kj = 'u', 'w'
    else:  # vw
        ki, kj = 'v', 'w'
    
    idx_i = {'u': 0, 'v': 9, 'w': 18}[ki]
    idx_j = {'u': 0, 'v': 9, 'w': 18}[kj]
    dim_i = 9
    dim_j = 9
    
    # Build pairing matrix M: columns are fi ⊗ gj for each term
    M = np.zeros((dim_i * dim_j, r))
    for t_idx, t in enumerate(terms):
        fi = np.array(t[ki], dtype=np.float64)
        gj = np.array(t[kj], dtype=np.float64)
        M[:, t_idx] = np.outer(fi, gj).flatten()
    
    # Build derivative matrix dM: columns are δfi ⊗ gj + fi ⊗ δgj
    dM = np.zeros((dim_i * dim_j, r))
    for t_idx, t in enumerate(terms):
        fi = np.array(t[ki], dtype=np.float64)
        gj = np.array(t[kj], dtype=np.float64)
        dfi = direction[27*t_idx + idx_i: 27*t_idx + idx_i + dim_i]
        dgj = direction[27*t_idx + idx_j: 27*t_idx + idx_j + dim_j]
        dM[:, t_idx] = np.outer(dfi, gj).flatten() + np.outer(fi, dgj).flatten()
    
    pairing_rank = np.linalg.matrix_rank(M)
    
    # If pairing rank is already < r, direction is less informative
    if pairing_rank < r:
        return {'pairing_rank': pairing_rank, 'already_deficient': True}
    
    # Project dM onto the left kernel of M
    U, S, Vt = np.linalg.svd(M, full_matrices=True)
    null_dim = dim_i * dim_j - pairing_rank
    if null_dim == 0:
        # M is full column rank AND full row rank? Only if r <= 81
        # Project dM onto left nullspace of M
        left_null = U[:, pairing_rank:]  # (81 x null_dim)
        projected = left_null.T @ dM  # (null_dim x r)
        proj_rank = np.linalg.matrix_rank(projected, tol=1e-10)
        return {
            'pairing_rank': pairing_rank,
            'left_null_dim': null_dim,
            'projected_deriv_rank': proj_rank,
            'rank_could_drop': proj_rank > 0,
        }
    else:
        left_null = U[:, pairing_rank:]
        projected = left_null.T @ dM
        proj_rank = np.linalg.matrix_rank(projected, tol=1e-10)
        return {
            'pairing_rank': pairing_rank,
            'left_null_dim': null_dim,
            'projected_deriv_rank': proj_rank,
            'rank_could_drop': proj_rank > 0,
        }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('scheme', help='QMM scheme file')
    ap.add_argument('--json-out', help='Output JSON file')
    args = ap.parse_args()
    
    S = parse_qmm(args.scheme)
    terms = S['terms']
    r = S['rank']
    n = 9
    print(f"Scheme: {args.scheme}, rank={r}, dims={S['dimensions']}")
    
    # 1. Build Jacobian and find kernel
    J = build_jacobian(terms)
    print(f"Jacobian shape: {J.shape}")
    jrank = np.linalg.matrix_rank(J, tol=1e-10)
    print(f"Jacobian rank: {jrank} / {J.shape[1]} (nullity = {J.shape[1] - jrank})")
    
    # Compute SVD to get kernel basis
    U_j, S_j, Vt_j = np.linalg.svd(J, full_matrices=True)
    kernel_basis = Vt_j[jrank:].T  # (27r x nullity)
    nullity = kernel_basis.shape[1]
    print(f"Kernel dimension: {nullity}")
    
    # 2. Build rescaling subspace
    R_vecs = build_rescaling_vectors(terms)
    # Project rescaling vectors into kernel
    R_in_kernel = kernel_basis.T @ R_vecs.T  # (nullity x 2r)
    rescaling_rank = np.linalg.matrix_rank(R_in_kernel, tol=1e-10)
    print(f"Rescaling directions in kernel: {rescaling_rank} / {2*r}")
    
    # 3. Build stabilizer subspace
    stab_vecs = build_stabilizer_vectors(terms)
    S_in_kernel = kernel_basis.T @ stab_vecs.T  # (nullity x 27)
    stab_rank = np.linalg.matrix_rank(S_in_kernel, tol=1e-10)
    print(f"Stabilizer directions in kernel: {stab_rank} / 27")
    
    # 4. Combined rescaling + stabilizer
    combined = np.hstack([R_in_kernel, S_in_kernel])  # (nullity x (2r+27))
    combined_rank = np.linalg.matrix_rank(combined, tol=1e-10)
    print(f"Combined rescaling+stabilizer rank in kernel: {combined_rank}")
    residual_dim = nullity - combined_rank
    print(f"Residual (genuine deformation) dimension: {residual_dim}")
    
    # 5. Extract residual directions
    if residual_dim > 0:
        # Find basis for the complement of combined in kernel
        U_c, S_c, Vt_c = np.linalg.svd(combined, full_matrices=True)
        # Columns of U_c beyond combined_rank span the complement
        residual_basis_in_kernel = U_c[:, combined_rank:]  # (nullity x residual_dim)
        # Map back to parameter space
        residual_dirs = kernel_basis @ residual_basis_in_kernel  # (27r x residual_dim)
        
        print(f"\nPairing rank-defect analysis for {residual_dim} residual directions:")
        for pair in ['uv', 'uw', 'vw']:
            rank_drop_count = 0
            for d_idx in range(min(residual_dim, 20)):  # analyze up to 20
                d = residual_dirs[:, d_idx]
                result = pairing_rank_derivative(terms, d, pair=pair)
                if result.get('rank_could_drop', False):
                    rank_drop_count += 1
            print(f"  {pair}: {rank_drop_count}/{min(residual_dim,20)} directions can drop pairing rank")
    
    # Collect results
    results = {
        'scheme': args.scheme,
        'rank': r,
        'jacobian_shape': list(J.shape),
        'jacobian_rank': int(jrank),
        'kernel_dim': int(nullity),
        'rescaling_dim_in_kernel': int(rescaling_rank),
        'stabilizer_dim_in_kernel': int(stab_rank),
        'combined_dim_in_kernel': int(combined_rank),
        'residual_deformation_dim': int(residual_dim),
    }
    
    if residual_dim > 0:
        pairing_results = {}
        for pair in ['uv', 'uw', 'vw']:
            drops = []
            for d_idx in range(residual_dim):
                d = residual_dirs[:, d_idx]
                result = pairing_rank_derivative(terms, d, pair=pair)
                drops.append(result)
            can_drop = sum(1 for d in drops if d.get('rank_could_drop', False))
            pairing_results[pair] = {
                'n_can_drop': can_drop,
                'n_tested': residual_dim,
            }
        results['pairing_defect_analysis'] = pairing_results
    
    def convert_np(obj):
        if isinstance(obj, (np.integer,)):
            return int(obj)
        if isinstance(obj, (np.floating,)):
            return float(obj)
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        return obj
    
    txt = json.dumps(results, indent=2, default=convert_np)
    print(f"\n{txt}")
    if args.json_out:
        Path(args.json_out).write_text(txt + '\n')
        print(f"Saved to {args.json_out}")


if __name__ == '__main__':
    main()
