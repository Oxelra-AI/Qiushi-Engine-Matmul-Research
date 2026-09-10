#!/usr/bin/env python3
"""Investigate the Kuranishi quadratic ideal V(I) for T_{3,3,3} rank-23 decompositions.

Given the coefficient tensor C[ℓ,j,k] of the Kuranishi ideal generators:
  f_ℓ(x) = Σ_{j,k} C[ℓ,j,k] x_j x_k

1. Compute the rank of the ideal generators (how many are independent)
2. Search for actual solutions of the quadratic system (points in V(I))
3. If solutions exist, verify they are genuine unobstructed directions
"""
import argparse, json, sys
from pathlib import Path
import numpy as np
from scipy.optimize import minimize


def parse_qmm(path):
    dims = None; rank = None; terms = []
    cur = None
    for raw in Path(path).read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith('#'): continue
        parts = line.split()
        if parts[0] == 'dimensions': dims = tuple(map(int, parts[1:4]))
        elif parts[0] == 'rank': rank = int(parts[1])
        elif parts[0] == 'term':
            if cur: terms.append(cur)
            cur = {'index': int(parts[1])}
        elif parts[0] in ('u','v','w'):
            cur[parts[0]] = [int(x) for x in parts[1:]]
    if cur: terms.append(cur)
    return {'dimensions': dims, 'rank': rank, 'terms': terms}


def build_jacobian(terms, n=9):
    r = len(terms)
    J = np.zeros((n**3, 3*n*r), dtype=np.float64)
    for i, t in enumerate(terms):
        u,v,w = [np.array(t[k], dtype=np.float64) for k in 'uvw']
        cb = 27*i
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    row = a*81+b*9+c
                    J[row,cb+a] += v[b]*w[c]
                    J[row,cb+9+b] += u[a]*w[c]
                    J[row,cb+18+c] += u[a]*v[b]
    return J


def build_symmetry_space(terms):
    """Build combined rescaling + stabilizer space vectors."""
    r = len(terms); n = 3
    vecs = []
    # Rescaling: 2r vectors
    for i, t in enumerate(terms):
        u,v,w = [np.array(t[k], dtype=np.float64) for k in 'uvw']
        d1 = np.zeros(27*r); d1[27*i:27*i+9] = u; d1[27*i+18:27*i+27] = -w
        d2 = np.zeros(27*r); d2[27*i+9:27*i+18] = v; d2[27*i+18:27*i+27] = -w
        vecs.extend([d1, d2])
    # Stabilizer: 27 vectors (dP, dQ, dR for each E_{jk})
    for jj in range(n):
        for kk in range(n):
            E = np.zeros((n,n)); E[jj,kk] = 1.0
            for gen_type in range(3):  # 0=dP, 1=dQ, 2=dR
                sv = np.zeros(27*r)
                for i, t in enumerate(terms):
                    U = np.array(t['u']).reshape(n,n).astype(float)
                    V = np.array(t['v']).reshape(n,n).astype(float)
                    W = np.array(t['w']).reshape(n,n).astype(float)
                    if gen_type == 0:  # dP
                        sv[27*i:27*i+9] += (E@U).flatten()
                        sv[27*i+18:27*i+27] += (E@W).flatten()
                    elif gen_type == 1:  # dQ
                        sv[27*i:27*i+9] += -(U@E).flatten()
                        sv[27*i+9:27*i+18] += (E@V).flatten()
                    else:  # dR
                        sv[27*i+9:27*i+18] += -(V@E).flatten()
                        sv[27*i+18:27*i+27] += -(W@E).flatten()
                vecs.append(sv)
    return np.array(vecs)


def compute_bilinear_Q(terms, d1, d2, n=9):
    r = len(terms)
    Q = np.zeros(n**3)
    for i, t in enumerate(terms):
        u,v,w = [np.array(t[k], dtype=np.float64) for k in 'uvw']
        du1,dv1,dw1 = d1[27*i:27*i+9], d1[27*i+9:27*i+18], d1[27*i+18:27*i+27]
        du2,dv2,dw2 = d2[27*i:27*i+9], d2[27*i+9:27*i+18], d2[27*i+18:27*i+27]
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    idx = a*81+b*9+c
                    Q[idx] += 0.5*(du1[a]*dv2[b]*w[c]+du2[a]*dv1[b]*w[c])
                    Q[idx] += 0.5*(du1[a]*v[b]*dw2[c]+du2[a]*v[b]*dw1[c])
                    Q[idx] += 0.5*(u[a]*dv1[b]*dw2[c]+u[a]*dv2[b]*dw1[c])
    return Q


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('scheme')
    ap.add_argument('--json-out')
    args = ap.parse_args()
    
    S = parse_qmm(args.scheme)
    terms = S['terms']
    r = S['rank']
    
    # Build Jacobian, kernel, cokernel
    J = build_jacobian(terms)
    jrank = np.linalg.matrix_rank(J, tol=1e-10)
    U_j, S_j, Vt_j = np.linalg.svd(J, full_matrices=True)
    kernel_basis = Vt_j[jrank:].T
    left_null = U_j[:, jrank:]
    nullity = kernel_basis.shape[1]
    coker_dim = left_null.shape[1]
    print(f"J rank={jrank}, ker={nullity}, coker={coker_dim}")
    
    # Symmetry subspace
    sym_vecs = build_symmetry_space(terms)
    sym_in_ker = kernel_basis.T @ sym_vecs.T
    sym_rank = np.linalg.matrix_rank(sym_in_ker, tol=1e-10)
    residual_dim = nullity - sym_rank
    print(f"Symmetry in kernel: {sym_rank}, residual: {residual_dim}")
    
    # Extract residual basis
    U_c, S_c, _ = np.linalg.svd(sym_in_ker, full_matrices=True)
    residual_in_ker = U_c[:, sym_rank:]
    residual_dirs = kernel_basis @ residual_in_ker
    m = residual_dim
    
    # Build Kuranishi coefficient matrix: 
    # F[ℓ, (j,k)] for upper-triangular (j,k) indices
    mono2 = [(j,k) for j in range(m) for k in range(j, m)]
    n_mono2 = len(mono2)
    mono2_idx = {(j,k): idx for idx, (j,k) in enumerate(mono2)}
    
    F = np.zeros((coker_dim, n_mono2))  # F[ℓ, mono_idx]
    
    print(f"\nComputing {coker_dim} generators × {n_mono2} monomials...")
    # Precompute all Q(r_j, r_k) projected to cokernel
    for j in range(m):
        for k in range(j, m):
            Q_jk = compute_bilinear_Q(terms, residual_dirs[:,j], residual_dirs[:,k])
            proj = left_null.T @ Q_jk
            idx = mono2_idx[(j,k)]
            F[:, idx] = proj
    
    # Rank of generators
    gen_rank = np.linalg.matrix_rank(F, tol=1e-10)
    print(f"Generator rank: {gen_rank} / {coker_dim} (over {n_mono2} monomial basis)")
    print(f"  -> {gen_rank} independent quadratic equations in {m} variables")
    
    # The quadratic system: F @ mono2_vec(x) = 0
    # where mono2_vec(x) = [x_j*x_k for (j,k) in mono2]
    # This is a linear system in the "Veronese coordinates" z_{jk} = x_j*x_k
    
    # Kernel of F in monomial space
    U_f, S_f, Vt_f = np.linalg.svd(F, full_matrices=True)
    f_rank = gen_rank
    mono_kernel = Vt_f[f_rank:].T  # (n_mono2 x (n_mono2 - f_rank))
    ker_dim = mono_kernel.shape[1]
    print(f"Monomial kernel dimension: {ker_dim}")
    print(f"  -> {ker_dim}-dim space of degree-2 forms vanishing on V(I)")
    print(f"  -> NOT all degree-2 forms, so V(I) could be nonempty")
    
    # Check: are there Veronese points (pure squares) in the kernel?
    # z_{jk} = x_j * x_k is a Veronese point. We need to find x such that
    # F @ veronese(x) = 0.
    
    def veronese_vec(x):
        """Map x ∈ R^m to upper-triangular product vector."""
        z = np.zeros(n_mono2)
        for idx, (j,k) in enumerate(mono2):
            z[idx] = x[j] * x[k]
        return z
    
    def loss(x):
        """Sum of squares of F @ veronese(x)."""
        z = veronese_vec(x)
        Fz = F @ z
        return 0.5 * np.sum(Fz**2)
    
    def grad_loss(x):
        """Gradient of loss."""
        z = veronese_vec(x)
        Fz = F @ z  # (coker_dim,)
        FtFz = F.T @ Fz  # (n_mono2,)
        # d(loss)/dx_s = Σ_{(j,k)} FtFz[(j,k)] * d(x_j*x_k)/dx_s
        g = np.zeros(m)
        for idx, (j,k) in enumerate(mono2):
            if j == k:
                g[j] += 2 * x[j] * FtFz[idx]
            else:
                g[j] += x[k] * FtFz[idx]
                g[k] += x[j] * FtFz[idx]
        return g
    
    # Multi-start optimization to find solutions
    print(f"\nSearching for solutions of quadratic system ({m} vars, {gen_rank} eqs)...")
    best_loss = float('inf')
    best_x = None
    n_starts = 200
    
    for trial in range(n_starts):
        np.random.seed(trial * 137 + 42)
        x0 = np.random.randn(m)
        x0 /= np.linalg.norm(x0)  # normalize to unit sphere
        
        result = minimize(loss, x0, jac=grad_loss, method='L-BFGS-B',
                         options={'maxiter': 2000, 'ftol': 1e-30, 'gtol': 1e-20})
        
        val = result.fun
        if val < best_loss:
            best_loss = val
            best_x = result.x
    
    print(f"Best loss after {n_starts} starts: {best_loss:.6e}")
    
    if best_loss < 1e-20:
        print("*** SOLUTION FOUND: V(I) is NONEMPTY ***")
        print("*** There exist unobstructed second-order deformation directions ***")
        solution_status = "nonempty"
        
        # Verify: compute Q(d,d) and check it's in Im(J)
        d = residual_dirs @ best_x
        Q_dd = compute_bilinear_Q(terms, d, d)
        proj = left_null.T @ Q_dd
        residual_norm = np.linalg.norm(proj)
        Q_norm = np.linalg.norm(Q_dd)
        print(f"  |Q(d,d)| = {Q_norm:.6e}")
        print(f"  |proj to coker| = {residual_norm:.6e}")
        print(f"  relative = {residual_norm/max(Q_norm,1e-15):.6e}")
    elif best_loss < 1e-10:
        print("Near-solution found (loss < 1e-10), needs higher precision")
        solution_status = "near_solution"
    else:
        print("No solution found in random search")
        solution_status = "no_solution_found"
    
    # Also try to find solutions on coordinate planes (sparser search)
    print("\nSparse direction search (2-variable combinations)...")
    best_sparse_loss = float('inf')
    best_sparse_pair = None
    for j in range(m):
        for k in range(j, m):
            # Try x = α e_j + β e_k on the unit circle
            for angle in np.linspace(0, np.pi, 20):
                x_try = np.zeros(m)
                x_try[j] = np.cos(angle)
                x_try[k] = np.sin(angle)
                val = loss(x_try)
                if val < best_sparse_loss:
                    best_sparse_loss = val
                    best_sparse_pair = (j, k, angle)
    
    print(f"Best 2-var loss: {best_sparse_loss:.6e} at pair {best_sparse_pair}")
    
    results = {
        'scheme': args.scheme,
        'jacobian_rank': int(jrank),
        'residual_dim': int(m),
        'cokernel_dim': int(coker_dim),
        'generator_rank': int(gen_rank),
        'monomial_kernel_dim': int(ker_dim),
        'solution_search': {
            'n_starts': n_starts,
            'best_loss': float(best_loss),
            'solution_status': solution_status,
            'best_sparse_loss': float(best_sparse_loss),
        },
    }
    
    txt = json.dumps(results, indent=2)
    print(f"\n{txt}")
    if args.json_out:
        Path(args.json_out).write_text(txt + '\n')


if __name__ == '__main__':
    main()
