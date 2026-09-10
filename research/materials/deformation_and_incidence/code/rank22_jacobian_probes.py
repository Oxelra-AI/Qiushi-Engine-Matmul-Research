#!/usr/bin/env python3
"""
Rank-22 incidence probes for T⟨3,3,3⟩ via Jacobian rank analysis.

Central computation: For the rank-r Brent system
  f_{a,b,c}(u,v,w) = T_{a,b,c} - sum_i u_{i,a} v_{i,b} w_{i,c}
the 729 × (r*27) Jacobian at a generic point over F_p determines the
dimension of the r-th secant variety (image of the parameterization).

After the shortening (eliminating W via a 22×22 UV minor),
the resulting 531-equation system in 396 UV variables has Jacobian rank
equal to rank(full_Jac) - 198.

This script:
  Part 1: Generic Jacobian rank for r=20,21,22,23,24 over several primes
  Part 2: Jacobian at cn122's first 22 terms; residual-in-image test
  Part 3: Shortened-system dimension estimate
"""
import numpy as np
import json, time, sys, os

# ── T⟨3,3,3⟩ ────────────────────────────────────────────────────────
def make_T333():
    """Build T⟨3,3,3⟩ as a 9×9×9 integer tensor."""
    T = np.zeros((9, 9, 9), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T

# ── QMM scheme loader ────────────────────────────────────────────────
def load_qmm(path):
    """Load a QMM_SCHEME_V1 file, return (U, V, W) each (r, 9)."""
    Us, Vs, Ws = [], [], []
    with open(path) as f:
        for line in f:
            parts = line.strip().split()
            if not parts:
                continue
            if parts[0] == 'u':
                Us.append([int(x) for x in parts[1:]])
            elif parts[0] == 'v':
                Vs.append([int(x) for x in parts[1:]])
            elif parts[0] == 'w':
                Ws.append([int(x) for x in parts[1:]])
    return np.array(Us), np.array(Vs), np.array(Ws)

# ── Gaussian elimination mod p ────────────────────────────────────────
def matrix_rank_Fp(M, p):
    """Rank of M over F_p via row reduction. M entries assumed in [0,p)."""
    A = M.copy()
    nrows, ncols = A.shape
    piv = 0
    for col in range(ncols):
        if piv >= nrows:
            break
        # find pivot
        nz = np.nonzero(A[piv:, col])[0]
        if len(nz) == 0:
            continue
        r0 = piv + int(nz[0])
        if r0 != piv:
            A[[piv, r0]] = A[[r0, piv]]
        inv = pow(int(A[piv, col]), p - 2, p)
        A[piv] = A[piv] * inv % p
        # eliminate
        factors = A[:, col].copy()
        factors[piv] = 0
        nz_rows = np.nonzero(factors)[0]
        if len(nz_rows) > 0:
            A[nz_rows] = (A[nz_rows] - np.outer(factors[nz_rows], A[piv])) % p
        piv += 1
    return piv

# ── Build the 729 × (r*27) Brent Jacobian over F_p ──────────────────
def brent_jacobian_Fp(U, V, W, p):
    """
    Jacobian of the Brent system at (U,V,W) over F_p.
    Returns (729, r*27) matrix with entries in [0, p).
    Column layout per term i: [u_{i,0}..u_{i,8}, v_{i,0}..v_{i,8}, w_{i,0}..w_{i,8}]
    Row layout: (a,b,c) → a*81 + b*9 + c
    """
    r = U.shape[0]
    J = np.zeros((729, r * 27), dtype=np.int64)
    
    # precompute row indices
    aa9 = np.arange(9, dtype=np.int64)
    
    for i in range(r):
        vw_i = (np.outer(V[i], W[i]).ravel()) % p   # 81-vector: v_{i,b}*w_{i,c}
        uw_i = (np.outer(U[i], W[i]).ravel()) % p   # 81-vector: u_{i,a}*w_{i,c}
        uv_i = (np.outer(U[i], V[i]).ravel()) % p   # 81-vector: u_{i,a}*v_{i,b}
        
        base = i * 27
        # U-columns: column base+a has (-v_{i,b}*w_{i,c}) at rows a*81..a*81+80
        for a in range(9):
            J[a*81:(a+1)*81, base + a] = (p - vw_i) % p
        
        # V-columns: column base+9+b has (-u_{i,a}*w_{i,c}) at rows a*81+b*9+c
        for b in range(9):
            rows = np.arange(9, dtype=np.int64) * 81 + b * 9  # a*81+b*9 for a=0..8
            for c in range(9):
                for a in range(9):
                    J[a*81 + b*9 + c, base + 9 + b] = (p - U[i, a] * W[i, c] % p) % p
        
        # W-columns: column base+18+c has (-u_{i,a}*v_{i,b}) at rows a*81+b*9+c
        for c in range(9):
            for a in range(9):
                for b in range(9):
                    J[a*81 + b*9 + c, base + 18 + c] = (p - U[i, a] * V[i, b] % p) % p
    
    return J % p

def brent_jacobian_Fp_fast(U, V, W, p):
    """Faster vectorized Jacobian construction."""
    r = U.shape[0]
    J = np.zeros((729, r * 27), dtype=np.int64)
    
    for i in range(r):
        base = i * 27
        u, v, w = U[i] % p, V[i] % p, W[i] % p
        
        vw = np.outer(v, w).ravel() % p  # 81
        
        # U-block: 9 columns, column a has (p-vw) at rows a*81..a*81+80
        for a in range(9):
            J[a*81:(a+1)*81, base + a] = (p - vw) % p
        
        # V-block: 9 columns, column b
        # Row (a,b,c) = a*81+b*9+c; entry = -(u_a * w_c) mod p
        uw_mat = np.outer(u, w) % p  # 9×9: uw_mat[a,c] = u_a * w_c mod p
        for b in range(9):
            # extract rows where second index = b
            # these are rows a*81+b*9+c for a in 0..8, c in 0..8
            # = reshape all 729 rows: row r -> (a,b',c) where a=r//81, b'=(r%81)//9, c=r%9
            # rows with b'=b form a 9×9 block in (a,c) space
            for a in range(9):
                J[a*81+b*9:a*81+b*9+9, base + 9 + b] = (p - uw_mat[a]) % p
        
        # W-block: 9 columns, column c
        uv_mat = np.outer(u, v) % p  # 9×9: uv_mat[a,b] = u_a * v_b mod p
        for c in range(9):
            for a in range(9):
                J[a*81:a*81+9*9:9, base + 18 + c]  # rows a*81+b*9+c for b=0..8
                # row a*81+b*9+c = a*81+c + b*9 ... no, let me be explicit
                pass
        # simpler: fill W-block entry by entry using vectorized ops
        uv_flat = np.outer(u, v).ravel() % p  # 81-vector: uv_flat[a*9+b] = u_a * v_b
        for c in range(9):
            # column base+18+c: row (a,b,c) has value -(u_a * v_b)
            # rows for fixed c: a*81+b*9+c for a=0..8, b=0..8 → 81 rows
            rows_c = np.arange(81, dtype=np.int64) * 9 + c  # wrong
            # Actually: row index = a*81 + b*9 + c
            # For a in 0..8, b in 0..8: row = a*81 + b*9 + c
            rows_c = np.array([a*81 + b*9 + c for a in range(9) for b in range(9)])
            J[rows_c, base + 18 + c] = (p - uv_flat) % p
    
    return J % p

def brent_jacobian_Fp_v3(U, V, W, p):
    """Cleaner vectorized Jacobian using reshape/index tricks."""
    r = U.shape[0]
    J = np.zeros((729, r * 27), dtype=np.int64)
    
    # Precompute index arrays for V-block and W-block
    # Row (a,b,c) has index a*81+b*9+c
    abc = np.arange(729, dtype=np.int64)
    a_idx = abc // 81
    b_idx = (abc % 81) // 9
    c_idx = abc % 9
    
    for i in range(r):
        base = i * 27
        u = U[i] % p
        v = V[i] % p
        w = W[i] % p
        
        # U-block: df_{abc}/du_{i,a'} = -delta(a,a') * v_b * w_c
        vw = (v[b_idx] * w[c_idx]) % p  # 729-vector
        for a in range(9):
            mask = (a_idx == a)
            J[mask, base + a] = (p - vw[mask]) % p
        
        # V-block: df_{abc}/dv_{i,b'} = -delta(b,b') * u_a * w_c
        uw = (u[a_idx] * w[c_idx]) % p  # 729-vector
        for b in range(9):
            mask = (b_idx == b)
            J[mask, base + 9 + b] = (p - uw[mask]) % p
        
        # W-block: df_{abc}/dw_{i,c'} = -delta(c,c') * u_a * v_b
        uv = (u[a_idx] * v[b_idx]) % p  # 729-vector
        for c in range(9):
            mask = (c_idx == c)
            J[mask, base + 18 + c] = (p - uv[mask]) % p
    
    return J % p

# ── Residual computation ──────────────────────────────────────────────
def brent_residual(U, V, W, T):
    """Compute T - sum_i u_i ⊗ v_i ⊗ w_i as a flat 729-vector."""
    r = U.shape[0]
    Tapprox = np.zeros((9,9,9), dtype=np.int64)
    for i in range(r):
        Tapprox += np.einsum('a,b,c->abc', U[i], V[i], W[i])
    return (T - Tapprox).ravel()

# ── Main experiment ───────────────────────────────────────────────────
def experiment_generic_jacobian_rank(primes, ranks, n_trials=20):
    """Part 1: Generic Jacobian rank of rank-r Brent system over F_p."""
    results = {}
    for p in primes:
        results[str(p)] = {}
        for r in ranks:
            trial_ranks = []
            t0 = time.time()
            for trial in range(n_trials):
                np.random.seed(1000*r + 100*p + trial)
                U = np.random.randint(0, p, (r, 9), dtype=np.int64)
                V = np.random.randint(0, p, (r, 9), dtype=np.int64)
                W = np.random.randint(0, p, (r, 9), dtype=np.int64)
                J = brent_jacobian_Fp_v3(U, V, W, p)
                rk = matrix_rank_Fp(J, p)
                trial_ranks.append(rk)
            elapsed = time.time() - t0
            max_rk = max(trial_ranks)
            min_rk = min(trial_ranks)
            jac_shape = (729, r*27)
            results[str(p)][str(r)] = {
                'jac_shape': list(jac_shape),
                'max_rank': max_rk,
                'min_rank': min_rk,
                'n_trials': n_trials,
                'all_ranks': trial_ranks,
                'elapsed_sec': round(elapsed, 2),
                'expected_secant_dim_proj': min(25*r - 1, 728),
                'expected_secant_dim_affine': min(25*r, 729),
            }
            print(f"  p={p} r={r}: Jac {jac_shape}, rank range [{min_rk},{max_rk}], "
                  f"expected affine dim {min(25*r,729)}, elapsed {elapsed:.1f}s")
    return results

def experiment_cn122_truncation(primes, scheme_path):
    """Part 2: Jacobian at cn122 with one term removed."""
    U, V, W = load_qmm(scheme_path)
    T = make_T333()
    
    # Verify the scheme first
    res = brent_residual(U, V, W, T)
    assert np.all(res == 0), f"cn122 verification failed: max residual {np.max(np.abs(res))}"
    
    results = {}
    for p in primes:
        p_results = []
        for drop_idx in range(23):
            # Remove term drop_idx → 22-term decomposition
            keep = [j for j in range(23) if j != drop_idx]
            U22 = U[keep] % p
            V22 = V[keep] % p
            W22 = W[keep] % p
            
            J = brent_jacobian_Fp_v3(U22, V22, W22, p)
            jac_rank = matrix_rank_Fp(J, p)
            
            # Residual = u_drop ⊗ v_drop ⊗ w_drop (the removed term)
            residual = np.einsum('a,b,c->abc', U[drop_idx], V[drop_idx], W[drop_idx]).ravel() % p
            
            # Check if residual is in column span of J
            # Augment J with the residual column and check rank increase
            J_aug = np.zeros((729, 22*27 + 1), dtype=np.int64)
            J_aug[:, :22*27] = J
            J_aug[:, -1] = (p - residual) % p  # negative because f = T - sum
            aug_rank = matrix_rank_Fp(J_aug, p)
            
            in_image = (aug_rank == jac_rank)
            
            p_results.append({
                'drop_term': drop_idx,
                'jac_rank': jac_rank,
                'aug_rank': aug_rank,
                'residual_in_image': in_image,
            })
        
        n_in_image = sum(1 for x in p_results if x['residual_in_image'])
        jac_ranks = [x['jac_rank'] for x in p_results]
        
        results[str(p)] = {
            'drop_results': p_results,
            'jac_rank_range': [min(jac_ranks), max(jac_ranks)],
            'residual_in_image_count': n_in_image,
        }
        print(f"  p={p}: Jac rank range [{min(jac_ranks)},{max(jac_ranks)}], "
              f"residual in image: {n_in_image}/23")
    
    return results

def experiment_shortened_system(primes, ranks_data):
    """Part 3: Interpret shortened system dimensions."""
    results = {}
    for p_str, p_data in ranks_data.items():
        for r_str, r_data in p_data.items():
            r = int(r_str)
            generic_rank = r_data['max_rank']
            n_w_vars = r * 9
            n_uv_vars = r * 18  # = r*27 - r*9
            shortened_rank = generic_rank - n_w_vars
            
            # Gauge: GL_3 on U-space (dim 9) + GL_3 on V-space (dim 9) + 
            # S_r permutation (discrete) + r term rescalings (projective: r-1)
            # but after W-elimination, rescaling acts as (lambda*u, lambda^{-1}*v)
            gl_gauge = 9 + 9  # GL_3 × GL_3
            rescale_gauge = r  # one per term
            total_gauge = gl_gauge + rescale_gauge
            
            effective_vars = n_uv_vars - total_gauge
            expected_dim = effective_vars - max(shortened_rank, 0)
            
            results[f"p={p_str}_r={r_str}"] = {
                'r': r,
                'generic_jac_rank': generic_rank,
                'n_w_eliminated': n_w_vars,
                'shortened_jac_rank': shortened_rank,
                'n_uv_vars': n_uv_vars,
                'gauge_dim': total_gauge,
                'effective_vars': effective_vars,
                'expected_moduli_dim': expected_dim,
                'note': 'positive => possibly nonempty; negative => generically empty'
            }
    return results


def main():
    base = os.path.dirname(os.path.abspath(__file__))
    ws = os.path.dirname(base)  # workspace
    
    outdir = os.path.join(ws, 'data', 'rank22_probes')
    os.makedirs(outdir, exist_ok=True)
    
    scheme_path = os.path.join(ws, 'data', 'cn122_r23_reproduce', 'scheme.qmm')
    
    # Use moderate primes to avoid int64 overflow: p < 2^31 ensures p^2 < 2^62
    primes = [65521, 104729, 1000003]
    ranks = [20, 21, 22, 23, 24]
    
    print("=" * 60)
    print("Part 1: Generic Jacobian rank of rank-r Brent system")
    print("=" * 60)
    t0 = time.time()
    generic_results = experiment_generic_jacobian_rank(primes, ranks, n_trials=10)
    print(f"\nPart 1 total: {time.time()-t0:.1f}s\n")
    
    print("=" * 60)
    print("Part 2: cn122 truncation analysis")
    print("=" * 60)
    t0 = time.time()
    cn122_results = experiment_cn122_truncation(primes[:2], scheme_path)  # 2 primes
    print(f"\nPart 2 total: {time.time()-t0:.1f}s\n")
    
    print("=" * 60)
    print("Part 3: Shortened system dimension estimates")
    print("=" * 60)
    shortened_results = experiment_shortened_system(primes, generic_results)
    for key, val in shortened_results.items():
        if 'r=22' in key:
            print(f"  {key}: shortened_rank={val['shortened_jac_rank']}, "
                  f"effective_vars={val['effective_vars']}, "
                  f"expected_moduli_dim={val['expected_moduli_dim']}")
    
    all_results = {
        'generic_jacobian_rank': generic_results,
        'cn122_truncation': cn122_results,
        'shortened_system_dimension': shortened_results,
        'tensor': '3x3_matrix_multiplication',
        'primes_used': primes,
    }
    
    outfile = os.path.join(outdir, 'rank22_jacobian_probes.json')
    with open(outfile, 'w') as f:
        json.dump(all_results, f, indent=2, sort_keys=True, default=int)
    print(f"\nAll results saved to {outfile}")

if __name__ == '__main__':
    main()
