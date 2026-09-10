#!/usr/bin/env python3
"""Targeted rank-19 search for the E11 core over F2.

Strategy 1: Analyze the deficiency-1 gap precisely, then search for coordinated
2-replacement that closes it.

Strategy 2: Random algebraic construction - choose u-factors, solve linear
system for (v,w).

Strategy 3: Start from the flip-cpd rank-21 scheme and search for 2-term
reductions using algebraic merging conditions.
"""
import json, sys, time
import numpy as np
from pathlib import Path

def load_core(path):
    T = np.load(path).astype(np.uint8)
    return T

def build_target_slices(T):
    """Build the 9 C-slices: S_l[i,j] = T[i,j,l] as 8x9 matrices."""
    m, n, p = T.shape
    slices = []
    for l in range(p):
        slices.append(T[:, :, l].copy())
    return slices

def f2_rank(M):
    """Compute rank of binary matrix over F2 using Gaussian elimination."""
    M = M.astype(np.uint8).copy()
    rows, cols = M.shape
    rank = 0
    for c in range(cols):
        # Find pivot
        found = False
        for r in range(rank, rows):
            if M[r, c]:
                found = True
                if r != rank:
                    M[[rank, r]] = M[[r, rank]]
                break
        if not found:
            continue
        # Eliminate
        for r in range(rows):
            if r != rank and M[r, c]:
                M[r] = M[r] ^ M[rank]
        rank += 1
    return rank

def f2_solve(A, b):
    """Solve Ax=b over F2. Returns solution and whether consistent."""
    m, n = A.shape
    Ab = np.hstack([A, b.reshape(-1, 1)]).astype(np.uint8)
    rows, cols = Ab.shape
    pivot_col = [-1] * rows
    rank = 0
    for c in range(n):
        found = False
        for r in range(rank, rows):
            if Ab[r, c]:
                found = True
                if r != rank:
                    Ab[[rank, r]] = Ab[[r, rank]]
                break
        if not found:
            continue
        pivot_col[rank] = c
        for r in range(rows):
            if r != rank and Ab[r, c]:
                Ab[r] = Ab[r] ^ Ab[rank]
        rank += 1
    # Check consistency
    for r in range(rank, rows):
        if Ab[r, -1]:
            return None, False  # Inconsistent
    # Back-substitute (pick one solution with free vars = 0)
    x = np.zeros(n, dtype=np.uint8)
    for r in range(rank):
        c = pivot_col[r]
        if c >= 0:
            x[c] = Ab[r, -1]
    return x, True

def enumerate_rank1_f2(m, n):
    """Enumerate all nonzero rank-1 m×n matrices over F2."""
    # Each is u⊗v where u ∈ F2^m \ {0}, v ∈ F2^n \ {0}
    results = []
    for ui in range(1, 2**m):
        u = np.array([(ui >> b) & 1 for b in range(m)], dtype=np.uint8)
        for vi in range(1, 2**n):
            v = np.array([(vi >> b) & 1 for b in range(n)], dtype=np.uint8)
            results.append((u, v, np.outer(u, v).astype(np.uint8)))
    return results

def strategy1_gap_analysis(T, known_scheme_path):
    """Analyze the deficiency-1 gap from the known 21-term E11 restriction."""
    # Load known scheme
    m, n, p = T.shape
    target_slices = build_target_slices(T)
    
    # Build target matrix: stack C-slices as columns of an 8*9 × 9 matrix
    # Actually: for the span approach, we flatten each C-slice to m*n = 72 dims
    S = np.column_stack([s.ravel() for s in target_slices])  # (72, 9) target
    
    print(f"Target matrix S: shape={S.shape}, F2-rank={f2_rank(S)}")
    return S

def strategy2_random_u_solve(T, rank, n_trials=100000, seed=42):
    """Random algebraic construction: choose u-factors, solve for (v,w)."""
    m, n, p = T.shape
    rng = np.random.RandomState(seed)
    best_residual = float('inf')
    best_scheme = None
    
    t0 = time.time()
    for trial in range(n_trials):
        # Random u-factors: r nonzero vectors in F2^m
        us = np.zeros((rank, m), dtype=np.uint8)
        for k in range(rank):
            while True:
                u = rng.randint(0, 2, m).astype(np.uint8)
                if u.any():
                    us[k] = u
                    break
        
        # For fixed u, the Brent equations T[i,j,l] = Σ_k u_k[i]*v_k[j]*w_k[l]
        # become: for each (j,l), Σ_{k: u_k[i]=1} v_k[j]*w_k[l] = T[i,j,l]
        # This is bilinear in v, w — still hard.
        # 
        # Simpler: fix u AND try to solve for v_k[j]*w_k[l] = p_k[j,l]
        # where p_k is the "pair matrix" for term k.
        # Then Σ_{k: u_k[i]=1} p_k[j,l] = T[i,j,l] for all i,j,l
        # This is a linear system in the p_k (which are 9*9 = 81 binary variables each)
        # with the constraint that each p_k is rank-1 over F2.
        
        # Build the linear system: for each (i,j,l), Σ_{k:u_k[i]=1} p_k[j,l] = T[i,j,l]
        # Variables: p_k[j,l] for k=0..rank-1, j=0..n-1, l=0..p-1
        # Total variables: rank * n * p = 19 * 81 = 1539
        # Equations: m * n * p = 648
        
        n_vars = rank * n * p
        n_eqs = m * n * p
        A_sys = np.zeros((n_eqs, n_vars), dtype=np.uint8)
        b_sys = np.zeros(n_eqs, dtype=np.uint8)
        
        eq_idx = 0
        for i in range(m):
            for j in range(n):
                for l in range(p):
                    b_sys[eq_idx] = T[i, j, l]
                    for k in range(rank):
                        if us[k, i]:
                            var_idx = k * n * p + j * p + l
                            A_sys[eq_idx, var_idx] = 1
                    eq_idx += 1
        
        # Solve the linear system over F2
        x_sol, consistent = f2_solve(A_sys, b_sys)
        
        if not consistent:
            continue
        
        # Extract pair matrices and check if each is rank-1
        all_rank1 = True
        vs = np.zeros((rank, n), dtype=np.uint8)
        ws = np.zeros((rank, p), dtype=np.uint8)
        
        for k in range(rank):
            pk = x_sol[k*n*p:(k+1)*n*p].reshape(n, p)
            rk = f2_rank(pk)
            if rk > 1:
                all_rank1 = False
                break
            elif rk == 1:
                # Extract v, w from the rank-1 matrix
                for j in range(n):
                    if pk[j].any():
                        vs[k] = np.zeros(n, dtype=np.uint8)
                        vs[k, j] = 1
                        # Actually, need to find the rank-1 factorization
                        # Find first nonzero row
                        row_idx = -1
                        for jj in range(n):
                            if pk[jj].any():
                                row_idx = jj
                                break
                        if row_idx >= 0:
                            ws[k] = pk[row_idx]
                            for jj in range(n):
                                if np.array_equal(pk[jj], pk[row_idx]):
                                    vs[k, jj] = 1
                                elif pk[jj].any():
                                    # Not rank-1!
                                    all_rank1 = False
                                    break
                        break
            # rk == 0: term contributes nothing, vs[k]=ws[k]=0
        
        if all_rank1:
            # Verify!
            T_recon = np.zeros_like(T)
            for k in range(rank):
                T_recon += np.einsum('a,b,c->abc', us[k], vs[k], ws[k])
            T_recon = T_recon % 2
            residual = np.sum(T_recon != T)
            if residual == 0:
                elapsed = time.time() - t0
                print(f"FOUND rank-{rank} decomposition at trial {trial} ({elapsed:.1f}s)!")
                return {'found': True, 'trial': trial, 'elapsed': elapsed,
                        'us': us.tolist(), 'vs': vs.tolist(), 'ws': ws.tolist()}
            else:
                if residual < best_residual:
                    best_residual = residual
                    print(f"  trial {trial}: consistent but rank-1 check residual={residual}")
        
        if trial % 10000 == 0 and trial > 0:
            elapsed = time.time() - t0
            print(f"  trial {trial}/{n_trials} ({elapsed:.1f}s) best_residual={best_residual}")
    
    elapsed = time.time() - t0
    return {'found': False, 'n_trials': n_trials, 'elapsed': elapsed, 'best_residual': int(best_residual)}

def strategy3_span_targeted(T, rank, seed=123):
    """Targeted span-based search: use random u-factors and check if the
    resulting v⊗w column space spans the target."""
    m, n, p = T.shape
    rng = np.random.RandomState(seed)
    
    # Build target: 9 C-slices, each 8×9 → flatten to 72-dim vectors
    # We need rank rank-one 8×9 matrices whose F2 span includes all 9 target slices
    target_vecs = []
    for l in range(p):
        target_vecs.append(T[:, :, l].ravel())
    S = np.column_stack(target_vecs)  # (72, 9)
    target_rank = f2_rank(S)
    print(f"Target span: {S.shape}, rank={target_rank}")
    
    # For the two-factor approach: need rank rank-one 8×9 matrices
    # whose column space contains all columns of S
    
    n_trials = 500000
    best_deficiency = p  # worst case: miss all slices
    t0 = time.time()
    
    for trial in range(n_trials):
        # Choose r random nonzero u ∈ F2^m and v ∈ F2^n
        us = []
        vs = []
        for k in range(rank):
            while True:
                u = rng.randint(0, 2, m).astype(np.uint8)
                if u.any():
                    break
            while True:
                v = rng.randint(0, 2, n).astype(np.uint8)
                if v.any():
                    break
            us.append(u)
            vs.append(v)
        
        # Build the matrix K: columns are u_k ⊗ v_k (flattened 8×9 → 72-dim)
        K = np.column_stack([np.outer(us[k], vs[k]).ravel() for k in range(rank)])  # (72, rank)
        
        # Check if target is in col span of K over F2
        KS = np.hstack([K, S]) % 2  # (72, rank+9)
        rKS = f2_rank(KS)
        rK = f2_rank(K)
        deficiency = rKS - rK  # number of target columns NOT in span of K
        
        if deficiency < best_deficiency:
            best_deficiency = deficiency
            elapsed = time.time() - t0
            print(f"  trial {trial}: deficiency={deficiency} (rK={rK}, rKS={rKS}) [{elapsed:.1f}s]")
            
            if deficiency == 0:
                # K spans the target! Now solve for w
                print("  SPAN FOUND! Solving for w...")
                # For each target slice l, find coefficients α_k such that
                # Σ_k α_k * (u_k ⊗ v_k) = S[:, l] over F2
                ws = np.zeros((rank, p), dtype=np.uint8)
                for l in range(p):
                    alpha, consistent = f2_solve(K, S[:, l])
                    if not consistent:
                        print(f"    Slice {l}: INCONSISTENT (shouldn't happen with deficiency 0)")
                        break
                    ws[:, l] = alpha
                
                # Verify
                T_recon = np.zeros_like(T)
                for k in range(rank):
                    T_recon += np.einsum('a,b,c->abc', us[k], vs[k], ws[k])
                T_recon = T_recon % 2
                residual = np.sum(T_recon != T)
                
                if residual == 0:
                    elapsed = time.time() - t0
                    print(f"FOUND rank-{rank} decomposition at trial {trial} ({elapsed:.1f}s)!")
                    return {'found': True, 'trial': trial, 'elapsed': elapsed,
                            'us': [u.tolist() for u in us],
                            'vs': [v.tolist() for v in vs],
                            'ws': ws.tolist()}
                else:
                    print(f"    Verification failed: residual={residual}")
        
        if trial % 50000 == 0 and trial > 0:
            elapsed = time.time() - t0
            print(f"  checkpoint trial {trial}/{n_trials} best_def={best_deficiency} [{elapsed:.1f}s]")
    
    elapsed = time.time() - t0
    return {'found': False, 'n_trials': n_trials, 'elapsed': elapsed,
            'best_deficiency': int(best_deficiency)}

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('core_npy')
    ap.add_argument('--rank', type=int, default=19)
    ap.add_argument('--strategy', choices=['gap', 'random_u', 'span'], default='span')
    ap.add_argument('--trials', type=int, default=200000)
    ap.add_argument('--seed', type=int, default=42)
    ap.add_argument('--json-out', required=True)
    args = ap.parse_args()
    
    T = load_core(args.core_npy)
    print(f"Core tensor: shape={T.shape}, nnz={np.count_nonzero(T)}")
    
    if args.strategy == 'gap':
        S = strategy1_gap_analysis(T, None)
        result = {'strategy': 'gap', 'target_shape': list(S.shape), 'target_rank': int(f2_rank(S))}
    elif args.strategy == 'random_u':
        result = strategy2_random_u_solve(T, args.rank, n_trials=args.trials, seed=args.seed)
        result['strategy'] = 'random_u'
    elif args.strategy == 'span':
        result = strategy3_span_targeted(T, args.rank, seed=args.seed)
        result['strategy'] = 'span'
    
    result['core'] = args.core_npy
    result['rank'] = args.rank
    Path(args.json_out).write_text(json.dumps(result, indent=2) + '\n')
    print(f"Wrote {args.json_out}")

if __name__ == '__main__':
    main()
