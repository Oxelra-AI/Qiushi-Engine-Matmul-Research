#!/usr/bin/env python3
"""
analysis: Newton iteration on the Z₄-equivariant exterior fiber
and Koszul rank computation at fiber points.

Over F_p, finds random points on the exterior fiber (solution variety of
S4·(A∧B∧C) = ω in sl₃) near the BILR point, then computes the Koszul-Young
flattening rank of the residual cubic at each point to test whether
the Waring rank can drop from 11 to ≤10.
"""
import numpy as np
from itertools import combinations
import json, sys, time
from pathlib import Path

WS = Path('.')
OUT = WS / 'data' / 'z4_char0_model'
OUT.mkdir(parents=True, exist_ok=True)

n = 3; N = 9; D_L3 = 84  # C(9,3)

def det3(m):
    return int(m[0,0]*(m[1,1]*m[2,2]-m[1,2]*m[2,1])
              -m[0,1]*(m[1,0]*m[2,2]-m[1,2]*m[2,0])
              +m[0,2]*(m[1,0]*m[2,1]-m[1,1]*m[2,0]))

TRIPLES = list(combinations(range(N), 3))

def wedge3(v1, v2, v3, p_mod=0):
    r = np.zeros(D_L3, dtype=np.int64)
    for i,(a,b,c) in enumerate(TRIPLES):
        m = np.array([[v1[a],v2[a],v3[a]],[v1[b],v2[b],v3[b]],[v1[c],v2[c],v3[c]]], dtype=np.int64)
        r[i] = det3(m)
    if p_mod: r = r % p_mod
    return r

def rank_mod(M, p):
    m = M.copy().astype(np.int64) % p
    nr, nc = m.shape; row = 0
    for col in range(nc):
        found = -1
        for r in range(row, nr):
            if m[r,col] % p: found=r; break
        if found<0: continue
        m[[row,found]] = m[[found,row]]
        inv = pow(int(m[row,col]%p), p-2, p)
        m[row] = m[row]*inv%p
        for r in range(nr):
            if r!=row and m[r,col]%p:
                m[r] = (m[r] - int(m[r,col])*m[row])%p
        row += 1
    return row

def solve_mod(A, b, p):
    """Solve A·x ≡ b mod p for x in row space of A. Returns x or None."""
    nr, nc = A.shape
    # Augment [A | b]
    aug = np.zeros((nr, nc+1), dtype=np.int64)
    aug[:,:nc] = A % p; aug[:,nc] = b % p
    # RREF
    pivot_cols = []; row = 0
    for col in range(nc):
        found = -1
        for r in range(row, nr):
            if aug[r,col]%p: found=r; break
        if found<0: continue
        aug[[row,found]] = aug[[found,row]]
        inv = pow(int(aug[row,col]%p), p-2, p)
        aug[row] = aug[row]*inv%p
        for r in range(nr):
            if r!=row and aug[r,col]%p:
                aug[r] = (aug[r] - int(aug[r,col])*aug[row])%p
        pivot_cols.append(col); row += 1
    # Check consistency: remaining rows should have zero augmented column
    for r in range(row, nr):
        if aug[r,nc]%p: return None  # inconsistent
    x = np.zeros(nc, dtype=np.int64)
    for i, pc in enumerate(pivot_cols):
        x[pc] = aug[i,nc] % p
    return x

def build_sl3_basis():
    """8-dim traceless basis for gl3."""
    basis = []
    for i in range(3):
        for j in range(3):
            if i != j:
                v = np.zeros(9,dtype=np.int64); v[3*i+j] = 1; basis.append(v)
    h1 = np.zeros(9,dtype=np.int64); h1[0]=1; h1[4]=-1; basis.append(h1)
    h2 = np.zeros(9,dtype=np.int64); h2[4]=1; h2[8]=-1; basis.append(h2)
    return np.array(basis).T  # 9×8

def build_koszul_residual(orbit_forms, p):
    """Build the 1134×1134 Koszul-Young flattening of the residual cubic.
    
    orbit_forms: list of 4 triples (lA, lB, lC) where lA is a 9-vector
    The diagonal polynomial is tr(M³) = Σ M_{ij}M_{jk}M_{ki}
    The residual = tr(M³) - 3 * Σ_{orbits} lA·x * lB·x * lC·x
    
    Returns the Koszul matrix mod p.
    """
    # Build tr(M³) as a symmetric 3-tensor in 9 variables
    # M = Σ x_i e_i where e_i = e_{ab} with a=i//3, b=i%3
    # tr(M³) = Σ_{a,b,c} M_{ab}M_{bc}M_{ca} = Σ x_{3a+b} x_{3b+c} x_{3c+a}
    
    # Build coefficient array for the cubic: T[i,j,k] = coefficient of x_i x_j x_k
    T_cubic = np.zeros((N,N,N), dtype=np.int64)
    for a in range(n):
        for b in range(n):
            for c in range(n):
                i = 3*a+b; j = 3*b+c; k = 3*c+a
                T_cubic[i,j,k] += 1
    
    # Subtract orbit contributions: 3 * Σ_k lA_k * lB_k * lC_k (outer product)
    for lA, lB, lC in orbit_forms:
        for i in range(N):
            for j in range(N):
                for k in range(N):
                    T_cubic[i,j,k] -= 3 * int(lA[i]) * int(lB[j]) * int(lC[k])
    
    T_cubic = T_cubic % p
    
    # Build Koszul-Young flattening: Λ⁴V ⊗ V* → Λ⁵V ⊗ V
    # Actually use the standard Young flattening for cubics
    # For a cubic C ∈ Sym³(V), V = K^9:
    # Koszul: Λ^{k+1}V ⊗ S_{d-k}V → Λ^k V ⊗ S_{d-k+1}V
    # For d=3, k=3: Λ⁴V ⊗ S₀V → Λ³V ⊗ S₁V, i.e., Λ⁴V → Λ³V ⊗ V
    # Dims: C(9,4)=126 → C(9,3)*9 = 84*9 = 756. Not 1134.
    
    # The 1134×1134 flattening from analysis used a different Young diagram.
    # 1134 = 126*9 = C(9,4)*9. So it's the map:
    # Λ⁴V ⊗ V → Λ⁵V ⊗ Sym²V (or similar)
    # Wait: 126 = C(9,4), 9*126 = 1134.
    # The standard Koszul flattening for Sym³(K⁹) is:
    # φ_C: V* → Sym²(V): (duality) C contracted once.
    # Or: Λ²V* ⊗ K → Λ¹V ⊗ Sym²V → ...
    
    # Actually from analysis, the Koszul-Young flattening shape was 1134×1134
    # which is C(9,4) × 9 = 126 × 9 = 1134 for both rows and columns.
    # This matches Λ⁴(V) ⊗ V* → Λ⁵(V) ⊗ V
    # But C(9,5)=126 as well, so it's 126*9 = 1134 rows and columns.
    
    # Let me use the same construction as the analysis script.
    # The Koszul map for a 3-form f ∈ Sym³(V*):
    # κ: Λ⁴V → Λ³V ⊗ V = Λ³V ⊗ V
    # This has dimension C(9,4) × C(9,3)*9 = 126 → 756. Not 1134.
    
    # Or the Young flattening:
    # φ_{2,1}: V ⊗ V → Sym²V  (for degree 3, using the (2,1) partition)
    # 9*9 → C(9+1,2) = 45. Not 1134.
    
    # Let me look at how analysis computed it.
    # From cyclic_koszul_scan.py
    # Actually I should look at the script. Let me use a simpler approach.
    
    # Standard catalecticant/apolarity: for a cubic f = Σ T_{ijk} x_i x_j x_k,
    # the catalecticant is the 9×45 matrix mapping V → Sym²V*.
    # Cat(f)_{i,(jk)} = T_{ijk} (symmetrized)
    # But 9×45 gives rank at most 9. Not useful for distinguishing 10 vs 11 cubes.
    
    # The Koszul-Young flattening is a stronger flattening.
    # 1134 = 126*9 suggests using Λ⁴V ⊗ V* or similar.
    
    # Actually, 1134 = 9 * 126 = 9 * C(9,4). 
    # The standard Koszul complex for Sym^d on V = K^n:
    # ... → Λ^(p+1) V ⊗ Sym^(d-1) V → Λ^p V ⊗ Sym^d V → ...
    # For d=3, p=3: Λ⁴V ⊗ Sym²V → Λ³V ⊗ Sym³V
    # Dims: C(9,4)*C(9+1,2) = 126*45 = 5670 → C(9,3)*C(9+2,3) = 84*165 = 13860
    # Not 1134.
    
    # Hmm. Let me just use the catalecticant (9×45) as a quick proxy.
    # A 10-cube sum has catalecticant rank ≤ 10.
    # A 11-cube sum has catalecticant rank 11 (if generic).
    # The BILR residual has catalecticant rank... from analysis: catalecticant rank 2 for (2,7).
    # For (11,4): catalecticant rank should be ≤ 11.
    # Actually for a sum of 11 cubes in 9 vars, catalecticant rank ≤ 11.
    # But 11 > 9 so catalecticant (9×45) has rank ≤ 9. Not useful.
    
    # OK, the Koszul-Young from analysis must be a specific higher flattening.
    # Let me check the actual script.
    return None

def main():
    p = 65521
    
    # Setup
    a0 = np.array([[0,0,-1],[1,0,-1],[0,1,-1]], dtype=np.int64)
    I3 = np.eye(3,dtype=np.int64)
    a0p = [I3.copy()]
    for _ in range(3): a0p.append((a0p[-1]@a0).astype(np.int64))
    a0inv = a0p[3]
    
    Ad = np.zeros((N,N),dtype=np.int64)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    Ad[n*i+j,n*k+l] = a0[i,k]*a0inv[l,j]
    Ad_pow = [np.eye(N,dtype=np.int64)]
    for _ in range(3): Ad_pow.append((Ad_pow[-1]@Ad).astype(np.int64))
    
    # L3 and S4
    L3 = np.zeros((D_L3,D_L3), dtype=np.int64)
    for j,(p1,p2,p3) in enumerate(TRIPLES):
        L3[:,j] = wedge3(Ad[:,p1], Ad[:,p2], Ad[:,p3])
    L3_2 = (L3@L3).astype(np.int64)
    L3_3 = (L3_2@L3).astype(np.int64)
    S4 = np.eye(D_L3,dtype=np.int64) + L3 + L3_2 + L3_3
    
    # Cartan form
    omega = np.zeros(D_L3, dtype=np.int64)
    for idx,(pi,qi,ri) in enumerate(TRIPLES):
        a,b=pi//n,pi%n; c,d=qi//n,qi%n; e,f=ri//n,ri%n
        omega[idx] = (1 if d==e and b==c and a==f else 0) - (1 if f==c and b==e and a==d else 0)
    
    # BILR point
    scheme = json.load(open(WS/'data/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json'))
    reps = scheme['free_orbit_representatives']
    U0 = np.array(reps[0]['U'],dtype=np.int64).flatten()
    V0 = np.array(reps[0]['V'],dtype=np.int64).flatten()
    W0 = np.array(reps[0]['W'],dtype=np.int64).flatten()
    
    # Verify
    w0 = wedge3(U0,V0,W0)
    s4w0 = S4 @ w0
    resid0 = s4w0 - omega
    print(f"BILR check: S4·(A∧B∧C) - ω max |entry| = {np.abs(resid0).max()}")
    
    # sl3 basis
    sl3B = build_sl3_basis()  # 9×8
    
    # sl3 Jacobian at BILR
    def compute_sl3_jacobian(U, V, W):
        J = np.zeros((D_L3, 24), dtype=np.int64)
        for k in range(8):
            e = sl3B[:,k]
            J[:,k]    = S4 @ wedge3(e, V, W)
            J[:,8+k]  = S4 @ wedge3(U, e, W)
            J[:,16+k] = S4 @ wedge3(U, V, e)
        return J
    
    J0 = compute_sl3_jacobian(U0, V0, W0)
    jr0 = rank_mod(J0, p)
    print(f"BILR Jacobian rank (sl3): {jr0}")
    
    # Kernel of J0
    from itertools import combinations as comb
    def kernel_mod_fn(M, pp):
        m = M.copy().astype(np.int64) % pp
        nr,nc = m.shape; pivot_cols = []; row = 0
        for col in range(nc):
            found = -1
            for r in range(row, nr):
                if m[r,col]%pp: found=r; break
            if found<0: continue
            m[[row,found]] = m[[found,row]]
            inv = pow(int(m[row,col]%pp), pp-2, pp)
            m[row] = m[row]*inv%pp
            for r in range(nr):
                if r!=row and m[r,col]%pp:
                    m[r] = (m[r] - int(m[r,col])*m[row])%pp
            pivot_cols.append(col); row += 1
        free = [c for c in range(nc) if c not in pivot_cols]
        if not free: return np.zeros((nc,0),dtype=np.int64)
        basis = np.zeros((nc,len(free)),dtype=np.int64)
        for k,fc in enumerate(free):
            basis[fc,k] = 1
            for i,pc in enumerate(pivot_cols):
                basis[pc,k] = (-m[i,fc])%pp
        return basis
    
    ker0 = kernel_mod_fn(J0, p)
    print(f"Kernel dimension: {ker0.shape[1]}")
    
    # sl3 coords to gl3 coords
    def sl3_to_gl3(coords_24):
        """Convert 24 sl3 coordinates to 3 flat gl3 vectors (traceless)."""
        U = (sl3B @ coords_24[:8].astype(np.int64)) 
        V = (sl3B @ coords_24[8:16].astype(np.int64))
        W = (sl3B @ coords_24[16:].astype(np.int64))
        return U, V, W
    
    # Newton iteration to find fiber points
    def find_fiber_point(U_init, V_init, W_init, max_iter=20):
        """Newton iterate from (U,V,W) to find S4·(A∧B∧C)=ω on sl3."""
        U = U_init.copy() % p; V = V_init.copy() % p; W = W_init.copy() % p
        for it in range(max_iter):
            w = wedge3(U, V, W, p)
            F = ((S4 @ w) - omega) % p
            resid = sum(1 for x in F if x%p != 0)
            if resid == 0:
                return U%p, V%p, W%p, it
            
            J = np.zeros((D_L3, 24), dtype=np.int64)
            for k in range(8):
                e = sl3B[:,k]
                J[:,k]    = (S4 @ wedge3(e, V, W, p)) % p
                J[:,8+k]  = (S4 @ wedge3(U, e, W, p)) % p
                J[:,16+k] = (S4 @ wedge3(U, V, e, p)) % p
            
            delta = solve_mod(J, (-F)%p, p)
            if delta is None:
                return None, None, None, -1
            
            dU, dV, dW = sl3_to_gl3(delta)
            U = (U + dU) % p
            V = (V + dV) % p
            W = (W + dW) % p
        
        return None, None, None, -2

    # Test Newton at BILR (should converge in 0 iterations)
    Ut, Vt, Wt, iters = find_fiber_point(U0, V0, W0)
    print(f"Newton at BILR: converged in {iters} iterations")
    
    # Find random fiber points
    np.random.seed(2024)
    results = []
    
    print(f"\n{'='*60}")
    print("Searching for fiber points via Newton iteration")
    print(f"{'='*60}")
    
    n_trials = 8
    for trial in range(n_trials):
        # Random perturbation in kernel
        coeffs = np.random.randint(1, p, size=ker0.shape[1], dtype=np.int64)
        delta_sl3 = np.zeros(24, dtype=np.int64)
        for k in range(ker0.shape[1]):
            delta_sl3 = (delta_sl3 + int(coeffs[k]) * ker0[:,k]) % p
        
        # Scale perturbation (use random nonzero scale)
        scale = np.random.randint(1, p)
        delta_sl3 = (delta_sl3 * scale) % p
        
        dU, dV, dW = sl3_to_gl3(delta_sl3)
        U_start = (U0 + dU) % p
        V_start = (V0 + dV) % p
        W_start = (W0 + dW) % p
        
        t0 = time.time()
        Uf, Vf, Wf, iters = find_fiber_point(U_start, V_start, W_start)
        dt = time.time() - t0
        
        if Uf is not None:
            # Verify
            w = wedge3(Uf, Vf, Wf, p)
            check = ((S4 @ w) - omega) % p
            ok = np.all(check == 0)
            
            # Check if different from BILR
            diff_U = (Uf - U0%p) % p
            diff_V = (Vf - V0%p) % p  
            diff_W = (Wf - W0%p) % p
            is_bilr = np.all(diff_U==0) and np.all(diff_V==0) and np.all(diff_W==0)
            
            # Compute Jacobian rank at new point
            Jf = compute_sl3_jacobian(Uf, Vf, Wf)
            jr_f = rank_mod(Jf, p)
            
            print(f"  Trial {trial}: Newton {iters} iters, {dt:.2f}s, verified={ok}, "
                  f"is_BILR={is_bilr}, Jac_rank={jr_f}")
            
            if ok and not is_bilr:
                results.append({
                    'trial': trial, 'newton_iters': iters,
                    'U': Uf.tolist(), 'V': Vf.tolist(), 'W': Wf.tolist(),
                    'jac_rank': jr_f
                })
        else:
            print(f"  Trial {trial}: Newton FAILED (iters={iters})")
    
    # Summary
    print(f"\nFound {len(results)} non-BILR fiber points")
    if results:
        jac_ranks = [r['jac_rank'] for r in results]
        print(f"Jacobian ranks: {jac_ranks}")
    
    # Save
    summary = {
        'prime': p,
        'bilr_jac_rank': int(jr0),
        'bilr_kernel_dim': int(ker0.shape[1]),
        'fiber_points_found': len(results),
        'results': results[:5]  # save first 5
    }
    (OUT/'newton_fiber_search.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(f"\nSaved {OUT/'newton_fiber_search.json'}")

if __name__ == '__main__':
    main()
