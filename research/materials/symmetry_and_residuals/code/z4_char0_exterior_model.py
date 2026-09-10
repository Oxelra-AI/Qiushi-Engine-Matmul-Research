#!/usr/bin/env python3
"""
analysis: Characteristic-zero Z₄-equivariant exterior model.

Build the character-block decomposition of Ad(a₀) on gl₃,
the Z₄-invariant Λ³ projector, verify the BILR exterior equation,
compute the exterior fiber dimension, and analyze stabilizer/genuine directions.

All key computations are exact (integer or modular).
"""
import numpy as np
from itertools import combinations
import json, sys
from pathlib import Path

WS = Path('.')
OUT = WS / 'data' / 'z4_char0_model'
OUT.mkdir(parents=True, exist_ok=True)

def det3(m):
    return int(m[0,0]*(m[1,1]*m[2,2]-m[1,2]*m[2,1])
              -m[0,1]*(m[1,0]*m[2,2]-m[1,2]*m[2,0])
              +m[0,2]*(m[1,0]*m[2,1]-m[1,1]*m[2,0]))

def wedge3(v1, v2, v3, triples):
    r = np.zeros(len(triples), dtype=np.int64)
    for i,(p,q,s) in enumerate(triples):
        m = np.array([[v1[p],v2[p],v3[p]],[v1[q],v2[q],v3[q]],[v1[s],v2[s],v3[s]]], dtype=np.int64)
        r[i] = det3(m)
    return r

def rank_mod(M, p):
    m = np.array(M, dtype=np.int64) % p
    nr,nc = m.shape; row = 0
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

def kernel_mod(M, p):
    m = np.array(M, dtype=np.int64) % p
    nr,nc = m.shape; pivot_cols = []; row = 0
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
        pivot_cols.append(col); row += 1
    rk = len(pivot_cols)
    free = [c for c in range(nc) if c not in pivot_cols]
    if not free: return np.zeros((nc,0), dtype=np.int64), rk
    basis = np.zeros((nc, len(free)), dtype=np.int64)
    for k,fc in enumerate(free):
        basis[fc,k] = 1
        for i,pc in enumerate(pivot_cols):
            basis[pc,k] = (-m[i,fc]) % p
    return basis, rk

def main():
    n=3; N=9; p = 65521
    
    # === a₀ (companion of t³+t²+t+1) ===
    a0 = np.array([[0,0,-1],[1,0,-1],[0,1,-1]], dtype=np.int64)
    I3 = np.eye(3,dtype=np.int64)
    a0p = [I3.copy()]
    for _ in range(3): a0p.append((a0p[-1]@a0).astype(np.int64))
    assert np.array_equal(a0p[3]@a0, I3)
    a0inv = a0p[3]
    print(f"a₀ = {a0.tolist()}")
    print(f"a₀⁻¹ = a₀³ = {a0inv.tolist()}")
    print(f"charpoly eigenvalues: -1, ±i  (t³+t²+t+1 = (t+1)(t²+1))")
    
    # === Ad(a₀) on gl₃ ===
    Ad = np.zeros((N,N),dtype=np.int64)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    Ad[n*i+j,n*k+l] = a0[i,k]*a0inv[l,j]
    
    # Ad powers
    Ad_pow = [np.eye(N,dtype=np.int64)]
    for _ in range(3): Ad_pow.append((Ad_pow[-1]@Ad).astype(np.int64))
    
    # Eigenspace dims
    I9 = np.eye(N,dtype=np.int64)
    d1 = N - rank_mod(Ad-I9, p)
    dm1 = N - rank_mod(Ad+I9, p)
    Ad2 = (Ad@Ad).astype(np.int64)
    dpi = N - rank_mod(Ad2+I9, p)
    print(f"\nAd(a₀) eigenspace dimensions:")
    print(f"  V₁ (eig 1):   {d1}  [centralizer = span{{I, a₀, a₀²}}]")
    print(f"  V₋₁ (eig -1): {dm1}")
    print(f"  V±ᵢ (eig ±i): {dpi}  [combined real subspace]")
    print(f"  Total: {d1+dm1+dpi} = {N}")
    
    # Verify centralizer
    cent = [I3.flatten(), a0.flatten(), (a0@a0).flatten().astype(np.int64)]
    for k,c in enumerate(cent):
        assert np.all(Ad@c == c), f"Cent basis {k} not fixed"
    print("  Centralizer {I,a₀,a₀²} verified fixed by Ad(a₀)")
    
    # === Λ³(gl₃) ===
    triples = list(combinations(range(N),3))
    D = len(triples)  # 84
    triple_idx = {t:i for i,t in enumerate(triples)}
    print(f"\nΛ³(gl₃) dimension: {D}")
    
    # Λ³(Ad a₀) matrix
    L3 = np.zeros((D,D), dtype=np.int64)
    for j,(p1,p2,p3) in enumerate(triples):
        L3[:,j] = wedge3(Ad[:,p1], Ad[:,p2], Ad[:,p3], triples)
    L3_2 = (L3@L3).astype(np.int64)
    L3_3 = (L3_2@L3).astype(np.int64)
    assert np.array_equal(L3_2@L3_2, np.eye(D,dtype=np.int64)), "Λ³(Ad)⁴≠I"
    
    # Z₄ sum S4 = I + L3 + L3² + L3³
    S4 = np.eye(D,dtype=np.int64) + L3 + L3_2 + L3_3
    assert np.all((S4@S4).astype(np.int64) == 4*S4), "S4²≠4S4"
    inv_dim = rank_mod(S4, p)
    print(f"Λ³(Ad a₀)⁴ = I verified")
    print(f"Z₄-invariant dim of Λ³(gl₃): {inv_dim}")
    
    # === Cartan form ω ===
    omega = np.zeros(D, dtype=np.int64)
    for idx,(pi,qi,ri) in enumerate(triples):
        a,b = pi//n, pi%n; c,d = qi//n, qi%n; e,f = ri//n, ri%n
        # κ(e_{ab},e_{cd},e_{ef}) = tr(e_{ab}[e_{cd},e_{ef}])
        #   = δ_{de}δ_{bc}δ_{af} - δ_{fc}δ_{be}δ_{ad}
        omega[idx] = (1 if d==e and b==c and a==f else 0) - \
                     (1 if f==c and b==e and a==d else 0)
    nz = int(np.count_nonzero(omega))
    print(f"\nCartan form ω: {nz} nonzero entries (values: {sorted(set(omega[omega!=0].tolist()))})")
    assert np.array_equal(L3@omega, omega), "ω not Z₄-inv"
    print("ω is Z₄-invariant: verified")
    
    # ι_tr(ω) = 0 check
    diag_indices = [0, 4, 8]  # e_{00}, e_{11}, e_{22}
    trace_ok = True
    for q1 in range(N):
        for q2 in range(q1+1, N):
            val = 0
            for di in diag_indices:
                triple = tuple(sorted([di,q1,q2]))
                if len(set(triple))<3: continue
                tidx = triple_idx.get(triple)
                if tidx is None: continue
                orig = [di,q1,q2]; s=sorted(orig)
                # Parity of permutation
                inv=0
                for x in range(3):
                    for y in range(x+1,3):
                        if orig[x]>orig[y]: inv+=1
                sign = 1 if inv%2==0 else -1
                val += sign * omega[tidx]
            if val != 0: trace_ok = False; break
        if not trace_ok: break
    print(f"ι_tr(ω) = 0: {trace_ok}")
    
    # === BILR scheme ===
    scheme = json.load(open(WS/'data/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json'))
    reps = scheme['free_orbit_representatives']
    
    # Load all 4 reps
    rep_UVW = []
    for rep in reps:
        U = np.array(rep['U'],dtype=np.int64).flatten()
        V = np.array(rep['V'],dtype=np.int64).flatten()
        W = np.array(rep['W'],dtype=np.int64).flatten()
        rep_UVW.append((U,V,W))
    
    # === Z₄ orbit structure check ===
    print(f"\n{'='*50}")
    print("Z₄ orbit structure of BILR free reps")
    print(f"{'='*50}")
    U0,V0,W0 = rep_UVW[0]
    
    # Compute Ad^k images of rep0
    for k in range(4):
        Uk = Ad_pow[k] @ U0
        Vk = Ad_pow[k] @ V0
        Wk = Ad_pow[k] @ W0
        Ud,Vd,Wd = rep_UVW[k]
        # Direct match
        direct = np.array_equal(Uk,Ud) and np.array_equal(Vk,Vd) and np.array_equal(Wk,Wd)
        # Cyclic permutation match
        cyc_match = "none"
        for label,(Ut,Vt,Wt) in [("UVW",(Ud,Vd,Wd)),("VWU",(Vd,Wd,Ud)),("WUV",(Wd,Ud,Vd))]:
            if np.array_equal(Uk,Ut) and np.array_equal(Vk,Vt) and np.array_equal(Wk,Wt):
                cyc_match = label; break
        # Wedge match (sufficient for exterior equation)
        wk_comp = wedge3(Uk, Vk, Wk, triples)
        wk_data = wedge3(Ud, Vd, Wd, triples)
        wedge_match = np.array_equal(wk_comp, wk_data)
        print(f"  k={k}: direct={direct}, cyclic={cyc_match}, wedge_match={wedge_match}")
    
    # === Exterior equation check ===
    print(f"\n{'='*50}")
    print("Exterior equation verification")
    print(f"{'='*50}")
    
    # orbit_sum from stored reps
    orbit_sum_data = np.zeros(D, dtype=np.int64)
    for U,V,W in rep_UVW:
        orbit_sum_data += wedge3(U, V, W, triples)
    
    # orbit_sum from Z₄ images of rep0
    w0 = wedge3(U0, V0, W0, triples)
    s4_w0 = S4 @ w0
    
    # orbit_sum from direct computation of Ad^k(rep0) wedges
    orbit_sum_direct = np.zeros(D, dtype=np.int64)
    for k in range(4):
        Uk = Ad_pow[k] @ U0; Vk = Ad_pow[k] @ V0; Wk = Ad_pow[k] @ W0
        orbit_sum_direct += wedge3(Uk, Vk, Wk, triples)
    
    print(f"  orbit_sum (data) nonzero: {np.count_nonzero(orbit_sum_data)}")
    print(f"  S4·w₀ nonzero: {np.count_nonzero(s4_w0)}")
    print(f"  orbit_sum (Ad^k) nonzero: {np.count_nonzero(orbit_sum_direct)}")
    print(f"  S4·w₀ = orbit_sum(data): {np.array_equal(s4_w0, orbit_sum_data)}")
    print(f"  S4·w₀ = orbit_sum(Ad^k): {np.array_equal(s4_w0, orbit_sum_direct)}")
    print(f"  orbit_sum(data) = orbit_sum(Ad^k): {np.array_equal(orbit_sum_data, orbit_sum_direct)}")
    
    # Check 3·orbit_sum = ω
    check_data = np.array_equal(3*orbit_sum_data, omega)
    check_s4 = np.array_equal(3*s4_w0, omega)
    print(f"\n  3·orbit_sum(data) = ω: {check_data}")
    print(f"  3·S4·w₀ = ω: {check_s4}")
    
    # Determine the correct equation form
    if check_s4:
        print("  → Exterior equation: 3·S4·(A∧B∧C) = ω")
        print("  → Equivalently: Proj(A∧B∧C) = ω/12")
    elif check_data:
        # orbit_sum doesn't match S4·w₀, but 3·orbit_sum = ω
        # Investigate ratio
        nzp = np.nonzero(s4_w0)[0]
        if len(nzp) > 0:
            ratio = orbit_sum_data[nzp[0]] / s4_w0[nzp[0]] if s4_w0[nzp[0]] != 0 else None
            print(f"  → S4·w₀ ≠ orbit_sum but orbit_sum/S4·w₀ might be constant: ratio at first nonzero = {ratio}")
    
    # === Jacobian at BILR (exact mod p) ===
    print(f"\n{'='*50}")
    print("Jacobian and fiber analysis at BILR")
    print(f"{'='*50}")
    
    # The map: (A,B,C) → 3·S4·(A∧B∧C)  (should equal ω)
    # Jacobian: d/dA at (U₀,V₀,W₀):  δA → 3·S4·(δA∧V₀∧W₀)
    J = np.zeros((D, 27), dtype=np.int64)
    for i in range(9):
        e = np.zeros(9,dtype=np.int64); e[i]=1
        J[:,i]    = 3 * (S4 @ wedge3(e, V0, W0, triples))
        J[:,9+i]  = 3 * (S4 @ wedge3(U0, e, W0, triples))
        J[:,18+i] = 3 * (S4 @ wedge3(U0, V0, e, triples))
    
    jr = rank_mod(J, p)
    print(f"  Jacobian of 3·S4∘wedge at BILR:")
    print(f"    rank (mod {p}): {jr}")
    print(f"    fiber dimension: {27 - jr}")
    
    # Also check at second prime
    p2 = 32003
    jr2 = rank_mod(J, p2)
    print(f"    rank (mod {p2}): {jr2}")
    
    # Kernel
    ker, _ = kernel_mod(J, p)
    tdim = ker.shape[1]
    print(f"    tangent space dimension: {tdim}")
    
    # === Stabilizer directions ===
    # Centralizer Z(a₀) = span{I,a₀,a₀²} acts by conjugation on (A,B,C)
    # Infinitesimal: X ∈ Z(a₀) gives (δA,δB,δC) = ([X,A],[X,B],[X,C])
    print(f"\n  Stabilizer analysis:")
    stab_dirs = np.zeros((27, 3), dtype=np.int64)
    A_mat = U0.reshape(3,3); B_mat = V0.reshape(3,3); C_mat = W0.reshape(3,3)
    for k in range(3):
        X = cent[k].reshape(3,3)
        dA = (X@A_mat - A_mat@X).flatten()
        dB = (X@B_mat - B_mat@X).flatten()
        dC = (X@C_mat - C_mat@X).flatten()
        stab_dirs[:9,k] = dA; stab_dirs[9:18,k] = dB; stab_dirs[18:,k] = dC
    
    # Check each in kernel
    for k in range(3):
        Jv = np.zeros(D, dtype=np.int64)
        for row in range(D):
            Jv[row] = sum(int(J[row,c])*int(stab_dirs[c,k]) for c in range(27))
        in_ker = all(x % p == 0 for x in Jv)
        name = ['I','a₀','a₀²'][k]
        nonzero = np.count_nonzero(stab_dirs[:,k])
        print(f"    X={name}: in kernel={in_ker}, direction nonzero entries={nonzero}")
    
    stab_rank = rank_mod(stab_dirs, p)
    print(f"    stabilizer subspace rank: {stab_rank}")
    print(f"    genuine fiber dimension (mod stabilizer): {tdim - stab_rank}")
    
    # === Character block projections ===
    print(f"\n{'='*50}")
    print("Character block structure")
    print(f"{'='*50}")
    
    # Get eigenspace bases
    V1_basis, _ = kernel_mod(Ad - I9, p)
    Vm1_basis, _ = kernel_mod(Ad + I9, p)
    Vpi_basis, _ = kernel_mod(Ad2 + I9, p)
    
    print(f"  V₁ basis dim: {V1_basis.shape[1]}")
    print(f"  V₋₁ basis dim: {Vm1_basis.shape[1]}")
    print(f"  V±ᵢ basis dim: {Vpi_basis.shape[1]}")
    
    # Check Ad(a₀²) eigenspaces (for size-2 cube orbits)
    # V₁⊕V₋₁ = ker(Ad² - I)
    d_fixed_by_a02 = N - rank_mod(Ad2 - I9, p)
    print(f"\n  V₁⊕V₋₁ = ker(Ad²-I) dim: {d_fixed_by_a02}")
    print(f"  (Size-2 cube orbits have c ∈ V₁⊕V₋₁, dim 5)")
    
    # Cube character counting
    print(f"\n  Cube structure for rank-22 (f=10, m=4):")
    print(f"    Fixed cubes: c ∈ V₁ (3 dim), contributes c³")
    print(f"    Size-2 orbits: c ∈ V₁⊕V₋₁\\V₁ (5-3=2 new dirs), contributes c³+(a₀c)³")
    print(f"    Size-4 orbits: c ∈ gl₃\\V₁⊕V₋₁ (9-5=4 new dirs), contributes ∑ₖ(a₀ᵏc)³")
    
    # Count Z₄-inv Sym³ equations by computing Z₄ projector on the diagonal part
    # The diagonal/symmetric cubic has 165 independent monomials
    # Z₄-invariant: ~43 (from cyclic analysis)
    # We'll verify this another way
    
    # === Fiber parametrization probe ===
    # Try random perturbation of BILR point in the tangent space
    print(f"\n{'='*50}")
    print("Fiber exploration")
    print(f"{'='*50}")
    
    if tdim > 0:
        np.random.seed(42)
        # Pick random tangent direction (mod p)
        for trial in range(3):
            # Random kernel direction
            coeffs = np.random.randint(1, p, size=tdim)
            v = np.zeros(27, dtype=np.int64)
            for k in range(tdim):
                v = (v + int(coeffs[k]) * ker[:,k]) % p
            
            # Perturbed point (mod p): (U0 + eps*dU, V0 + eps*dV, W0 + eps*dW)
            # In a finite field, use the kernel direction directly as a linear perturbation
            # Check if the Jacobian rank is maintained
            dU = v[:9]; dV = v[9:18]; dW = v[18:]
            
            # New Jacobian at (U0+t*dU, V0+t*dV, W0+t*dW) for generic t
            # Use t = trial+1 (small nonzero integer)
            t = trial + 1
            U_new = (U0 + t * dU) % p
            V_new = (V0 + t * dV) % p
            W_new = (W0 + t * dW) % p
            
            J_new = np.zeros((D, 27), dtype=np.int64)
            for i in range(9):
                e = np.zeros(9,dtype=np.int64); e[i]=1
                J_new[:,i]    = 3 * (S4 @ wedge3(e, V_new, W_new, triples))
                J_new[:,9+i]  = 3 * (S4 @ wedge3(U_new, e, W_new, triples))
                J_new[:,18+i] = 3 * (S4 @ wedge3(U_new, V_new, e, triples))
            J_new = J_new % p
            jr_new = rank_mod(J_new, p)
            
            # Check if 3·S4·(U_new∧V_new∧W_new) = ω mod p
            w_new = wedge3(U_new, V_new, W_new, triples)
            target = (3 * (S4 @ w_new)) % p
            omega_mod = omega % p
            eq_check = np.array_equal(target, omega_mod)
            
            print(f"  Trial {trial}: t={t}, Jac rank={jr_new}, equation satisfied={eq_check}")
    
    # === Summary ===
    results = {
        'a0': a0.tolist(),
        'a0_inv': a0inv.tolist(),
        'Ad_eigenspace_dims': {'V1': int(d1), 'Vm1': int(dm1), 'Vpi': int(dpi)},
        'L3_gl3_dim': D,
        'Z4_inv_dim_L3': int(inv_dim),
        'omega_nonzero_count': nz,
        'omega_Z4_invariant': True,
        'iota_tr_omega_zero': trace_ok,
        'bilr_3_orbit_data_eq_omega': bool(check_data),
        'bilr_3_S4_w0_eq_omega': bool(check_s4),
        'jacobian_rank_mod_65521': int(jr),
        'jacobian_rank_mod_32003': int(jr2),
        'fiber_dim': int(27-jr),
        'tangent_dim': int(tdim),
        'stabilizer_rank': int(stab_rank),
        'genuine_fiber_dim': int(tdim - stab_rank),
        'expected_summary': (
            f"20 Z₄-invariant exterior equations in 27 variables, "
            f"fiber dim {27-jr}, stabilizer dim {stab_rank}, "
            f"effective dim {tdim-stab_rank}"
        )
    }
    (OUT/'z4_exterior_model_basic.json').write_text(json.dumps(results,indent=2)+'\n')
    print(f"\nSaved {OUT/'z4_exterior_model_basic.json'}")

if __name__=='__main__':
    main()
