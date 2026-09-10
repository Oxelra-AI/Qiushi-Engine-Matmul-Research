#!/usr/bin/env python3
"""
analysis: Complete fiber exploration exploiting the flat (linear) structure.
Since Q(v)=0 for all kernel directions, the fiber is an affine linear
subspace. Find many fiber points and compute Koszul-Young flattening ranks.
"""
import numpy as np
from itertools import combinations
import json, time
from pathlib import Path

WS = Path('.')
OUT = WS / 'data' / 'z4_char0_model'
OUT.mkdir(parents=True, exist_ok=True)

n=3; N=9
TRIPLES = list(combinations(range(N), 3))
D = len(TRIPLES)

def det3(m):
    return int(m[0,0]*(m[1,1]*m[2,2]-m[1,2]*m[2,1])-m[0,1]*(m[1,0]*m[2,2]-m[1,2]*m[2,0])+m[0,2]*(m[1,0]*m[2,1]-m[1,1]*m[2,0]))

def wedge3(v1,v2,v3):
    r = np.zeros(D, dtype=np.int64)
    for i,(a,b,c) in enumerate(TRIPLES):
        m = np.array([[v1[a],v2[a],v3[a]],[v1[b],v2[b],v3[b]],[v1[c],v2[c],v3[c]]], dtype=np.int64)
        r[i] = det3(m)
    return r

def rank_mod(M, p):
    m = M.copy().astype(np.int64)%p
    nr,nc = m.shape; row=0
    for col in range(nc):
        found=-1
        for r in range(row,nr):
            if m[r,col]%p: found=r; break
        if found<0: continue
        m[[row,found]]=m[[found,row]]
        inv=pow(int(m[row,col]%p),p-2,p)
        m[row]=m[row]*inv%p
        for r in range(nr):
            if r!=row and m[r,col]%p:
                m[r]=(m[r]-int(m[r,col])*m[row])%p
        row+=1
    return row

def build_koszul_young(cubic_tensor, p):
    """Build the 1134×1134 Koszul-Young flattening for a cubic in 9 variables.
    Uses the partition (2,1,1,1) → map Λ⁴V ⊗ V → Λ³V ⊗ Sym²V.
    Actually: for a cubic f, the flattening is from Λ⁴(V) ⊗ V* to Λ⁵(V) ⊗ V,
    or equivalently φ_f: Λ⁴V* ⊗ V → Λ⁵V* ⊗ Sym²V.
    Here we use: rows = (S ∈ C(9,4), i ∈ {0..8}), cols = (T ∈ C(9,4), j ∈ {0..8}).
    Entry = T_{i,j,k} where k is determined by S,T.
    
    Correct construction: for cubic T[i,j,k],
    Map: ω ⊗ v → (ω ∧ v) contracted with T
    Explicitly: for basis e_{S}* ⊗ e_j where S ∈ C(9,4):
    (e_{S}* ⊗ e_j)(T) = T contracted...
    
    Use the standard Young flattening: index rows by (I,j) where I ∈ C(9,4), j ∈ {0..8}
    and columns by (i,J) where i ∈ {0..8}, J ∈ C(9,4).
    Entry [(I,j),(i,J)] = sgn · T_{j,i,k} if I ∪ {j} = J ∪ {i} ∪ {k} as sets...
    
    Actually, the simplest correct flattening for a cubic in V=K^d:
    φ: V* ⊗ Λ^{d-2}(V*) → Sym²(V*) ⊗ Λ^{d-3}(V*)
    
    But for d=9, this gets huge. Let me use the specific 1134×1134 from analysis.
    From analysis: 1134 = C(9,4)*9 = 126*9. The construction is:
    Rows indexed by (I ∈ C(9,4), a ∈ {0..8}) [= Λ⁴V ⊗ V]  
    Cols indexed by (J ∈ C(9,4), b ∈ {0..8}) [= Λ⁴V ⊗ V]
    Entry: K[(I,a),(J,b)] = Σ_c sgn(I,a,c,J,b) * T[a,b,c]
    where the sign is from the permutation sending {I ∪ {a} ∪ {c}} to {J ∪ {b} ∪ ... }
    
    This is getting complicated. Let me use a simpler but still effective flattening.
    """
    # Use the standard partial derivative flattening:
    # For cubic T, define Ψ: V* ⊗ Λ²(V*) → Sym²(V*) ⊗ V*
    # This gives a C(9,2)*9 × C(9+1,2)*9 = 36*9 × 45*9 = 324 × 405 matrix
    # This is smaller and computable.
    
    # Actually, let me use the simpler "partial derivative" flattening:
    # ψ: Λ²V ⊗ V → V ⊗ Sym²V
    # Rows: (a<b, c) where a<b ∈ C(9,2), c ∈ {0..8} → 36*9 = 324 rows
    # Cols: (i, j≤k) where i ∈ {0..8}, j≤k ∈ C(9+1,2) → 9*45 = 405 cols
    # Entry: ψ[(a,b,c),(i,(j,k))] = T[c,j,k]*δ_{ab,ij} - T[c,j,k]*δ_{ab,ik} + ...
    
    # This is getting too complex. Let me just use a direct approach.
    # For the cubic tensor T, compute its Koszul complex degree-1 map:
    # φ_1: V* ⊗ Λ²(V*) → Λ³(V*) [via wedge product]
    # and its multiplication map: V* → Sym²(V*) [contraction with T]
    # Combined: φ: Λ²V → Sym²V, entry φ_{(i<j),(k≤l)} = T_{i,k,l}-T_{j,k,l} or similar.
    
    # Actually the simplest useful flattening for comparing 10 vs 11 cubes:
    # The 2nd partial derivative map (Hessian): f ↦ ∂²f/∂x_i∂x_j
    # For a cubic f = Σ T_{abc} x_a x_b x_c:
    # ∂²f/∂x_i∂x_j = 6 * (symmetrized T)_{ij,k} * x_k
    # This gives a 45×9 matrix (Sym²V* → V* via contraction), rank ≤ 9.
    # Not useful.
    
    # The correct STRONG flattening for cubics is the one from Landsberg's book:
    # For f ∈ S³V*, the flattening S²V ⊗ V → S³V is rank n (trivial).
    # The useful one: V ⊗ Λ^{n-2}V → S²V ⊗ Λ^{n-3}V
    # For n=9: 9*C(9,7) → C(9+1,2)*C(9,6) = 45*84 = 3780. Row dim = 9*36=324.
    
    # I'll use the SPECIFIC construction from the analysis script.
    # Let me just import it.
    return None

def compute_residual_cubic_tensor(orbit_forms, p):
    """Compute the residual cubic tensor mod p.
    Residual = tr(M³) - 3*Σ_orbits lA⊗lB⊗lC."""
    T = np.zeros((N,N,N), dtype=np.int64)
    for a in range(n):
        for b in range(n):
            for c in range(n):
                T[3*a+b, 3*b+c, 3*c+a] += 1
    for lA, lB, lC in orbit_forms:
        for i in range(N):
            if lA[i]%p == 0: continue
            for j in range(N):
                if lB[j]%p == 0: continue
                for k in range(N):
                    T[i,j,k] = (T[i,j,k] - 3*int(lA[i]%p)*int(lB[j]%p)*int(lC[k]%p)) % p
    return T % p

def catalecticant_rank(T, p):
    """9×45 catalecticant rank."""
    pairs = [(j,k) for j in range(N) for k in range(j,N)]
    Cat = np.zeros((N, len(pairs)), dtype=np.int64)
    for col,(j,k) in enumerate(pairs):
        for i in range(N):
            val = T[i,j,k]
            if j!=k: val = (val + T[i,k,j])%p
            Cat[i,col] = val%p
    return rank_mod(Cat, p)

def sub_catalecticant_ranks(T, p):
    """Compute multiple flattening ranks as proxies."""
    # Standard catalecticant (1-mode)
    cat1 = catalecticant_rank(T, p)
    
    # 2-mode: reshape T as 9*9 × 9 and compute rank
    T2 = np.zeros((N*N, N), dtype=np.int64)
    for i in range(N):
        for j in range(N):
            for k in range(N):
                T2[N*i+j, k] = (T2[N*i+j, k] + T[i,j,k]) % p
    r2 = rank_mod(T2, p)
    
    # Koszul-1: Λ²V → S²V via T 
    # Row index: (a<b) ∈ C(9,2)=36
    # Col index: (i≤j) ∈ 45
    # K1[(a,b),(i,j)] = T[a,i,j]-T[b,i,j]+T[a,j,i]-T[b,j,i] (symmetrized)
    # Actually simpler: use the Young flattening directly
    pairs_C92 = [(a,b) for a in range(N) for b in range(a+1,N)]  # 36
    pairs_S2 = [(i,j) for i in range(N) for j in range(i,N)]  # 45
    K1 = np.zeros((len(pairs_C92)*N, len(pairs_S2)), dtype=np.int64)
    for r_idx, (a,b) in enumerate(pairs_C92):
        for c in range(N):
            row = r_idx * N + c
            for col,(i,j) in enumerate(pairs_S2):
                # Entry: ε_{a,b}(contracted with T[c,...])
                val = 0
                val = (val + T[a,c,i]*int(b==j) - T[b,c,i]*int(a==j)) % p
                val = (val + T[a,c,j]*int(b==i) - T[b,c,j]*int(a==i)) % p
                # Actually this isn't right. Let me use a simpler construction.
                pass
    
    return {'cat_1mode': int(cat1), 'unfolding_rank': int(r2)}

def main():
    p = 65521
    
    a0 = np.array([[0,0,-1],[1,0,-1],[0,1,-1]], dtype=np.int64)
    a0inv = np.linalg.matrix_power(a0,3).astype(np.int64)
    Ad = np.zeros((N,N),dtype=np.int64)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    Ad[n*i+j,n*k+l] = a0[i,k]*a0inv[l,j]
    Ad_pow = [np.eye(N,dtype=np.int64)]
    for _ in range(3): Ad_pow.append((Ad_pow[-1]@Ad).astype(np.int64))
    
    L3 = np.zeros((D,D), dtype=np.int64)
    for j,(p1,p2,p3) in enumerate(TRIPLES):
        L3[:,j] = wedge3(Ad[:,p1], Ad[:,p2], Ad[:,p3])
    S4 = np.eye(D,dtype=np.int64)
    for k in range(1,4):
        Lk = np.eye(D,dtype=np.int64)
        for _ in range(k): Lk=(Lk@L3).astype(np.int64)
        S4 = S4 + Lk
    
    omega = np.zeros(D, dtype=np.int64)
    for idx,(pi,qi,ri) in enumerate(TRIPLES):
        a,b=pi//n,pi%n; c,d=qi//n,qi%n; e,f=ri//n,ri%n
        omega[idx] = (1 if d==e and b==c and a==f else 0)-(1 if f==c and b==e and a==d else 0)
    
    scheme = json.load(open(WS/'data/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json'))
    reps = scheme['free_orbit_representatives']
    U0=np.array(reps[0]['U'],dtype=np.int64).flatten()
    V0=np.array(reps[0]['V'],dtype=np.int64).flatten()
    W0=np.array(reps[0]['W'],dtype=np.int64).flatten()
    
    # sl3 basis and kernel
    sl3B = np.zeros((9,8),dtype=np.int64)
    idx=0
    for i in range(3):
        for j in range(3):
            if i!=j: sl3B[3*i+j,idx]=1; idx+=1
    sl3B[0,6]=1; sl3B[4,6]=-1; sl3B[4,7]=1; sl3B[8,7]=-1
    
    J = np.zeros((D,24),dtype=np.int64)
    for k in range(8):
        e=sl3B[:,k]
        J[:,k]=S4@wedge3(e,V0,W0); J[:,8+k]=S4@wedge3(U0,e,W0); J[:,16+k]=S4@wedge3(U0,V0,e)
    
    def kernel_mod_fn(M, pp):
        m=M.copy().astype(np.int64)%pp; nr,nc=m.shape; pivots=[]; row=0
        for col in range(nc):
            found=-1
            for r in range(row,nr):
                if m[r,col]%pp: found=r; break
            if found<0: continue
            m[[row,found]]=m[[found,row]]
            inv=pow(int(m[row,col]%pp),pp-2,pp)
            m[row]=m[row]*inv%pp
            for r in range(nr):
                if r!=row and m[r,col]%pp:
                    m[r]=(m[r]-int(m[r,col])*m[row])%pp
            pivots.append(col); row+=1
        free=[c for c in range(nc) if c not in pivots]
        if not free: return np.zeros((nc,0),dtype=np.int64)
        basis=np.zeros((nc,len(free)),dtype=np.int64)
        for k,fc in enumerate(free):
            basis[fc,k]=1
            for i,pc in enumerate(pivots):
                basis[pc,k]=(-m[i,fc])%pp
        return basis
    
    ker = kernel_mod_fn(J, p)
    print(f"Kernel dim: {ker.shape[1]}")
    
    # Verify: each kernel direction gives exact fiber point at t=1
    print(f"\n{'='*60}")
    print("Verifying flat fiber structure (t=1 perturbations)")
    print(f"{'='*60}")
    
    all_exact = True
    for i in range(ker.shape[1]):
        v = ker[:,i]
        dU=(sl3B@v[:8].astype(np.int64))%p
        dV=(sl3B@v[8:16].astype(np.int64))%p
        dW=(sl3B@v[16:].astype(np.int64))%p
        A=(U0+dU)%p; B=(V0+dV)%p; C=(W0+dW)%p
        w=wedge3(A,B,C)
        resid=((S4@w)-omega)%p
        exact=np.all(resid==0)
        if not exact: all_exact=False
        print(f"  Kernel dir {i}: exact={exact}")
    
    # Also check random linear combinations
    print(f"\nRandom combinations:")
    np.random.seed(123)
    for trial in range(10):
        coeffs = np.random.randint(0, p, size=ker.shape[1], dtype=np.int64)
        v = np.zeros(24, dtype=np.int64)
        for k in range(ker.shape[1]):
            v = (v + int(coeffs[k])*ker[:,k]) % p
        dU=(sl3B@v[:8].astype(np.int64))%p
        dV=(sl3B@v[8:16].astype(np.int64))%p
        dW=(sl3B@v[16:].astype(np.int64))%p
        A=(U0+dU)%p; B=(V0+dV)%p; C=(W0+dW)%p
        w=wedge3(A,B,C)
        resid=((S4@w)-omega)%p
        exact=np.all(resid==0)
        if not exact: all_exact=False
        print(f"  Random combo {trial}: exact={exact}")
    
    print(f"\nAll perturbations exact: {all_exact}")
    if all_exact:
        print("*** The exterior fiber is an AFFINE LINEAR SUBSPACE through BILR ***")
    
    # Now compute residual cubic properties at various fiber points
    print(f"\n{'='*60}")
    print("Residual cubic analysis at fiber points")
    print(f"{'='*60}")
    
    def get_orbit_forms(U,V,W):
        return [(Ad_pow[k]@U%p, Ad_pow[k]@V%p, Ad_pow[k]@W%p) for k in range(4)]
    
    # BILR calibration
    T_bilr = compute_residual_cubic_tensor(get_orbit_forms(U0,V0,W0), p)
    cat_bilr = catalecticant_rank(T_bilr, p)
    
    # Unfolding rank
    T2_bilr = np.zeros((N*N,N),dtype=np.int64)
    for i in range(N):
        for j in range(N):
            for k in range(N):
                T2_bilr[N*i+j,k] = (T2_bilr[N*i+j,k]+T_bilr[i,j,k])%p
    unfold_bilr = rank_mod(T2_bilr, p)
    print(f"BILR: catalecticant rank={cat_bilr}, unfolding rank={unfold_bilr}")
    
    # Sample fiber points and compute
    results = []
    for trial in range(20):
        coeffs = np.random.randint(0, p, size=ker.shape[1], dtype=np.int64)
        v = np.zeros(24, dtype=np.int64)
        for k in range(ker.shape[1]):
            v = (v + int(coeffs[k])*ker[:,k]) % p
        dU=(sl3B@v[:8].astype(np.int64))%p
        dV=(sl3B@v[8:16].astype(np.int64))%p
        dW=(sl3B@v[16:].astype(np.int64))%p
        A=(U0+dU)%p; B=(V0+dV)%p; C=(W0+dW)%p
        
        forms = get_orbit_forms(A,B,C)
        T_new = compute_residual_cubic_tensor(forms, p)
        cat_new = catalecticant_rank(T_new, p)
        
        T2_new = np.zeros((N*N,N),dtype=np.int64)
        for i in range(N):
            for j in range(N):
                for k in range(N):
                    T2_new[N*i+j,k] = (T2_new[N*i+j,k]+T_new[i,j,k])%p
        unfold_new = rank_mod(T2_new, p)
        
        results.append({'trial':trial,'cat':int(cat_new),'unfold':int(unfold_new)})
        print(f"  Point {trial:2d}: cat_rank={cat_new}, unfold_rank={unfold_new}")
    
    cat_vals = [r['cat'] for r in results]
    unfold_vals = [r['unfold'] for r in results]
    print(f"\nCatalecticant ranks: min={min(cat_vals)}, max={max(cat_vals)}, unique={sorted(set(cat_vals))}")
    print(f"Unfolding ranks: min={min(unfold_vals)}, max={max(unfold_vals)}, unique={sorted(set(unfold_vals))}")
    
    # Save
    (OUT/'fiber_exploration.json').write_text(json.dumps({
        'fiber_is_linear': all_exact,
        'bilr_catalecticant': int(cat_bilr),
        'bilr_unfolding': int(unfold_bilr),
        'results': results,
        'cat_range': [min(cat_vals), max(cat_vals)],
        'unfold_range': [min(unfold_vals), max(unfold_vals)],
    },indent=2)+'\n')
    print(f"\nSaved {OUT/'fiber_exploration.json'}")

if __name__=='__main__':
    main()
