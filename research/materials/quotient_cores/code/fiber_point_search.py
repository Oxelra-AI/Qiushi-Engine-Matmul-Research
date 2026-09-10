#!/usr/bin/env python3
"""
analysis: Find fiber points by fixing A,B and solving linearly for C.

For the equation S4·(A∧B∧C) = ω, given traceless A,B, this is linear in C.
Build M(A,B) such that wedge3(A,B,C)=M(A,B)·C, then solve S4·M(A,B)·C = ω.
At found fiber points, compute the residual cubic and its catalecticant rank.
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
    return int(m[0,0]*(m[1,1]*m[2,2]-m[1,2]*m[2,1])
              -m[0,1]*(m[1,0]*m[2,2]-m[1,2]*m[2,0])
              +m[0,2]*(m[1,0]*m[2,1]-m[1,1]*m[2,0]))

def wedge3(v1,v2,v3):
    r = np.zeros(D, dtype=np.int64)
    for i,(a,b,c) in enumerate(TRIPLES):
        m = np.array([[v1[a],v2[a],v3[a]],[v1[b],v2[b],v3[b]],[v1[c],v2[c],v3[c]]], dtype=np.int64)
        r[i] = det3(m)
    return r

def build_M_AB(A, B):
    """Build the 84×9 matrix M(A,B) such that wedge3(A,B,C) = M·C."""
    M = np.zeros((D, N), dtype=np.int64)
    for t, (pp, q, r) in enumerate(TRIPLES):
        # wedge3(A,B,C)_t = C_r*(A_p*B_q-A_q*B_p) + C_q*(A_r*B_p-A_p*B_r) + C_p*(A_q*B_r-A_r*B_q)
        M[t, r] += int(A[pp])*int(B[q]) - int(A[q])*int(B[pp])
        M[t, q] += int(A[r])*int(B[pp]) - int(A[pp])*int(B[r])
        M[t, pp] += int(A[q])*int(B[r]) - int(A[r])*int(B[q])
    return M

def rank_mod(M, p):
    m = M.copy().astype(np.int64) % p
    nr,nc = m.shape; row = 0
    for col in range(nc):
        found = -1
        for r in range(row, nr):
            if m[r,col]%p: found=r; break
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
    """Solve A·x ≡ b mod p. Returns (x, consistent) or (None, False)."""
    nr,nc = A.shape
    aug = np.zeros((nr,nc+1),dtype=np.int64)
    aug[:,:nc] = A%p; aug[:,nc] = b%p
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
                aug[r] = (aug[r]-int(aug[r,col])*aug[row])%p
        pivot_cols.append(col); row += 1
    for r in range(row, nr):
        if aug[r,nc]%p: return None, False
    x = np.zeros(nc,dtype=np.int64)
    for i,pc in enumerate(pivot_cols):
        x[pc] = aug[i,nc]%p
    return x, True

def kernel_mod(M, p):
    m = M.copy().astype(np.int64)%p
    nr,nc = m.shape; pivot_cols=[]; row=0
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
        pivot_cols.append(col); row+=1
    free=[c for c in range(nc) if c not in pivot_cols]
    if not free: return np.zeros((nc,0),dtype=np.int64)
    basis=np.zeros((nc,len(free)),dtype=np.int64)
    for k,fc in enumerate(free):
        basis[fc,k]=1
        for i,pc in enumerate(pivot_cols):
            basis[pc,k]=(-m[i,fc])%p
    return basis

def build_sl3_basis():
    basis = []
    for i in range(3):
        for j in range(3):
            if i!=j: v=np.zeros(9,dtype=np.int64); v[3*i+j]=1; basis.append(v)
    h1=np.zeros(9,dtype=np.int64); h1[0]=1; h1[4]=-1; basis.append(h1)
    h2=np.zeros(9,dtype=np.int64); h2[4]=1; h2[8]=-1; basis.append(h2)
    return np.array(basis).T

def compute_catalecticant(orbit_forms, p):
    """Compute the 9×45 catalecticant of the residual cubic mod p.
    Residual = tr(M³) - 3*Σ_orbits lA*lB*lC.
    Returns rank.
    """
    # Symmetrized cubic tensor T[i,j,k]
    T = np.zeros((N,N,N), dtype=np.int64)
    # tr(M³) = Σ M_{ab}M_{bc}M_{ca}
    for a in range(n):
        for b in range(n):
            for c in range(n):
                T[3*a+b, 3*b+c, 3*c+a] = (T[3*a+b, 3*b+c, 3*c+a] + 1)
    
    for lA, lB, lC in orbit_forms:
        for i in range(N):
            for j in range(N):
                for k in range(N):
                    T[i,j,k] = (T[i,j,k] - 3*int(lA[i])*int(lB[j])*int(lC[k]))%p
    T = T%p
    
    # Catalecticant: C_{i,(j,k)} = T[i,j,k] symmetrized over j,k
    # Index pairs (j,k) with j<=k: C(9+1,2)=45
    pairs = [(j,k) for j in range(N) for k in range(j,N)]
    Cat = np.zeros((N, len(pairs)), dtype=np.int64)
    for col, (j,k) in enumerate(pairs):
        for i in range(N):
            val = T[i,j,k]
            if j != k: val = (val + T[i,k,j])%p
            Cat[i,col] = val%p
    
    return rank_mod(Cat, p)

def main():
    p = 65521
    
    a0 = np.array([[0,0,-1],[1,0,-1],[0,1,-1]], dtype=np.int64)
    I3 = np.eye(3,dtype=np.int64)
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
        for _ in range(k): Lk = (Lk@L3).astype(np.int64)
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
    
    sl3B = build_sl3_basis()
    
    # Get kernel directions
    J = np.zeros((D,24),dtype=np.int64)
    for k in range(8):
        e=sl3B[:,k]
        J[:,k]=S4@wedge3(e,V0,W0); J[:,8+k]=S4@wedge3(U0,e,W0); J[:,16+k]=S4@wedge3(U0,V0,e)
    ker = kernel_mod(J, p)
    print(f"Kernel dim: {ker.shape[1]}")
    
    # BILR orbit forms for catalecticant calibration
    def get_orbit_forms(U, V, W):
        forms = []
        for k in range(4):
            lA = Ad_pow[k]@U; lB = Ad_pow[k]@V; lC = Ad_pow[k]@W
            forms.append((lA%p, lB%p, lC%p))
        return forms
    
    bilr_forms = get_orbit_forms(U0, V0, W0)
    cat_bilr = compute_catalecticant(bilr_forms, p)
    print(f"BILR catalecticant rank: {cat_bilr}")
    
    # Now find fiber points
    print(f"\n{'='*60}")
    print("Finding fiber points: fix A,B from kernel perturbation, solve for C")
    print(f"{'='*60}")
    
    np.random.seed(42)
    results = []
    
    for trial in range(15):
        # Random kernel direction
        c = np.random.randint(0, p, size=ker.shape[1], dtype=np.int64)
        v = np.zeros(24, dtype=np.int64)
        for k in range(ker.shape[1]):
            v = (v + int(c[k])*ker[:,k]) % p
        
        dU = (sl3B @ v[:8].astype(np.int64))%p
        dV = (sl3B @ v[8:16].astype(np.int64))%p
        
        A = (U0 + dU) % p
        B = (V0 + dV) % p
        
        # Build M(A,B) and L = S4·M
        M = build_M_AB(A, B)
        L = (S4 @ M) % p  # 84×9
        
        # Add tracelessness constraint: C[0]+C[4]+C[8] = 0
        trace_row = np.zeros((1,N), dtype=np.int64)
        trace_row[0,0] = 1; trace_row[0,4] = 1; trace_row[0,8] = 1
        L_aug = np.vstack([L, trace_row])
        b_aug = np.concatenate([omega, [0]])
        
        C_sol, consistent = solve_mod(L_aug, b_aug, p)
        
        if consistent:
            # Verify: S4·(A∧B∧C) = omega?
            w = wedge3(A, B, C_sol%p)
            check = ((S4 @ w) - omega) % p
            ok = np.all(check == 0)
            
            # Check tracelessness
            tr_C = (C_sol[0]+C_sol[4]+C_sol[8]) % p
            
            # Check if different from BILR
            diff = max(np.max(np.abs((A-U0%p)%p)), np.max(np.abs((B-V0%p)%p)), 
                      np.max(np.abs((C_sol%p-W0%p)%p)))
            is_new = diff > 0
            
            if ok:
                # Compute catalecticant rank of residual
                forms = get_orbit_forms(A%p, B%p, C_sol%p)
                cat_r = compute_catalecticant(forms, p)
                
                print(f"  Trial {trial:2d}: SOLVED, verified={ok}, tr(C)={tr_C}, "
                      f"new={is_new}, cat_rank={cat_r}")
                
                results.append({
                    'trial': trial, 'cat_rank': int(cat_r),
                    'is_new': bool(is_new)
                })
            else:
                print(f"  Trial {trial:2d}: SOLVED but verify FAILED")
        else:
            # System inconsistent - A,B not on fiber projection
            print(f"  Trial {trial:2d}: INCONSISTENT (L rank={rank_mod(L,p)}, system rank={rank_mod(L_aug,p)})")
    
    # Summary
    new_results = [r for r in results if r['is_new']]
    print(f"\nTotal solved: {len(results)}, new points: {len(new_results)}")
    if new_results:
        cat_ranks = [r['cat_rank'] for r in new_results]
        print(f"Catalecticant ranks at new points: {cat_ranks}")
        print(f"  Min: {min(cat_ranks)}, Max: {max(cat_ranks)}")
    
    # Save
    (OUT/'fiber_point_search.json').write_text(json.dumps({
        'bilr_cat_rank': int(cat_bilr),
        'prime': p,
        'total_trials': 15,
        'solved': len(results),
        'new_points': len(new_results),
        'results': results
    }, indent=2)+'\n')
    print(f"\nSaved {OUT/'fiber_point_search.json'}")

if __name__=='__main__':
    main()
