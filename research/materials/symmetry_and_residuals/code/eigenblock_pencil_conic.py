#!/usr/bin/env python3
"""
analysis: Eigen-coordinate pencil-conic extraction of BILR size-4 orbit forms.

Given the residual cubic C = Σ l_i³ (11 BILR cubes) in eigenbasis coordinates,
extract the qz² block as a 2×3 matrix, intersect the pencil with the Veronese
conic to recover the z-components of the two size-4 orbit forms, then reconstruct
the full forms and validate against the actual BILR scheme.
"""
from __future__ import annotations
import itertools, json, sys
from pathlib import Path
import numpy as np

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "eigenblock"
OUT.mkdir(parents=True, exist_ok=True)

P = 65521  # prime ≡ 1 mod 4

# ──── Modular arithmetic utilities ────
def mat_inv_mod(M, p):
    n = M.shape[0]
    aug = [[int(M[i,j])%p for j in range(n)]+[1 if i==j else 0 for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = None
        for i in range(col, n):
            if aug[i][col]%p: piv=i; break
        assert piv is not None, f"singular mod {p}"
        aug[col],aug[piv]=aug[piv],aug[col]
        inv=pow(aug[col][col]%p,-1,p); aug[col]=[(x*inv)%p for x in aug[col]]
        for i in range(n):
            if i!=col and aug[i][col]%p:
                f=aug[i][col]%p; aug[i]=[(aug[i][j]-f*aug[col][j])%p for j in range(2*n)]
    R = np.zeros((n,n),dtype=object)
    for i in range(n):
        for j in range(n): R[i,j]=aug[i][n+j]%p
    return R

def matmul_mod(A,B,p):
    C = np.zeros((A.shape[0],B.shape[1]),dtype=object)
    for i in range(A.shape[0]):
        for j in range(B.shape[1]):
            s=0
            for k in range(A.shape[1]): s+=int(A[i,k])*int(B[k,j])
            C[i,j]=s%p
    return C

def rank_mod(A,p):
    m,n=A.shape
    B=[[int(A[i,j])%p for j in range(n)] for i in range(m)]
    r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if B[i][c]%p: piv=i; break
        if piv is None: continue
        B[r],B[piv]=B[piv],B[r]
        inv=pow(B[r][c]%p,-1,p); B[r]=[(x*inv)%p for x in B[r]]
        for i in range(m):
            if i!=r and B[i][c]%p:
                f=B[i][c]%p; B[i]=[(B[i][j]-f*B[r][j])%p for j in range(n)]
        r+=1
    return r

def sqrt_mod(n, p):
    n=n%p
    if n==0: return 0
    if pow(n,(p-1)//2,p)!=1: return None
    Q,S=p-1,0
    while Q%2==0: Q//=2; S+=1
    if S==1: return pow(n,(p+1)//4,p)
    z=2
    while pow(z,(p-1)//2,p)!=p-1: z+=1
    M2=S; c=pow(z,Q,p); t=pow(n,Q,p); R=pow(n,(Q+1)//2,p)
    while True:
        if t==1: return R
        i=1; tmp=(t*t)%p
        while tmp!=1: tmp=(tmp*tmp)%p; i+=1
        b=pow(c,pow(2,M2-i-1,p-1),p); M2=i; c=(b*b)%p; t=(t*c)%p; R=(R*b)%p

# ──── Build eigenbasis ────
a0 = np.array([[0,0,-1],[1,0,-1],[0,1,-1]], dtype=object)

def ad_matrix(g,p):
    G=np.array(g,dtype=object)%p; Gi=mat_inv_mod(g,p); n=g.shape[0]
    M=np.zeros((n*n,n*n),dtype=object)
    for k in range(n*n):
        E=np.zeros((n,n),dtype=object); E[k//n,k%n]=1
        res=matmul_mod(matmul_mod(G,E,p),Gi,p)
        for l in range(n*n): M[l,k]=res[l//n,l%n]%p
    return M

def eigenspaces(M,p,ev):
    n=M.shape[0]; A=np.zeros((n,n),dtype=object)
    for i in range(n):
        for j in range(n): A[i,j]=(int(M[i,j])-(ev if i==j else 0))%p
    m,nc=A.shape; B=[[int(A[i,j])%p for j in range(nc)] for i in range(m)]
    pivots=[]; r=0
    for c in range(nc):
        piv=None
        for i in range(r,m):
            if B[i][c]%p: piv=i; break
        if piv is None: continue
        B[r],B[piv]=B[piv],B[r]; inv=pow(B[r][c]%p,-1,p); B[r]=[(x*inv)%p for x in B[r]]
        for i in range(m):
            if i!=r and B[i][c]%p:
                f=B[i][c]%p; B[i]=[(B[i][j]-f*B[r][j])%p for j in range(nc)]
        pivots.append(c); r+=1
    free=[c for c in range(nc) if c not in pivots]
    vecs=[]
    for fc in free:
        v=[0]*nc; v[fc]=1
        for idx,pc in enumerate(pivots): v[pc]=(-B[idx][fc])%p
        vecs.append(v)
    return np.array(vecs,dtype=object).T if vecs else np.zeros((nc,0),dtype=object)

# Find i = sqrt(-1) mod P
for a in range(2, P):
    c = pow(a, (P-1)//4, P)
    if (c*c) % P == P-1:
        imag_unit = c; break

Ad = ad_matrix(a0, P)
evals = {'+1':1, '-1':P-1, 'i':imag_unit, '-i':(P-imag_unit)%P}
eigsp = {name: eigenspaces(Ad, P, val) for name, val in evals.items()}
change = np.hstack([eigsp[k] for k in ['+1','-1','i','-i']])

print(f"Prime p={P}, i={imag_unit}")
print(f"Eigenspace dims: +1={eigsp['+1'].shape[1]}, -1={eigsp['-1'].shape[1]}, "
      f"i={eigsp['i'].shape[1]}, -i={eigsp['-i'].shape[1]}")

# Form transformation: l_new = change^T @ l_old
change_T = change.T % P

def form_to_new(l_old):
    l = np.array(l_old, dtype=object) % P
    r = np.zeros(9, dtype=object)
    for i in range(9):
        for j in range(9): r[i] = (r[i] + int(change_T[i,j])*int(l[j])) % P
    return r

# ──── Sym³ monomials and blocks ────
MONOS = list(itertools.combinations_with_replacement(range(9), 3))
mono_idx = {m:i for i,m in enumerate(MONOS)}

def var_type(idx):
    if idx<3: return 'p'
    elif idx<5: return 'q'
    elif idx<7: return 'z'
    else: return 'w'

def block_name(mono):
    counts = {'p':0,'q':0,'z':0,'w':0}
    for i in mono: counts[var_type(i)] += 1
    nq,nz,nw = counts['q'],counts['z'],counts['w']
    is_inv = ((nq+nz)%2==0 and (nz+nw)%4==0) or ((nq+nz)%2==1 and (nz+nw)%4==2)
    if not is_inv: return None
    np_=counts['p']
    if np_==3 and nq==0 and nz==0 and nw==0: return 'p3'
    if np_==1 and nq==2 and nz==0 and nw==0: return 'pq2'
    if np_==1 and nq==0 and nz==1 and nw==1: return 'pzw'
    if np_==0 and nq==1 and nz==2 and nw==0: return 'qz2'
    if np_==0 and nq==1 and nz==0 and nw==2: return 'qw2'
    return None

block_idx = {bn:[] for bn in ['p3','pq2','pzw','qz2','qw2']}
for i,m in enumerate(MONOS):
    bn = block_name(m)
    if bn: block_idx[bn].append(i)

def cube_coeffs(l, p):
    """Sym³ coefficients of l³ with multinomial weights."""
    coeffs = [0]*len(MONOS)
    for a in range(9):
        for b in range(a,9):
            for c in range(b,9):
                val = int(l[a])*int(l[b])*int(l[c])
                mult = 1 if a==b==c else (3 if a==b or b==c else 6)
                coeffs[mono_idx[(a,b,c)]] = (coeffs[mono_idx[(a,b,c)]] + mult*val) % p
    return coeffs

# ──── Load BILR scheme and compute residual ────
sch = json.loads((WS/"data"/"ballard_z4_cyclic"/"ballard_z4_cyclic_scheme.json").read_text())
cubes_flat = [[c[i][j] for i in range(3) for j in range(3)] for c in sch["cubes"]]

print(f"\nComputing BILR residual in eigenbasis (sum of {len(cubes_flat)} cube l³)...")
residual = [0]*len(MONOS)
for cf in cubes_flat:
    l_new = form_to_new(cf)
    cc = cube_coeffs(l_new, P)
    residual = [(residual[i]+cc[i])%P for i in range(len(MONOS))]

# Check Z₄-invariance of the residual
non_inv = sum(1 for i,m in enumerate(MONOS) if block_name(m) is None and residual[i]%P!=0)
print(f"Non-invariant nonzero entries: {non_inv}")

# Block content
for bn in ['p3','pq2','pzw','qz2','qw2']:
    nz = sum(1 for i in block_idx[bn] if residual[i]%P!=0)
    print(f"  {bn}: {len(block_idx[bn])} monomials, {nz} nonzero")

# ──── Extract qz² and qw² blocks as 2×3 matrices ────
# Indexing: p=0..2, q=3..4, z=5..6, w=7..8
# qz²: q_i z_j z_k → V_{-1} ⊗ Sym²(V_i)
qz2_map = {(3,5,5):(0,0),(3,5,6):(0,1),(3,6,6):(0,2),
            (4,5,5):(1,0),(4,5,6):(1,1),(4,6,6):(1,2)}
qz2_mat = np.zeros((2,3),dtype=object)
for mono,(r,c) in qz2_map.items():
    qz2_mat[r,c] = residual[mono_idx[mono]] % P

# qw²: q_i w_j w_k → V_{-1} ⊗ Sym²(V_{-i})
qw2_map = {(3,7,7):(0,0),(3,7,8):(0,1),(3,8,8):(0,2),
            (4,7,7):(1,0),(4,7,8):(1,1),(4,8,8):(1,2)}
qw2_mat = np.zeros((2,3),dtype=object)
for mono,(r,c) in qw2_map.items():
    qw2_mat[r,c] = residual[mono_idx[mono]] % P

print(f"\nqz² matrix: rank {rank_mod(qz2_mat,P)}")
print(f"  {[[int(qz2_mat[i,j]) for j in range(3)] for i in range(2)]}")
print(f"qw² matrix: rank {rank_mod(qw2_mat,P)}")
print(f"  {[[int(qw2_mat[i,j]) for j in range(3)] for i in range(2)]}")

# ──── Pencil-conic intersection ────
# The qz² block = 3·Σ_orbits q_j ⊗ z_j²
# where z² = [z₀², 2z₀z₁, z₁²] and the monomial coeff of q_a z_b z_c
# has mult 3 for b=c and mult 6 for b≠c.
# So the matrix entry for q_a z_b² is 3·Σ q_{a,j}·z_{b,j}²
# and for q_a z_b z_c (b≠c) is 6·Σ q_{a,j}·z_{b,j}·z_{c,j}
#
# The MATRIX in the basis (z₀², z₀z₁, z₁²) is:
# M[i,0] = 3·Σ q_{i,j}·z₀_j², M[i,1] = 6·Σ q_{i,j}·z₀_j·z₁_j, M[i,2] = 3·Σ q_{i,j}·z₁_j²
#
# For a perfect square z = (α,β): z² = (α², 2αβ, β²), so the matrix row contribution
# from one orbit is 3·q ⊗ (α², 2αβ, β²) with a FACTOR of 2 on the middle.
# The actual Sym² coefficient of z₀z₁ in z² = (αe₅+βe₆)² is 2αβ.
# But the Sym³ monomial (q_a, z₀, z₁) with all distinct indices gets mult 6.
# So the matrix entry M[i,1] = 6·q_i·αβ = 3·q_i·(2αβ).
#
# In the Veronese parametrization [s:t:u] = [α²:2αβ:β²]:
# The matrix row from one orbit is 3·q_i·[α²:2αβ:β²] = 3q_i·[s:t:u]
# Veronese condition: s·u = (t/2)² i.e. 4su = t²

r0 = [int(qz2_mat[0,j]) for j in range(3)]
r1 = [int(qz2_mat[1,j]) for j in range(3)]

# Quadratic: 4(αr0[0]+βr1[0])(αr0[2]+βr1[2]) = (αr0[1]+βr1[1])²
# A·α² + B·αβ + C·β² = 0
A = (4*r0[0]*r0[2] - r0[1]*r0[1]) % P
B = (4*(r0[0]*r1[2]+r1[0]*r0[2]) - 2*r0[1]*r1[1]) % P
C = (4*r1[0]*r1[2] - r1[1]*r1[1]) % P
disc = (B*B - 4*A*C) % P

print(f"\nPencil-conic quadratic: {A}α² + {B}αβ + {C}β² = 0")
print(f"Discriminant = {disc}")

sq = sqrt_mod(disc, P)
if sq is not None:
    print(f"√disc = {sq}")
    inv2A = pow(2*A%P, -1, P)
    ratios = [((-B+sq)*inv2A)%P, ((-B-sq)*inv2A)%P]
else:
    print(f"Discriminant is NOT a QR — need quadratic extension F_p(√{disc})")
    ratios = []

# ──── Classify BILR cubes by Z₄ orbit structure ────
print(f"\n{'='*60}")
print("BILR cube Z₄ orbit analysis")
print("="*60)

# Apply Ad(a₀) to each cube form and find which cube it maps to
a0_inv = np.array([[-1,1,0],[-1,0,1],[-1,0,0]], dtype=object) % P
a0_mod = np.array(a0, dtype=object) % P

def conjugate_form(l_flat, g, gi, p):
    """Ad(g)(l) for l a linear form on gl₃, represented as 9-vector."""
    # l(X) → l(g⁻¹Xg): the form's coefficient matrix L transforms as L → g^T L (g⁻¹)^T
    # In 9-vector notation: l_new = Ad(g)^(-T) l  
    # But we can just compute Ad(g) on the matrix and read off
    L = np.array(l_flat, dtype=object).reshape(3,3) % p
    result = matmul_mod(matmul_mod(g, L, p), gi, p)  # gLg⁻¹
    return [int(result[i,j]) for i in range(3) for j in range(3)]

# Group cubes into Z₄ orbits
used = [False]*11
orbits = []
for i in range(11):
    if used[i]: continue
    orbit = [i]
    used[i] = True
    l = cubes_flat[i]
    for step in range(1,4):
        l = conjugate_form(l, a0_mod, a0_inv, P)
        # Find matching cube
        found = -1
        for j in range(11):
            if used[j]: continue
            match = all((int(l[k]) - int(cubes_flat[j][k]))%P == 0 for k in range(9))
            if match:
                found = j; break
        if found >= 0:
            orbit.append(found)
            used[found] = True
        else:
            # Check if it maps to the same cube (periodic orbit)
            match_self = all((int(l[k]) - int(cubes_flat[i][k]))%P == 0 for k in range(9))
            if not match_self:
                # Check if it maps to an earlier member of the orbit
                pass
    orbits.append(orbit)

for oi, orb in enumerate(orbits):
    print(f"  Orbit {oi}: cubes {orb} (size {len(orb)})")
    l_new = form_to_new(cubes_flat[orb[0]])
    p_part = [int(l_new[i]) for i in range(3)]
    q_part = [int(l_new[i]) for i in range(3,5)]
    z_part = [int(l_new[i]) for i in range(5,7)]
    w_part = [int(l_new[i]) for i in range(7,9)]
    print(f"    rep eigenbasis: p={p_part}, q={q_part}, z={z_part}, w={w_part}")

# ──── Validate pencil-conic solutions ────
if ratios:
    print(f"\n{'='*60}")
    print("Pencil-conic validation against BILR orbits")
    print("="*60)
    
    for si, ratio in enumerate(ratios):
        # z² vector on the pencil
        s = (ratio*r0[0] + r1[0]) % P
        t = (ratio*r0[1] + r1[1]) % P
        u = (ratio*r0[2] + r1[2]) % P
        print(f"\n  Solution {si}: α/β={ratio}, z²=[{s},{t},{u}]")
        print(f"  Veronese check 4su-t²={(4*s*u-t*t)%P}")
        
        # Extract z = (z₀, z₁)
        z0 = sqrt_mod(s, P)
        z1 = sqrt_mod(u, P)
        if z0 is not None and z1 is not None:
            # Find sign combination matching 2z₀z₁ = t
            for sg0 in [z0, P-z0]:
                for sg1 in [z1, P-z1]:
                    if (2*sg0*sg1)%P == t:
                        z_sol = (sg0, sg1)
                        print(f"  z = ({sg0}, {sg1})")
                        
                        # Check against BILR orbit z-components
                        for oi, orb in enumerate(orbits):
                            if len(orb) == 4:  # size-4 orbit
                                l_new = form_to_new(cubes_flat[orb[0]])
                                z_rep = (int(l_new[5]), int(l_new[6]))
                                # Check proportionality: z_sol = λ * z_rep for some λ
                                if z_rep[0] != 0:
                                    lam = (sg0 * pow(z_rep[0],-1,P)) % P
                                    match = (sg1 == lam * z_rep[1] % P)
                                elif z_rep[1] != 0:
                                    lam = (sg1 * pow(z_rep[1],-1,P)) % P
                                    match = (sg0 == 0)
                                else:
                                    match = (sg0 == 0 and sg1 == 0)
                                if match:
                                    print(f"  → matches orbit {oi} (cubes {orb}), λ={lam}")
                        break
        else:
            print(f"  z₀ or z₁ not a QR mod {P} — solution in quadratic extension")

# ──── Save results ────
results = {
    "prime": P,
    "imag_unit": int(imag_unit),
    "eigenspace_dims": {k:int(v.shape[1]) for k,v in eigsp.items()},
    "block_dims": {k:len(v) for k,v in block_idx.items()},
    "residual_non_invariant_nonzero": int(non_inv),
    "qz2_rank": int(rank_mod(qz2_mat, P)),
    "qw2_rank": int(rank_mod(qw2_mat, P)),
    "pencil_conic": {
        "A": int(A), "B": int(B), "C": int(C),
        "discriminant": int(disc),
        "sqrt_disc": int(sq) if sq is not None else None,
        "solutions": [int(r) for r in ratios]
    },
    "cube_orbits": [{"indices": orb, "size": len(orb)} for orb in orbits],
}
(OUT / "eigenblock_pencil_conic.json").write_text(json.dumps(results, indent=2)+'\n')
print(f"\nSaved {OUT/'eigenblock_pencil_conic.json'}")
