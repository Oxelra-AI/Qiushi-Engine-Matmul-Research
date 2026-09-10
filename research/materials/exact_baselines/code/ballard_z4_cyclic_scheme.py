#!/usr/bin/env python3
"""
analysis: Exact Ballard-Ikenmeyer-Landsberg-Ryder Z4 x Z3 cyclic rank-23 scheme.

The BILR/JPAA 3x3 paper gives a cyclic rank-23 decomposition consisting of
11 cyclic fixed cubes and four free cyclic 3-orbits (12 terms), see their Sec. 2.1
and the diagonalized discussion in Sec. 2.2.  This script reconstructs the scheme
from the displayed integer matrices, verifies all 729 entries of tr(XYZ), extracts
its m=4 exterior decomposition of the Cartan 3-form, and computes the Koszul-Young
flattening rank of the residual cubic represented by the 11 cubes.

This is not a rank-22 proof by itself: it certifies the known m=4 rank-23 member and
shows that this exact residual cubic has Waring rank >10 via a flattening rank >700.
"""
from __future__ import annotations

import itertools, json, math
from pathlib import Path
import numpy as np

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'ballard_z4_cyclic'
OUT.mkdir(parents=True, exist_ok=True)

N = 9
TRIPLES8 = list(itertools.combinations(range(8), 3))
TRIPLE8_IDX = {t:i for i,t in enumerate(TRIPLES8)}
SUB4 = list(itertools.combinations(range(9), 4))
SUB5 = list(itertools.combinations(range(9), 5))
SUB5_IDX = {s:i for i,s in enumerate(SUB5)}


def mat(a):
    return np.array(a, dtype=object)


def flatten(M):
    return np.array(M, dtype=object).reshape(9)


def inv_int(M):
    M = np.array(M, dtype=object)
    # for this a0 det=1 and inverse is integral; use rounded float then verify
    Minv = np.rint(np.linalg.inv(np.array(M, dtype=float))).astype(int).astype(object)
    assert np.array_equal(M @ Minv, np.eye(3, dtype=object))
    assert np.array_equal(Minv @ M, np.eye(3, dtype=object))
    return Minv


def conj(A, X):
    return A @ X @ inv_int(A)


def unique_mats(mats):
    out=[]; seen=set()
    for M in mats:
        key=tuple(int(x) for x in flatten(M))
        if key not in seen:
            seen.add(key); out.append(M)
    return out


def build_scheme():
    # BILR Sec. 2.1 matrices.
    a0 = mat([[0,0,-1],[1,0,-1],[0,1,-1]])
    powers=[np.eye(3, dtype=object)]
    for _ in range(3):
        powers.append(powers[-1] @ a0)
    assert np.array_equal(powers[3] @ a0, np.eye(3, dtype=object))

    cube0 = -a0  # (-a0)^tensor3 = - a0^tensor3
    cubeB = mat([[0,1,0],[0,1,0],[0,0,0]])
    cubeC = mat([[1,0,0],[0,0,0],[0,0,0]])
    cubeD = mat([[0,-1,0],[1,-1,0],[0,0,0]])
    U0 = mat([[0,0,0],[0,0,1],[0,0,0]])
    V0 = mat([[0,0,0],[0,0,0],[-1,1,0]])
    W0 = mat([[0,0,0],[0,1,-1],[0,1,-1]])

    cubes=[cube0]
    cubes += unique_mats([conj(P, cubeB) for P in powers])
    cubes += unique_mats([conj(P, cubeC) for P in powers])
    cubes += unique_mats([conj(P, cubeD) for P in powers])
    assert len(cubes)==11, len(cubes)

    free_orbits=[]
    terms=[]
    for C in cubes:
        terms.append((C,C,C,'cube'))
    for P in powers:
        U,V,W = conj(P,U0), conj(P,V0), conj(P,W0)
        free_orbits.append((U,V,W))
        terms.append((U,V,W,'free'))
        terms.append((V,W,U,'free_cyc'))
        terms.append((W,U,V,'free_cyc'))
    assert len(terms)==23
    return terms, cubes, free_orbits, powers, a0


def target_tensor_int():
    T = np.zeros((9,9,9), dtype=object)
    for a,b,c in itertools.product(range(3), repeat=3):
        i=3*a+b; j=3*b+c; k=3*c+a
        T[i,j,k] += 1
    return T


def terms_tensor(terms):
    T=np.zeros((9,9,9), dtype=object)
    for U,V,W,kind in terms:
        u=flatten(U); v=flatten(V); w=flatten(W)
        T += np.einsum('i,j,k->ijk', u, v, w)
    return T


def sym_outer3_int(u,v,w):
    T=np.zeros((9,9,9), dtype=object)
    vecs=[u,v,w]
    for perm in itertools.permutations(range(3)):
        T += np.einsum('i,j,k->ijk', vecs[perm[0]], vecs[perm[1]], vecs[perm[2]])
    # entries divisible by 6 if this represents sym tensor of polynomial coefficient? For
    # cyclic sum on diagonal, polynomial contribution is 3*u*v*w.  For the symmetric
    # tensor representation, the three cyclic terms equal 3*sym_outer without needing
    # integer entries in intermediate.  We use Fraction-like object division where needed.
    return T


def polynomial_coeffs_from_symmetric_tensor(T):
    coeff={}
    for key in itertools.combinations_with_replacement(range(9),3):
        perms=set(itertools.permutations(key))
        val=sum(T[p] for p in perms)
        if val:
            coeff[key]=int(val) if isinstance(val, (int, np.integer)) or (hasattr(val,'denominator') and val.denominator==1) else val
    return coeff


def target_trM3_coeffs():
    coeff={}
    for a,b,c in itertools.product(range(3), repeat=3):
        key=tuple(sorted([3*a+b,3*b+c,3*c+a]))
        coeff[key]=coeff.get(key,0)+1
    return coeff


def cube_coeffs(cubes):
    coeff={}
    for C in cubes:
        u=[int(x) for x in flatten(C)]
        for i,j,k in itertools.product(range(9), repeat=3):
            val=u[i]*u[j]*u[k]
            if val:
                key=tuple(sorted([i,j,k]))
                coeff[key]=coeff.get(key,0)+val
    return {k:v for k,v in coeff.items() if v}


def orbit_diag_coeffs(free_orbits):
    # diagonal polynomial contribution of a free cyclic orbit is 3*l_U*l_V*l_W in char 0.
    coeff={}
    for U,V,W in free_orbits:
        u=[int(x) for x in flatten(U)]; v=[int(x) for x in flatten(V)]; w=[int(x) for x in flatten(W)]
        for i,j,k in itertools.product(range(9), repeat=3):
            val=3*u[i]*v[j]*w[k]
            if val:
                key=tuple(sorted([i,j,k]))
                coeff[key]=coeff.get(key,0)+val
    return {k:v for k,v in coeff.items() if v}


def coeffs_to_tensor(coeff):
    # symmetric tensor T such that polynomial f(x)=sum_{ijk} T_ijk x_i x_j x_k
    T=np.zeros((9,9,9), dtype=object)
    from fractions import Fraction
    for key,c in coeff.items():
        perms=set(itertools.permutations(key))
        val=Fraction(c, len(perms))
        for p in perms:
            T[p]=val
    return T


def koszul_matrix_from_coeffs(coeff, p=4):
    # Use polynomial coefficients via symmetric tensor; scale by lcm 6 to integer matrix.
    T=coeffs_to_tensor(coeff)
    rows=len(SUB5)*9; cols=len(SUB4)*9
    M=np.zeros((rows,cols), dtype=object)
    for a in range(9):
        for sidx,S in enumerate(SUB4):
            Sset=set(S); col=a*len(SUB4)+sidx
            for i in range(9):
                if i in Sset: continue
                U=tuple(sorted((i,)+S))
                sign=-1 if (sum(1 for z in S if z < i)&1) else 1
                row0=SUB5_IDX[U]*9
                for k in range(9):
                    if T[a,i,k]:
                        M[row0+k,col] += sign*T[a,i,k]
    # scale to integers by 6
    Mint=np.zeros(M.shape, dtype=np.int64)
    for idx,x in np.ndenumerate(M):
        Mint[idx]=int(x*6)
    return Mint


def rank_mod_np(A_int64, prime):
    A=np.mod(A_int64, prime).astype(np.int64, copy=True)
    m,n=A.shape; r=0
    for c in range(n):
        piv=None
        nz=np.nonzero(A[r:,c] % prime)[0]
        if nz.size==0: continue
        piv=r+int(nz[0])
        if piv!=r:
            A[[r,piv]]=A[[piv,r]]
        inv=pow(int(A[r,c]), -1, prime)
        A[r,:]=(A[r,:]*inv)%prime
        rows=np.nonzero(A[:,c] % prime)[0]
        rows=rows[rows!=r]
        for i in rows:
            f=int(A[i,c])
            A[i,:]=(A[i,:]-f*A[r,:])%prime
        r+=1
        if r==m: break
    return r


def sl3_projection_matrix():
    # gl -> sl coordinates in analysis basis for traceless inputs only. For an arbitrary matrix,
    # use coordinates of its traceless projection X - tr(X)/3 I. Since B basis spans sl3.
    B=np.zeros((9,8), dtype=float)
    B[1,0]=1; B[2,1]=1; B[3,2]=1; B[5,3]=1; B[6,4]=1; B[7,5]=1
    B[0,6]=1; B[4,6]=-1; B[4,7]=1; B[8,7]=-1
    return np.linalg.pinv(B)


def wedge3(u,v,w):
    out=np.zeros(56, dtype=float)
    for r,(a,b,c) in enumerate(TRIPLES8):
        out[r]=u[a]*(v[b]*w[c]-v[c]*w[b])-u[b]*(v[a]*w[c]-v[c]*w[a])+u[c]*(v[a]*w[b]-v[b]*w[a])
    return out


def omega_sl3():
    out=np.zeros(56, dtype=float)
    for t,c in { (0,2,6):3, (0,3,4):3, (1,2,5):-3, (1,4,6):3, (1,4,7):3, (3,5,7):3}.items():
        out[TRIPLE8_IDX[t]]=c
    return out


def main():
    terms,cubes,free_orbits,powers,a0=build_scheme()
    T=terms_tensor(terms)
    target=target_tensor_int()
    diff=T-target
    errors=[]
    for idx,val in np.ndenumerate(diff):
        if val:
            errors.append((idx,int(val)))
    print(f'terms={len(terms)} cubes={len(cubes)} free_orbits={len(free_orbits)} brent_errors={len(errors)}')

    tr_coeff=target_trM3_coeffs()
    cubec=cube_coeffs(cubes)
    orbitc=orbit_diag_coeffs(free_orbits)
    # Check tr(M^3) = cube polynomial + orbit diagonal polynomial.
    allkeys=set(tr_coeff)|set(cubec)|set(orbitc)
    diag_mis={str(k): tr_coeff.get(k,0)-cubec.get(k,0)-orbitc.get(k,0) for k in allkeys if tr_coeff.get(k,0)-cubec.get(k,0)-orbitc.get(k,0)}
    print(f'diagonal polynomial mismatches={len(diag_mis)}')

    # Exterior decomposition by free orbits.
    P=sl3_projection_matrix()
    extsum=np.zeros(56)
    traces=[]
    for U,V,W in free_orbits:
        traces.append([int(np.trace(U)), int(np.trace(V)), int(np.trace(W))])
        u=P @ np.array(flatten(U), dtype=float)
        v=P @ np.array(flatten(V), dtype=float)
        w=P @ np.array(flatten(W), dtype=float)
        extsum += wedge3(u,v,w)
    ext_err=float(np.max(np.abs(extsum-omega_sl3())))
    print(f'exterior max error={ext_err:.2e}; traces={traces}')

    # Koszul rank of the residual cubic, which equals the 11-cube polynomial.
    K=koszul_matrix_from_coeffs(cubec, p=4)
    ranks={}
    for q in [1000003, 1000033, 65521, 32003]:
        r=rank_mod_np(K, q)
        ranks[str(q)]=int(r)
        print(f'Koszul rank mod {q}: {r}')
    rank_one_bound=70

    # Also rank of trM3 itself and orbit residual for comparison.
    Kdet=koszul_matrix_from_coeffs(tr_coeff, p=4)
    det_ranks={}
    for q in [1000003, 65521]:
        det_ranks[str(q)]=int(rank_mod_np(Kdet,q))
    print('trM3 Koszul ranks', det_ranks)

    result={
        'source':'Ballard-Ikenmeyer-Landsberg-Ryder JPAA 2018 Sec. 2.1, cyclic Z4 x Z3 rank-23 decomposition',
        'citation':'\\cite{ballard2018geometry}',
        'terms':len(terms), 'cube_count':len(cubes), 'free_cyclic_orbit_count':len(free_orbits),
        'brent_errors':len(errors), 'brent_error_examples':errors[:5],
        'diagonal_polynomial_mismatches':diag_mis,
        'free_orbit_traces':traces,
        'exterior_max_error':ext_err,
        'koszul_residual_cube_matrix_shape':list(K.shape),
        'koszul_rank_mod_primes':ranks,
        'rank_one_koszul_upper_per_cube':rank_one_bound,
        'rank_gt_700_implies_residual_waring_rank_gt_10': all(r>700 for r in ranks.values()),
        'rank_le_11_upper_from_displayed_cubes': True,
        'trM3_koszul_rank_mod_primes':det_ranks,
        'a0': [[int(x) for x in row] for row in a0.tolist()],
        'cubes': [[[int(x) for x in row] for row in C.tolist()] for C in cubes],
        'free_orbit_representatives': [
            {'U':[[int(x) for x in Urow] for Urow in U.tolist()],
             'V':[[int(x) for x in Vrow] for Vrow in V.tolist()],
             'W':[[int(x) for x in Wrow] for Wrow in W.tolist()]}
            for U,V,W in free_orbits
        ],
    }
    out=OUT/'ballard_z4_cyclic_scheme.json'
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(f'Saved {out}')

if __name__=='__main__':
    main()
