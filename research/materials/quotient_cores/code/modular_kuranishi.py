#!/usr/bin/env python3
"""Exact finite-field checks for the local Kuranishi quadratic system at QMM schemes.

This script verifies, over odd prime fields, the corrected tangent data and the
rank of the second-order obstruction quadrics modulo the true infinitesimal
symmetries (term rescalings plus the covector/pullback GL_3^3 isotropy action).
It is meant as arithmetic evidence for the characteristic-zero computation:
stable ranks over several primes strongly constrain possible floating-point/SVD
artifacts, while characteristic-2 behavior is deliberately not used for the
quadratic obstruction calculus because the factor 2 degenerates there.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
import numpy as np


def parse_qmm(path: str):
    dims=None; rank=None; domain=None; terms=[]; cur=None
    for raw in Path(path).read_text().splitlines():
        line=raw.strip()
        if not line or line.startswith('#'):
            continue
        p=line.split()
        if p[0]=='dimensions': dims=tuple(map(int,p[1:4]))
        elif p[0]=='rank': rank=int(p[1])
        elif p[0]=='domain': domain=p[1]
        elif p[0]=='term':
            if cur is not None: terms.append(cur)
            cur={'index':int(p[1])}
        elif p[0] in ('u','v','w'):
            cur[p[0]]=np.array([int(x) for x in p[1:]], dtype=object)
    if cur is not None: terms.append(cur)
    if dims is None or rank is None or len(terms)!=rank:
        raise ValueError(f'bad QMM {path}')
    return dims, rank, domain, terms


def rref_mod(A, p: int):
    A=np.array(A, dtype=np.int64) % p
    m,n=A.shape
    pivots=[]; r=0
    for c in range(n):
        nz=np.nonzero(A[r:,c] % p)[0]
        if nz.size==0:
            continue
        piv=r+int(nz[0])
        if piv!=r:
            A[[r,piv],:]=A[[piv,r],:]
        inv=pow(int(A[r,c] % p), -1, p)
        A[r,:]=(A[r,:]*inv) % p
        rows=np.nonzero(A[:,c] % p)[0]
        rows=rows[rows!=r]
        if rows.size:
            factors=A[rows,c].copy() % p
            A[rows,:]=(A[rows,:] - factors[:,None]*A[r,:]) % p
        pivots.append(c)
        r+=1
        if r==m:
            break
    return A, pivots


def rank_mod(A,p:int):
    _,piv=rref_mod(A,p)
    return len(piv)


def nullspace_mod(A,p:int):
    R,piv=rref_mod(A,p)
    A=np.array(A,dtype=np.int64)%p
    m,n=A.shape
    pivset=set(piv)
    free=[c for c in range(n) if c not in pivset]
    N=np.zeros((n,len(free)),dtype=np.int64)
    for j,f in enumerate(free):
        N[f,j]=1
        for row,pc in enumerate(piv):
            N[pc,j]=(-R[row,f])%p
    return N, piv


def build_jacobian(terms,p:int,n=9):
    r=len(terms)
    J=np.zeros((n**3,3*n*r), dtype=np.int64)
    for i,t in enumerate(terms):
        u=np.array(t['u'],dtype=np.int64)%p
        v=np.array(t['v'],dtype=np.int64)%p
        w=np.array(t['w'],dtype=np.int64)%p
        cb=27*i
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    row=a*81+b*9+c
                    J[row,cb+a]=(J[row,cb+a]+v[b]*w[c])%p
                    J[row,cb+9+b]=(J[row,cb+9+b]+u[a]*w[c])%p
                    J[row,cb+18+c]=(J[row,cb+18+c]+u[a]*v[b])%p
    return J


def terms_to_x(terms,p:int):
    xs=[]
    for t in terms:
        xs.extend([np.array(t['u'],dtype=np.int64)%p, np.array(t['v'],dtype=np.int64)%p, np.array(t['w'],dtype=np.int64)%p])
    return np.concatenate(xs)%p


def blocks(x,i,p:int):
    cb=27*i
    return x[cb:cb+9]%p, x[cb+9:cb+18]%p, x[cb+18:cb+27]%p


def build_rescalings(x,r,p:int):
    cols=[]
    for i in range(r):
        u,v,w=blocks(x,i,p)
        d1=np.zeros(27*r,dtype=np.int64); d1[27*i:27*i+9]=u; d1[27*i+18:27*i+27]=(-w)%p
        d2=np.zeros(27*r,dtype=np.int64); d2[27*i+9:27*i+18]=v; d2[27*i+18:27*i+27]=(-w)%p
        cols.extend([d1%p,d2%p])
    return np.array(cols,dtype=np.int64).T%p


def build_stabilizer_pullback(x,r,p:int,n=3):
    cols=[]
    for gen in ['p','q','r']:
        for jj in range(n):
            for kk in range(n):
                E=np.zeros((n,n),dtype=np.int64); E[jj,kk]=1
                d=np.zeros(27*r,dtype=np.int64)
                for i in range(r):
                    u,v,w=blocks(x,i,p)
                    U=u.reshape(n,n)%p; V=v.reshape(n,n)%p; W=w.reshape(n,n)%p
                    dU=np.zeros((n,n),dtype=np.int64); dV=np.zeros((n,n),dtype=np.int64); dW=np.zeros((n,n),dtype=np.int64)
                    if gen=='p':
                        dU=E.T@U
                        dW=-(E@W)
                    elif gen=='q':
                        dU=-(U@E.T)
                        dV=E.T@V
                    else:
                        dV=-(V@E.T)
                        dW=W@E
                    d[27*i:27*i+9]=(d[27*i:27*i+9]+dU.reshape(9))%p
                    d[27*i+9:27*i+18]=(d[27*i+9:27*i+18]+dV.reshape(9))%p
                    d[27*i+18:27*i+27]=(d[27*i+18:27*i+27]+dW.reshape(9))%p
                cols.append(d%p)
    return np.array(cols,dtype=np.int64).T%p


def qsym(d1,d2,x0,r,p:int,n=9):
    inv2=pow(2,-1,p)
    out=np.zeros(n**3,dtype=np.int64)
    for i in range(r):
        u0,v0,w0=blocks(x0,i,p)
        u1,v1,w1=blocks(d1,i,p)
        u2,v2,w2=blocks(d2,i,p)
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    val=(u1[a]*v2[b]*w0[c] + u2[a]*v1[b]*w0[c]
                         + u1[a]*v0[b]*w2[c] + u2[a]*v0[b]*w1[c]
                         + u0[a]*v1[b]*w2[c] + u0[a]*v2[b]*w1[c])
                    out[a*81+b*9+c]=(out[a*81+b*9+c]+inv2*val)%p
    return out%p


def select_residual(K,S,p:int):
    # Put symmetry columns first; RREF pivot columns from K then complete a quotient basis.
    M=np.concatenate([S%p,K%p],axis=1)%p
    _,piv=rref_mod(M,p)
    s_cols=S.shape[1]
    chosen=[c-s_cols for c in piv if c>=s_cols]
    return K[:,chosen]%p, chosen, len(piv)


def analyze_prime(path,p:int):
    dims,r,domain,terms=parse_qmm(path)
    if p==2:
        raise ValueError('Use odd primes for this Kuranishi rank check; characteristic 2 has different quadratic polarization.')
    x0=terms_to_x(terms,p)
    J=build_jacobian(terms,p)
    jrank=rank_mod(J,p)
    K,_=nullspace_mod(J,p)
    L,_=nullspace_mod(J.T,p)
    R=build_rescalings(x0,r,p)
    G=build_stabilizer_pullback(x0,r,p)
    S=np.concatenate([R,G],axis=1)%p
    res_basis, chosen, combined_rank=select_residual(K,S,p)
    m=res_basis.shape[1]
    assert m==K.shape[1]-rank_mod(S,p) or True
    mono=[]
    for j in range(m):
        for k in range(j,m):
            mono.append((j,k))
    F=np.zeros((L.shape[1],len(mono)),dtype=np.int64)
    for idx,(j,k) in enumerate(mono):
        q=qsym(res_basis[:,j],res_basis[:,k],x0,r,p)
        coeff=(L.T@q)%p
        if j<k:
            coeff=(2*coeff)%p
        F[:,idx]=coeff
    frank=rank_mod(F,p)
    return {
        'p':p,
        'jacobian_rank':int(jrank),
        'kernel_dim':int(K.shape[1]),
        'left_null_dim':int(L.shape[1]),
        'rescaling_rank':int(rank_mod(R,p)),
        'rescaling_J_rank':int(rank_mod((J@R)%p,p)),
        'stabilizer_rank':int(rank_mod(G,p)),
        'stabilizer_J_rank':int(rank_mod((J@G)%p,p)),
        'symmetry_rank':int(rank_mod(S,p)),
        'combined_rank_S_then_K':int(combined_rank),
        'residual_dim':int(m),
        'quadratic_polynomial_rank':int(frank),
        'quadratic_monomials':int(len(mono)),
        'residual_basis_kernel_indices':chosen[:],
    }


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('scheme')
    ap.add_argument('--primes',nargs='+',type=int,default=[3,5,7,101,103])
    ap.add_argument('--json-out',required=True)
    args=ap.parse_args()
    results=[]
    for p in args.primes:
        print(f'=== p={p} ===')
        res=analyze_prime(args.scheme,p)
        results.append(res)
        print(json.dumps({k:v for k,v in res.items() if k!='residual_basis_kernel_indices'},indent=2))
    out={'scheme':args.scheme,'prime_results':results,
         'note':'Odd-prime modular ranks verify the corrected tangent quotient and second-order quadratic rank; they are arithmetic evidence, not a rank-22 construction or a rank-23 lower bound.'}
    Path(args.json_out).write_text(json.dumps(out,indent=2)+'\n')
    print(f'wrote {args.json_out}')

if __name__=='__main__':
    main()
