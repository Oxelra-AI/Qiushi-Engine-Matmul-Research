#!/usr/bin/env python3
"""Intrinsic exact modular tangent/stabilizer analysis for a QMM decomposition.

This computes the tangent Jacobian J of the rank-r parameterization and the Lie
stabilizer of the tensor T itself inside gl(A)⊕gl(B)⊕gl(C) by solving

  (X_A⊗I⊗I + I⊗X_B⊗I + I⊗I⊗X_C) T = 0

over GF(p).  The resulting stabilizer basis is convention-free: it is derived
from the verified coordinate tensor carried by the QMM scheme, not from a guessed
matrix-sandwich formula.  Applying these 9x9 matrices to every rank-one term
gives parameter-space tangent directions that must lie in ker(J).  The script
then reports exact dimensions of ker(J), rescaling directions, intrinsic tensor
stabilizer directions, their combined span in parameter space, and the remaining
kernel dimension.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path

N=9


def parse_qmm(path: Path):
    dims=None; rank=None; terms=[]; cur=None
    for raw in path.read_text().splitlines():
        line=raw.strip()
        if not line or line.startswith('#'): continue
        parts=line.split()
        if parts[0]=='dimensions': dims=tuple(map(int,parts[1:4]))
        elif parts[0]=='rank': rank=int(parts[1])
        elif parts[0]=='term':
            if cur is not None: terms.append(cur)
            cur={'index':int(parts[1])}
        elif parts[0] in ('u','v','w'):
            cur[parts[0]]=[int(x) for x in parts[1:]]
    if cur is not None: terms.append(cur)
    if rank != len(terms): raise ValueError(f'rank {rank} but {len(terms)} terms')
    return {'dims':dims,'rank':rank,'terms':terms}


def rref_with_pivots(mat,p):
    A=[[(x%p) for x in row] for row in mat]
    m=len(A); n=len(A[0]) if m else 0
    pivots=[]; r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if A[i][c]%p: piv=i; break
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]
        inv=pow(A[r][c],-1,p)
        if inv!=1: A[r]=[(v*inv)%p for v in A[r]]
        for i in range(m):
            if i!=r and A[i][c]%p:
                f=A[i][c]
                A[i]=[(A[i][j]-f*A[r][j])%p for j in range(n)]
        pivots.append(c); r+=1
        if r==m: break
    return A,pivots


def rank_mod(mat,p):
    _,piv=rref_with_pivots(mat,p); return len(piv)


def nullspace_basis(mat,p):
    R,pivots=rref_with_pivots(mat,p)
    m=len(R); n=len(R[0]) if m else 0
    pivset=set(pivots)
    free=[j for j in range(n) if j not in pivset]
    basis=[]
    for f in free:
        x=[0]*n; x[f]=1
        # pivot row i has x[pivots[i]] + sum_free R[i][j] x[j] = 0
        for i,pc in enumerate(pivots):
            s=0
            row=R[i]
            for j in free:
                if row[j]: s=(s+row[j]*x[j])%p
            x[pc]=(-s)%p
        basis.append(x)
    return basis


def build_j_rows(terms,p):
    r=len(terms); cols=27*r
    uvw=[([x%p for x in t['u']], [x%p for x in t['v']], [x%p for x in t['w']]) for t in terms]
    rows=[]
    for a in range(N):
        for b in range(N):
            for c in range(N):
                row=[0]*cols
                for i,(u,v,w) in enumerate(uvw):
                    base=27*i
                    row[base+a]=(row[base+a]+v[b]*w[c])%p
                    row[base+9+b]=(row[base+9+b]+u[a]*w[c])%p
                    row[base+18+c]=(row[base+18+c]+u[a]*v[b])%p
                rows.append(row)
    return rows


def tensor_from_terms(terms,p):
    T=[0]*(N**3)
    for t in terms:
        u=[x%p for x in t['u']]; v=[x%p for x in t['v']]; w=[x%p for x in t['w']]
        for a in range(N):
            if not u[a]: continue
            for b in range(N):
                if not v[b]: continue
                for c in range(N):
                    if w[c]: T[a*81+b*9+c]=(T[a*81+b*9+c]+u[a]*v[b]*w[c])%p
    return T


def stabilizer_linear_system(T,p):
    # Unknowns: XA[a,a2] (0..80), XB[b,b2] (81..161), XC[c,c2] (162..242)
    rows=[]
    for a in range(N):
        for b in range(N):
            for c in range(N):
                row=[0]*(3*N*N)
                # contribution sum_{a2} XA[a,a2] T[a2,b,c]
                for a2 in range(N): row[a*N+a2]=T[a2*81+b*9+c]%p
                for b2 in range(N): row[81+b*N+b2]=T[a*81+b2*9+c]%p
                for c2 in range(N): row[162+c*N+c2]=T[a*81+b*9+c2]%p
                rows.append(row)
    return rows


def apply9(M,x,p):
    return [sum(M[i*N+j]*x[j] for j in range(N))%p for i in range(N)]


def stabilizer_parameter_dirs(stab_basis,terms,p):
    dirs=[]; r=len(terms)
    for sol in stab_basis:
        XA=sol[:81]; XB=sol[81:162]; XC=sol[162:243]
        d=[0]*(27*r)
        for i,t in enumerate(terms):
            du=apply9(XA,[x%p for x in t['u']],p)
            dv=apply9(XB,[x%p for x in t['v']],p)
            dw=apply9(XC,[x%p for x in t['w']],p)
            d[27*i:27*i+9]=du; d[27*i+9:27*i+18]=dv; d[27*i+18:27*i+27]=dw
        dirs.append(d)
    return dirs


def rescaling_vecs(terms,p):
    r=len(terms); vecs=[]
    for i,t in enumerate(terms):
        u=[x%p for x in t['u']]; v=[x%p for x in t['v']]; w=[x%p for x in t['w']]
        d=[0]*(27*r); d[27*i:27*i+9]=u; d[27*i+18:27*i+27]=[(-x)%p for x in w]; vecs.append(d)
        d=[0]*(27*r); d[27*i+9:27*i+18]=v; d[27*i+18:27*i+27]=[(-x)%p for x in w]; vecs.append(d)
    return vecs


def image_rows(J,dirs,p):
    if not dirs: return []
    cols=len(J[0]); out=[]
    for d in dirs:
        out.append([sum(row[j]*d[j] for j in range(cols))%p for row in J])
    return out


def span_report(J,dirs,p):
    sr=rank_mod(dirs,p); ir=rank_mod(image_rows(J,dirs,p),p)
    return {'span_rank':sr,'image_rank_under_J':ir,'kernel_intersection_dim':sr-ir,'all_in_kernel':ir==0}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('scheme',type=Path); ap.add_argument('--primes',nargs='+',type=int,default=[2,3,5,7,101]); ap.add_argument('--json-out',type=Path)
    args=ap.parse_args(); S=parse_qmm(args.scheme); out=[]
    for p in args.primes:
        J=build_j_rows(S['terms'],p); jr=rank_mod(J,p); cols=27*S['rank']
        T=tensor_from_terms(S['terms'],p); L=stabilizer_linear_system(T,p)
        stab_basis=nullspace_basis(L,p)
        stab_dirs=stabilizer_parameter_dirs(stab_basis,S['terms'],p)
        R=rescaling_vecs(S['terms'],p)
        repS=span_report(J,stab_dirs,p); repR=span_report(J,R,p); repC=span_report(J,R+stab_dirs,p)
        rec={'p':p,'jacobian_rank':jr,'kernel_dim':cols-jr,'tensor_lie_stabilizer_dim':len(stab_basis),'rescaling':repR,'intrinsic_stabilizer_parameter_dirs':repS,'combined':repC,'residual_dim':cols-jr-repC['kernel_intersection_dim']}
        print(rec); out.append(rec)
    payload={'scheme':str(args.scheme),'rank':S['rank'],'dims':S['dims'],'results':out}
    txt=json.dumps(payload,indent=2,sort_keys=True)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True,exist_ok=True); args.json_out.write_text(txt+'\n')
    print(txt)

if __name__=='__main__': main()
