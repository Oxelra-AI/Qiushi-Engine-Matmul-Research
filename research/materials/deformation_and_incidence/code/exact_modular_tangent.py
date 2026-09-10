#!/usr/bin/env python3
"""Exact modular tangent-space checks for 3x3 rank-r QMM schemes.

For a decomposition T=sum_i u_i⊗v_i⊗w_i, build the Jacobian J over GF(p),
compute rank/nullity, and compute the dimensions of natural tangent directions:
per-term rescalings and GL_3^3 sandwich transformations.  Unlike the first
float64 peer probe, this script does not assume proposed symmetry directions
lie in ker(J): for a direction span D it reports rank(D), rank(JD), and hence
rank(D∩ker J)=rank(D)-rank(JD).

The C/output factor has two common conventions.  `--c-action output` uses the
bilinear-map output convention W -> P W R^{-1}; `--c-action trace` uses the
trilinear trace-dual convention W -> R W P^{-1}.  The convention that is a true
stabilizer should have GL image rank 0 under J (up to characteristic effects).
"""
from __future__ import annotations
import argparse, json
from pathlib import Path

N = 9


def parse_qmm(path: Path):
    dims = None; rank = None; terms=[]; cur=None
    for raw in path.read_text().splitlines():
        line=raw.strip()
        if not line or line.startswith('#'):
            continue
        parts=line.split()
        if parts[0]=='dimensions':
            dims=tuple(map(int, parts[1:4]))
        elif parts[0]=='rank':
            rank=int(parts[1])
        elif parts[0]=='term':
            if cur is not None:
                terms.append(cur)
            cur={'index': int(parts[1])}
        elif parts[0] in ('u','v','w'):
            cur[parts[0]]=[int(x) for x in parts[1:]]
    if cur is not None:
        terms.append(cur)
    if rank != len(terms):
        raise ValueError(f'rank {rank} but {len(terms)} terms')
    return {'dims': dims, 'rank': rank, 'terms': terms}


def rank_mod(mat, p: int) -> int:
    A=[[(x % p) for x in row] for row in mat if any((y % p) for y in row)]
    m=len(A); n=len(A[0]) if m else 0
    r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if A[i][c] % p:
                piv=i; break
        if piv is None:
            continue
        A[r],A[piv]=A[piv],A[r]
        inv=pow(A[r][c], -1, p)
        if inv != 1:
            A[r]=[(v*inv)%p for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] % p:
                f=A[i][c]
                A[i]=[(A[i][j]-f*A[r][j])%p for j in range(n)]
        r+=1
        if r==m:
            break
    return r


def build_j_rows(terms, p:int):
    r=len(terms); cols=27*r
    rows=[]
    uvw=[([x%p for x in t['u']], [x%p for x in t['v']], [x%p for x in t['w']]) for t in terms]
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


def matmul3_left(E, M):
    out=[0]*9
    for i in range(3):
        for j in range(3):
            s=0
            for k in range(3):
                s += E[3*i+k]*M[3*k+j]
            out[3*i+j]=s
    return out


def matmul3_right(M, E):
    out=[0]*9
    for i in range(3):
        for j in range(3):
            s=0
            for k in range(3):
                s += M[3*i+k]*E[3*k+j]
            out[3*i+j]=s
    return out


def rescaling_vecs(terms, p:int):
    r=len(terms); vecs=[]
    for i,t in enumerate(terms):
        u=[x%p for x in t['u']]; v=[x%p for x in t['v']]; w=[x%p for x in t['w']]
        d=[0]*(27*r); d[27*i:27*i+9]=u; d[27*i+18:27*i+27]=[(-x)%p for x in w]; vecs.append(d)
        d=[0]*(27*r); d[27*i+9:27*i+18]=v; d[27*i+18:27*i+27]=[(-x)%p for x in w]; vecs.append(d)
    return vecs


def stabilizer_vecs(terms, p:int, c_action:str):
    r=len(terms)
    pvecs=[[0]*(27*r) for _ in range(9)]
    qvecs=[[0]*(27*r) for _ in range(9)]
    rvecs=[[0]*(27*r) for _ in range(9)]
    for it,t in enumerate(terms):
        U=[x%p for x in t['u']]; V=[x%p for x in t['v']]; W=[x%p for x in t['w']]
        for j in range(3):
            for k in range(3):
                idx=3*j+k
                E=[0]*9; E[idx]=1
                # A factor: U -> P U Q^{-1}; B factor: V -> Q V R^{-1}.
                for a,x in enumerate(matmul3_left(E,U)):
                    pvecs[idx][27*it+a]=(pvecs[idx][27*it+a]+x)%p
                for a,x in enumerate(matmul3_right(U,E)):
                    qvecs[idx][27*it+a]=(qvecs[idx][27*it+a]-x)%p
                for a,x in enumerate(matmul3_left(E,V)):
                    qvecs[idx][27*it+9+a]=(qvecs[idx][27*it+9+a]+x)%p
                for a,x in enumerate(matmul3_right(V,E)):
                    rvecs[idx][27*it+9+a]=(rvecs[idx][27*it+9+a]-x)%p
                if c_action == 'output':
                    # C/output matrix W -> P W R^{-1}.
                    for a,x in enumerate(matmul3_left(E,W)):
                        pvecs[idx][27*it+18+a]=(pvecs[idx][27*it+18+a]+x)%p
                    for a,x in enumerate(matmul3_right(W,E)):
                        rvecs[idx][27*it+18+a]=(rvecs[idx][27*it+18+a]-x)%p
                elif c_action == 'trace':
                    # Trace-dual matrix W -> R W P^{-1}.
                    for a,x in enumerate(matmul3_right(W,E)):
                        pvecs[idx][27*it+18+a]=(pvecs[idx][27*it+18+a]-x)%p
                    for a,x in enumerate(matmul3_left(E,W)):
                        rvecs[idx][27*it+18+a]=(rvecs[idx][27*it+18+a]+x)%p
                else:
                    raise ValueError(c_action)
    return [[x%p for x in row] for row in (pvecs+qvecs+rvecs)]


def image_rows(J, dirs, p:int):
    if not dirs:
        return []
    cols=len(J[0])
    out=[]
    for d in dirs:
        out.append([sum(row[j]*d[j] for j in range(cols))%p for row in J])
    return out


def span_report(J, dirs, p:int):
    d_rank=rank_mod(dirs,p)
    im=image_rows(J,dirs,p)
    im_rank=rank_mod(im,p)
    return {'span_rank':d_rank,'image_rank_under_J':im_rank,'kernel_intersection_dim':d_rank-im_rank,'all_in_kernel':im_rank==0}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('scheme', type=Path)
    ap.add_argument('--primes', nargs='+', type=int, default=[2,3,5,7,101,1009])
    ap.add_argument('--c-action', choices=['output','trace','both'], default='both')
    ap.add_argument('--json-out', type=Path)
    args=ap.parse_args()
    S=parse_qmm(args.scheme)
    actions=['output','trace'] if args.c_action=='both' else [args.c_action]
    all_results=[]
    for action in actions:
        for p in args.primes:
            J=build_j_rows(S['terms'], p)
            jr=rank_mod(J,p)
            cols=27*S['rank']
            R=rescaling_vecs(S['terms'],p)
            St=stabilizer_vecs(S['terms'],p,action)
            repR=span_report(J,R,p)
            repS=span_report(J,St,p)
            repC=span_report(J,R+St,p)
            rec={'p':p,'c_action':action,'jacobian_rank':jr,'kernel_dim':cols-jr,'rescaling':repR,'gl3xgl3xgl3':repS,'combined':repC,'residual_dim_after_combined_kernel_intersection':cols-jr-repC['kernel_intersection_dim']}
            print(rec)
            all_results.append(rec)
    out={'scheme':str(args.scheme),'rank':S['rank'],'dims':S['dims'],'results':all_results}
    text=json.dumps(out,indent=2,sort_keys=True)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True,exist_ok=True)
        args.json_out.write_text(text+'\n')
    print(text)

if __name__=='__main__':
    main()
