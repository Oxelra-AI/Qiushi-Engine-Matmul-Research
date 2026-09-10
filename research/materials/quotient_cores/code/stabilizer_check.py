#!/usr/bin/env python3
"""Check infinitesimal GL_3^3 stabilizer formula variants for QMM matrix-multiplication schemes.

The QMM verifier uses row-major coefficient vectors u(A), v(B), w(C).  This script
builds the Jacobian of the decomposition map and tests several plausible sandwich
infinitesimal formulas.  It records which formula actually gives a 26-dimensional
subspace of ker(J) at an exact verified 3x3 scheme.
"""
from pathlib import Path
import argparse, json
import numpy as np


def parse_qmm(path):
    dims=None; rank=None; terms=[]; cur=None
    for raw in Path(path).read_text().splitlines():
        line=raw.strip()
        if not line or line.startswith('#'):
            continue
        p=line.split()
        if p[0]=='dimensions': dims=tuple(map(int,p[1:4]))
        elif p[0]=='rank': rank=int(p[1])
        elif p[0]=='term':
            if cur is not None: terms.append(cur)
            cur={'index':int(p[1])}
        elif p[0] in ('u','v','w'):
            cur[p[0]]=np.array([float(x) for x in p[1:]], dtype=float)
    if cur is not None: terms.append(cur)
    return dims, rank, terms


def build_jacobian(terms, n=9):
    r=len(terms)
    J=np.zeros((n**3,3*n*r), dtype=float)
    for i,t in enumerate(terms):
        u,v,w=t['u'],t['v'],t['w']
        cb=27*i
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    row=a*81+b*9+c
                    J[row,cb+a]+=v[b]*w[c]
                    J[row,cb+9+b]+=u[a]*w[c]
                    J[row,cb+18+c]+=u[a]*v[b]
    return J


def mat_vec(M):
    return np.asarray(M, dtype=float).reshape(9)


def build_variant(terms, variant, n=3):
    """Return 27 columns for one stabilizer formula variant.

    Variants:
      old:        dU=pU-Uq,       dV=qV-Vr,       dW=pW-Wr
      pullback:   dU=p^T U-U q^T, dV=q^T V-V r^T, dW=-p W+W r
      pullbackT:  dU=p U-U q,     dV=q V-V r,     dW=-p^T W+W r^T
      alt1:       dU=-pU+Uq,      dV=-qV+Vr,      dW=pW-Wr
      alt1T:      dU=-p^T U+U q^T,dV=-q^T V+V r^T,dW=p W-W r
    """
    r=len(terms)
    vecs=[]
    for gen in ['p','q','r']:
        for jj in range(n):
            for kk in range(n):
                E=np.zeros((n,n)); E[jj,kk]=1.0
                sv=np.zeros(27*r)
                for i,t in enumerate(terms):
                    U=t['u'].reshape(n,n); V=t['v'].reshape(n,n); W=t['w'].reshape(n,n)
                    dU=np.zeros((n,n)); dV=np.zeros((n,n)); dW=np.zeros((n,n))
                    if variant=='old':
                        if gen=='p': dU=E@U; dW=E@W
                        elif gen=='q': dU=-(U@E); dV=E@V
                        else: dV=-(V@E); dW=-(W@E)
                    elif variant=='pullback':
                        if gen=='p': dU=E.T@U; dW=-(E@W)
                        elif gen=='q': dU=-(U@E.T); dV=E.T@V
                        else: dV=-(V@E.T); dW=W@E
                    elif variant=='pullbackT':
                        if gen=='p': dU=E@U; dW=-(E.T@W)
                        elif gen=='q': dU=-(U@E); dV=E@V
                        else: dV=-(V@E); dW=W@E.T
                    elif variant=='alt1':
                        if gen=='p': dU=-(E@U); dW=E@W
                        elif gen=='q': dU=U@E; dV=-(E@V)
                        else: dV=V@E; dW=-(W@E)
                    elif variant=='alt1T':
                        if gen=='p': dU=-(E.T@U); dW=E@W
                        elif gen=='q': dU=U@E.T; dV=-(E.T@V)
                        else: dV=V@E.T; dW=-(W@E)
                    else:
                        raise ValueError(variant)
                    sv[27*i:27*i+9]+=mat_vec(dU)
                    sv[27*i+9:27*i+18]+=mat_vec(dV)
                    sv[27*i+18:27*i+27]+=mat_vec(dW)
                vecs.append(sv)
    return np.array(vecs).T


def build_rescalings(terms):
    r=len(terms); cols=[]
    for i,t in enumerate(terms):
        u,v,w=t['u'],t['v'],t['w']
        d1=np.zeros(27*r); d1[27*i:27*i+9]=u; d1[27*i+18:27*i+27]=-w
        d2=np.zeros(27*r); d2[27*i+9:27*i+18]=v; d2[27*i+18:27*i+27]=-w
        cols.extend([d1,d2])
    return np.array(cols).T


def rank(A,tol=1e-10):
    return int(np.linalg.matrix_rank(A,tol=tol))


def nullity_rank_of_JS(J,S,tol=1e-10):
    JS=J@S
    return S.shape[1]-rank(JS,tol), rank(JS,tol), float(np.linalg.norm(JS,ord=2))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('scheme')
    ap.add_argument('--json-out')
    args=ap.parse_args()
    dims,r,terms=parse_qmm(args.scheme)
    J=build_jacobian(terms)
    jrank=rank(J)
    print(f'scheme={args.scheme} dims={dims} rank={r} Jrank={jrank} kernel={J.shape[1]-jrank}')
    results={'scheme':args.scheme,'jacobian_rank':jrank,'kernel_dim':J.shape[1]-jrank,'variants':{}}
    R=build_rescalings(terms)
    print(f'rescaling columns={R.shape[1]} rank={rank(R)} JS_rank={rank(J@R)} max_abs={np.max(np.abs(J@R)):.2e}')
    for var in ['old','pullback','pullbackT','alt1','alt1T']:
        S=build_variant(terms,var)
        JS=J@S
        sv=np.linalg.svd(JS,compute_uv=False)
        nker=S.shape[1]-rank(JS)
        combined=np.hstack([R,S])
        n_comb_in_kernel=combined.shape[1]-rank(J@combined)
        # rank of actual kernel vectors inside combined: use nullspace coeffs of J@combined.
        U,s,Vt=np.linalg.svd(J@combined,full_matrices=True)
        rr=int(np.sum(s>1e-10))
        C=Vt[rr:].T
        actual=combined@C
        actual_rank=rank(actual)
        print(f'variant={var:9s} stab_kernel_dim={nker:2d}/27 JS_rank={rank(JS):2d} ||JS||2={sv[0] if len(sv) else 0:.3e} combined_kernel_dim={actual_rank:2d}')
        # show scalar equal direction norm for pullback variants
        results['variants'][var]={
            'stab_cols_rank':rank(S),
            'JS_rank':rank(JS),
            'stab_kernel_dim':int(nker),
            'combined_actual_kernel_rank':int(actual_rank),
            'JS_max_singular':float(sv[0] if len(sv) else 0.0),
        }
    if args.json_out:
        Path(args.json_out).write_text(json.dumps(results,indent=2)+'\n')

if __name__=='__main__':
    main()
