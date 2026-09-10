#!/usr/bin/env python3
"""
analysis deletion-linearization v2.

Fixes two issues identified by review:
  1. include the 8 global adjoint directions in the m=4 exterior-fiber tangent;
  2. compute exact rational ranks with sympy, not only modular evidence.

For each BILR cube deletion, the map variables are:
  * 32 internal SL_3 basis changes for the four free cyclic orbits;
  * 8 global ad(sl_3) directions on the four exterior orbit triples;
  * 90 first-order perturbations of the 10 retained cube vectors.
The right-hand side is the missing cube cubic in S^3(gl_3^*).  If augmented rank is
larger over QQ, the deletion is first-order nonrepairable in this local m=4 chart.
"""
from __future__ import annotations
import itertools, json, time
from pathlib import Path
import numpy as np
import sympy as sp

import ballard_z4_cyclic_scheme as bilr
import bilr_exterior_kernel_check as kern

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'ballard_z4_cyclic'
OUT.mkdir(parents=True, exist_ok=True)

MONOS=list(itertools.combinations_with_replacement(range(9),3))
PERMS={m:sorted(set(itertools.permutations(m))) for m in MONOS}

GEN=[]
for i in range(3):
    for j in range(3):
        if i!=j:
            G=np.zeros((3,3),dtype=object); G[i,j]=1; GEN.append(G)
G=np.diag([1,-1,0]).astype(object); GEN.append(G)
G=np.diag([0,1,-1]).astype(object); GEN.append(G)

BAS=kern.BAS


def flatten(M): return np.array(M,dtype=object).reshape(9)

def mat_from_sl(c):
    return sum(c[i]*BAS[i] for i in range(8))

def prod_coeff(u,v,w):
    out=np.zeros(len(MONOS),dtype=object)
    u=list(u); v=list(v); w=list(w)
    for idx,m in enumerate(MONOS):
        s=0
        for p in PERMS[m]:
            s += u[p[0]]*v[p[1]]*w[p[2]]
        out[idx]=s
    return out

def cube_coeff(c): return prod_coeff(c,c,c)

def ad_matrix_on_gl(H):
    # H is a 3x3 traceless matrix; action on linear forms/matrix coordinates by commutator.
    # Same convention as scheme's simultaneous conjugation X -> A X A^{-1}; derivative [H,X].
    A=np.zeros((9,9),dtype=object)
    for q in range(9):
        E=np.zeros((3,3),dtype=object); E.reshape(9)[q]=1
        C=H@E-E@H
        A[:,q]=flatten(C)
    return A

def build_jacobian(drop, include_global=True):
    terms,cubes,free,_,_=bilr.build_scheme()
    cols=[]; meta=[]
    # internal basis changes of orbit products
    for j,(U,V,W) in enumerate(free):
        M=np.array([flatten(U),flatten(V),flatten(W)],dtype=object)
        for gi,G in enumerate(GEN):
            dM=G@M
            d=3*(prod_coeff(dM[0],M[1],M[2])+prod_coeff(M[0],dM[1],M[2])+prod_coeff(M[0],M[1],dM[2]))
            cols.append(d); meta.append({'kind':'internal','orbit':j,'gen':gi})
    # global ad directions on the four orbit triples only; remaining cube global effects are in cube perturbation columns.
    if include_global:
        for hi,H in enumerate(BAS):
            dtotal=np.zeros(len(MONOS),dtype=object)
            A=ad_matrix_on_gl(H)
            for j,(U,V,W) in enumerate(free):
                u=flatten(U); v=flatten(V); w=flatten(W)
                du=A@u; dv=A@v; dw=A@w
                dtotal += 3*(prod_coeff(du,v,w)+prod_coeff(u,dv,w)+prod_coeff(u,v,dw))
            cols.append(dtotal); meta.append({'kind':'global_ad_orbit','gen':hi})
    # kept cube vector perturbations
    evecs=[]
    for q in range(9):
        e=np.zeros(9,dtype=object); e[q]=1; evecs.append(e)
    for ci,C in enumerate(cubes):
        if ci==drop: continue
        c=flatten(C)
        for q,e in enumerate(evecs):
            cols.append(3*prod_coeff(c,c,e)); meta.append({'kind':'cube','cube':ci,'coord':q})
    J=np.stack(cols,axis=1)
    rhs=cube_coeff(flatten(cubes[drop]))
    return J,rhs,meta

def rank_mod(A,p):
    A=np.array(A,dtype=object); m,n=A.shape
    B=[[int(A[i,j])%p for j in range(n)] for i in range(m)]
    r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if B[i][c]%p: piv=i; break
        if piv is None: continue
        B[r],B[piv]=B[piv],B[r]
        inv=pow(B[r][c]%p,-1,p)
        B[r]=[(x*inv)%p for x in B[r]]
        for i in range(m):
            if i!=r and B[i][c]%p:
                f=B[i][c]%p
                B[i]=[(B[i][j]-f*B[r][j])%p for j in range(n)]
        r+=1
        if r==m: break
    return r

def rank_Q(A):
    M=sp.Matrix([[int(x) for x in row] for row in np.array(A,dtype=object).tolist()])
    return int(M.rank())

def main():
    primes=[1000003,1000033,65521,32003]
    records=[]
    for drop in range(11):
        J,rhs,meta=build_jacobian(drop, include_global=True)
        Aaug=np.concatenate([J,rhs.reshape(-1,1)],axis=1)
        t=time.time()
        rankq=rank_Q(J); augq=rank_Q(Aaug); sec=time.time()-t
        ranks={str(p):rank_mod(J,p) for p in primes}
        aug={str(p):rank_mod(Aaug,p) for p in primes}
        rec={
            'drop':drop,'jacobian_shape':list(J.shape),'rhs_nonzero_monomials':int(sum(1 for x in rhs if x)),
            'rank_Q':rankq,'augmented_rank_Q':augq,'rhs_in_Q_image': bool(augq==rankq),
            'exact_rank_seconds':sec,
            'rank_mod_primes':ranks,'augmented_rank_mod_primes':aug,
        }
        print(rec, flush=True)
        records.append(rec)
    result={
        'parameter_columns':{'internal_sl3':32,'global_ad_orbit':8,'kept_cube_perturbations':90,'total':130},
        'interpretation':'Exact QQ ranks with global adjoint orbit directions included. Augmented rank > rank proves first-order nonrepairability for that one-cube deletion in the local BILR m=4 chart.',
        'records':records,
        'all_drops_first_order_nonrepairable_over_Q': bool(all(not r['rhs_in_Q_image'] for r in records)),
    }
    out=OUT/'ballard_delete_linearization_v2.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('Saved',out)

if __name__=='__main__': main()
