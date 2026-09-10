#!/usr/bin/env python3
"""Compute Koszul/exterior flattening lower bounds for small matrix multiplication blocks."""
from __future__ import annotations
import itertools, math, json
from pathlib import Path
import numpy as np


def rank_mod(M, p=1000003):
    A=np.array(M%p,dtype=np.int64,copy=True); m,n=A.shape; r=0
    for c in range(n):
        if r>=m: break
        nz=np.nonzero(A[r:,c])[0]
        if len(nz)==0: continue
        piv=r+int(nz[0])
        if piv!=r: A[[r,piv]]=A[[piv,r]]
        inv=pow(int(A[r,c]),p-2,p)
        A[r]=(A[r]*inv)%p
        fac=A[:,c].copy(); fac[r]=0
        rows=np.nonzero(fac)[0]
        if len(rows): A[rows]=(A[rows]-fac[rows,None]*A[r])%p
        r+=1
    return r


def wedge_sign_insert(I, x):
    # I sorted tuple, x not in I. Return sorted union and sign for e_x wedge e_I.
    # e_x ∧ e_{i1}∧...; moving x to sorted position crosses count of i < x.
    cnt=sum(1 for i in I if i < x)
    sign=-1 if cnt%2 else 1
    J=tuple(sorted((x,)+tuple(I)))
    return J, sign


def koszul_bound(support, dims, mode, p_wedge):
    # support triples in local factor coordinates [0..dims[k]-1]. Treat chosen mode as A.
    modes=[0,1,2]
    others=[m for m in modes if m!=mode]
    da=dims[mode]; db=dims[others[0]]; dc=dims[others[1]]
    if p_wedge<0 or p_wedge>=da: return None
    wedges_p=list(itertools.combinations(range(da), p_wedge))
    wedges_q=list(itertools.combinations(range(da), p_wedge+1))
    wi={w:i for i,w in enumerate(wedges_p)}; wq={w:i for i,w in enumerate(wedges_q)}
    M=np.zeros((len(wedges_q)*dc, db*len(wedges_p)), dtype=np.int64)
    for t in support:
        a=t[mode]; b=t[others[0]]; c=t[others[1]]
        for I in wedges_p:
            if a in I: continue
            J,sgn=wedge_sign_insert(I,a)
            row=wq[J]*dc+c
            col=b*len(wedges_p)+wi[I]
            M[row,col]+=sgn
    rr=rank_mod(M,1000003)
    denom=math.comb(da-1,p_wedge)
    return {'mode':mode,'p':p_wedge,'matrix_shape':[int(M.shape[0]),int(M.shape[1])],'rank':rr,'denominator':denom,'lower_bound_ceil':(rr+denom-1)//denom}


def rectangular_support(m,n,p):
    # local matrix multiplication: A indices (a,b), B (b,c), C (a,c)
    U=[(a,b) for a in range(m) for b in range(n)]
    V=[(b,c) for b in range(n) for c in range(p)]
    W=[(a,c) for a in range(m) for c in range(p)]
    ui={x:i for i,x in enumerate(U)}; vi={x:i for i,x in enumerate(V)}; wi={x:i for i,x in enumerate(W)}
    supp=[]
    for a in range(m):
      for b in range(n):
        for c in range(p):
          supp.append((ui[(a,b)], vi[(b,c)], wi[(a,c)]))
    return supp, (len(U),len(V),len(W))


def analyze_rect(m,n,p):
    supp,dims=rectangular_support(m,n,p)
    records=[]
    for mode in range(3):
      for pw in range(dims[mode]):
        rec=koszul_bound(supp,dims,mode,pw)
        if rec: records.append(rec)
    best=max(records,key=lambda r:r['lower_bound_ceil'])
    return {'format':[m,n,p],'factor_dims':list(dims),'support_size':len(supp),'records':records,'best':best}


def main():
    targets=[(2,2,2),(3,2,2),(2,3,2),(2,2,3),(3,3,2),(3,2,3),(2,3,3),(3,3,1),(3,1,3),(1,3,3)]
    result={}
    for fmt in targets:
        rec=analyze_rect(*fmt)
        result[str(fmt)]=rec
        print(fmt,'dims',rec['factor_dims'],'best',rec['best'])
    out=Path('data/semisimple_arrangement/koszul_block_bounds.json')
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('wrote',out)

if __name__=='__main__':
    main()
