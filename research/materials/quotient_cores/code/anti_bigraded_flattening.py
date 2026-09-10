#!/usr/bin/env python3
"""Bigraded exterior flattenings for T_anti in A ⊗ Λ²W.

For T in A ⊗ Λ²W, define wedge flattenings
  Λ^s A ⊗ Λ^q W -> Λ^{s+1} A ⊗ Λ^{q+2} W
by wedging the A factor and the W 2-form factor.  For a structured rank-one term
a ⊗ (p∧q), the rank contribution is C(2,s)*C(7,q).  These give lower bounds
on m0, the number of tau-free orbits needed in the complementary sector.
"""
from __future__ import annotations
import itertools, math, json
from pathlib import Path
import numpy as np

SESSION=Path(__file__).resolve().parents[1]
OUT=SESSION/"data"/"transpose_component"
OUT.mkdir(parents=True, exist_ok=True)
p=1000003

def inv(a): return pow(int(a)%p,p-2,p)
def rank(M):
    M=np.array(M,dtype=np.int64)%p
    rows,cols=M.shape; r=0
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i,c]%p: piv=i; break
        if piv is None: continue
        M[[r,piv]]=M[[piv,r]]
        M[r]=M[r]*inv(M[r,c])%p
        for i in range(rows):
            if i!=r and M[i,c]%p:
                M[i]=(M[i]-int(M[i,c])*M[r])%p
        r+=1
        if r==rows: break
    return r

def idx(i,k): return 3*i+k
WPAIRS=[(i,j) for i in range(9) for j in range(i+1,9)]
WPI={q:i for i,q in enumerate(WPAIRS)}
def add_wedge2(v,a,b,c):
    if a>b: a,b=b,a; c=-c
    v[WPI[(a,b)]]=(v[WPI[(a,b)]]+c)%p

def target_theta():
    T=[]
    for i,j in [(0,1),(0,2),(1,2)]:
        v=np.zeros(36,dtype=np.int64)
        for k in range(3): add_wedge2(v,idx(i,k),idx(j,k),-1)
        T.append(v%p)
    return np.array(T,dtype=np.int64)%p

def wedge_sign(seq1, seq2):
    seq=list(seq1)+list(seq2)
    if len(set(seq))<len(seq): return None,0
    invs=0
    for i in range(len(seq)):
        for j in range(i+1,len(seq)):
            if seq[i]>seq[j]: invs+=1
    return tuple(sorted(seq)), (-1 if invs%2 else 1)

def flatten_rank(s,q,T):
    Adom=list(itertools.combinations(range(3),s))
    Acod=list(itertools.combinations(range(3),s+1))
    Wdom=list(itertools.combinations(range(9),q))
    Wcod=list(itertools.combinations(range(9),q+2))
    Aci={a:i for i,a in enumerate(Acod)}
    Wci={w:i for i,w in enumerate(Wcod)}
    rows=len(Acod)*len(Wcod)
    cols=len(Adom)*len(Wdom)
    M=np.zeros((rows,cols),dtype=np.int64)
    for r,theta in enumerate(T):
        avec=(r,)
        for ai,A0 in enumerate(Adom):
            A1,asgn=wedge_sign(avec,A0)
            if not asgn: continue
            ar=Aci[A1]
            for wi,W0 in enumerate(Wdom):
                col=ai*len(Wdom)+wi
                for coeff,pair in zip(theta,WPAIRS):
                    if coeff%p==0: continue
                    W1,wsgn=wedge_sign(pair,W0)
                    if not wsgn: continue
                    row=ar*len(Wcod)+Wci[W1]
                    M[row,col]=(M[row,col]+int(coeff)*asgn*wsgn)%p
    R=rank(M)
    per=math.comb(2,s)*math.comb(7,q) if s<=2 and q<=7 else 0
    lb=math.ceil(R/per) if per else None
    return {"s":s,"q":q,"matrix_shape":[rows,cols],"rank":R,"rank_per_structured_term":per,"lower_bound_m":lb}

def main():
    T=target_theta()
    rows=[]
    for s in range(0,3):
        for q in range(0,8):
            if s+1<=3 and q+2<=9:
                rows.append(flatten_rank(s,q,T))
    best=max(r["lower_bound_m"] for r in rows if r["lower_bound_m"] is not None)
    out={"prime":p,"target_theta_rank":rank(T),"flattenings":rows,"best_lower_bound_m":best}
    path=OUT/"anti_bigraded_flattening.json"
    path.write_text(json.dumps(out,indent=2)+"\n")
    for r in rows: print(r)
    print(f"best lower bound m >= {best}")
    print(f"SAVED {path}")

if __name__=='__main__':
    main()
