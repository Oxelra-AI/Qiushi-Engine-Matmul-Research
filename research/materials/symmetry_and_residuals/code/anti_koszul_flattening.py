#!/usr/bin/env python3
"""Exterior flattening lower bounds for the tau-complement anti subspace.

For T = sum_{r=1}^3 e_r \otimes theta_r in A \otimes Lambda^2 W,
with W=K^9 and theta_r the three rows of the anti target, define
  F_q(T): A^* \otimes Lambda^q W -> Lambda^{q+2} W,
  f \otimes eta |-> sum_r f(e_r) theta_r wedge eta.
If T = sum_{j=1}^m c_j \otimes (p_j wedge q_j), each summand has rank
C(7,q) under F_q. Hence m >= ceil(rank(F_q(T))/C(7,q)).
This is a lower bound on the tau-structured anti entry number m0.
"""
from __future__ import annotations
import itertools, math, json
from pathlib import Path
import numpy as np

SESSION=Path(__file__).resolve().parents[1]
OUT=SESSION/"data"/"transpose_component"
OUT.mkdir(parents=True, exist_ok=True)
p=1000003
n=9

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
pairs=[(i,j) for i in range(n) for j in range(i+1,n)]
pi={q:i for i,q in enumerate(pairs)}
def idx(i,k): return 3*i+k
def add(v,a,b,c):
    if a>b: a,b=b,a; c=-c
    v[pi[(a,b)]]=(v[pi[(a,b)]]+c)%p

def target_basis():
    T=[]
    for i,j in [(0,1),(0,2),(1,2)]:
        v=np.zeros(len(pairs),dtype=np.int64)
        for k in range(3): add(v,idx(i,k),idx(j,k),-1)
        T.append(v%p)
    return np.array(T,dtype=np.int64)%p

def wedge_sign(two, I):
    seq=list(two)+list(I)
    if len(set(seq))<len(seq): return None,0
    invs=0
    for a in range(len(seq)):
        for b in range(a+1,len(seq)):
            if seq[a]>seq[b]: invs+=1
    return tuple(sorted(seq)), (-1 if invs%2 else 1)

def flatten_rank(T,q):
    dom=list(itertools.combinations(range(n),q))
    cod=list(itertools.combinations(range(n),q+2))
    ci={c:i for i,c in enumerate(cod)}
    M=np.zeros((len(cod),3*len(dom)),dtype=np.int64)
    for r,theta in enumerate(T):
        for dI,I in enumerate(dom):
            col=r*len(dom)+dI
            for coeff,(a,b) in zip(theta,pairs):
                if coeff%p==0: continue
                K,s=wedge_sign((a,b),I)
                if s:
                    M[ci[K],col]=(M[ci[K],col]+int(coeff)*s)%p
    R=rank(M)
    simple=math.comb(n-2,q) if q<=n-2 else 0
    lb=math.ceil(R/simple) if simple else None
    return {"q":q,"domain_dim":3*len(dom),"codomain_dim":len(cod),"rank":R,"rank_per_decomposable":simple,"lower_bound_m":lb}

def main():
    T=target_basis()
    rows=[flatten_rank(T,q) for q in range(0,8)]
    out={"prime":p,"target_rank_in_Lambda2W":rank(T),"flattenings":rows,
         "best_lower_bound_m":max(r["lower_bound_m"] for r in rows if r["lower_bound_m"] is not None)}
    path=OUT/"anti_koszul_flattening.json"
    path.write_text(json.dumps(out,indent=2)+"\n")
    for r in rows:
        print(r)
    print(f"best lower bound m >= {out['best_lower_bound_m']}")
    print(f"SAVED {path}")

if __name__=='__main__':
    main()
