#!/usr/bin/env python3
"""Representation-component check for the analysis Gram polarization split.

For W=U(row) \otimes C(column),
    Lambda^2 W = (Lambda^2 U \otimes Sym^2 C) ⊕ (Sym^2 U \otimes Lambda^2 C).
The tau complementary target L is Lambda^2 U tensored with the column metric
I_C, hence lies in the first 18-dimensional component.  The six free products
coming from the row-norm Gram polarization have both linear forms with the same
row vector h and two column vectors p,q, so their wedges lie in the second
component Sym^2 U \otimes Lambda^2 C.

Therefore the literal f=6,m=6 Gram-polarization starting point cannot be completed
to f=6,m=8 by only two extra free orbits: the projection of L to the first
component is 3-dimensional, while two extra decomposable wedges span at most a
2-dimensional projection there.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

SESSION=Path(__file__).resolve().parents[1]
OUT=SESSION/"data"/"transpose_component"
OUT.mkdir(parents=True, exist_ok=True)

p=65521
I=24297  # sqrt(-1) mod 65521
PAIRS=[(i,j) for i in range(9) for j in range(i+1,9)]
PI={q:i for i,q in enumerate(PAIRS)}
def idx(i,k): return 3*i+k

def add_wedge(vec,a,b,c):
    if a==b: return
    if a<b: vec[PI[(a,b)]]=(vec[PI[(a,b)]]+c)%p
    else: vec[PI[(b,a)]]=(vec[PI[(b,a)]]-c)%p

def wedge(a,b):
    v=np.zeros(36,dtype=np.int64)
    for i in range(9):
        for j in range(i+1,9):
            v[PI[(i,j)]]=(int(a[i])*int(b[j])-int(a[j])*int(b[i]))%p
    return v%p

def rank(M):
    M=np.array(M,dtype=np.int64)%p
    rows,cols=M.shape
    r=0
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i,c]%p: piv=i; break
        if piv is None: continue
        M[[r,piv]]=M[[piv,r]]
        inv=pow(int(M[r,c]),p-2,p)
        M[r]=M[r]*inv%p
        for i in range(rows):
            if i!=r and M[i,c]%p:
                M[i]=(M[i]-int(M[i,c])*M[r])%p
        r+=1
        if r==rows: break
    return r

def comp1_basis():
    # Lambda^2 U ⊗ Sym^2 C, dim 3*6=18
    B=[]; labels=[]
    for i,j in [(0,1),(0,2),(1,2)]:
        for k in range(3):
            for l in range(k,3):
                v=np.zeros(36,dtype=np.int64)
                if k==l:
                    add_wedge(v,idx(i,k),idx(j,k),1)
                else:
                    add_wedge(v,idx(i,k),idx(j,l),1)
                    add_wedge(v,idx(i,l),idx(j,k),1)
                B.append(v); labels.append(("LambdaU_SymC",(i,j),(k,l)))
    return np.array(B,dtype=np.int64),labels

def comp2_basis():
    # Sym^2 U ⊗ Lambda^2 C, dim 6*3=18
    B=[]; labels=[]
    for i in range(3):
        for j in range(i,3):
            for k,l in [(0,1),(0,2),(1,2)]:
                v=np.zeros(36,dtype=np.int64)
                if i==j:
                    add_wedge(v,idx(i,k),idx(i,l),1)
                else:
                    add_wedge(v,idx(i,k),idx(j,l),1)
                    add_wedge(v,idx(i,l),idx(j,k),-1)
                B.append(v); labels.append(("SymU_LambdaC",(i,j),(k,l)))
    return np.array(B,dtype=np.int64),labels

def target_basis():
    T=[]
    for i,j in [(0,1),(0,2),(1,2)]:
        v=np.zeros(36,dtype=np.int64)
        for k in range(3): add_wedge(v,idx(i,k),idx(j,k),-1)
        T.append(v)
    return np.array(T,dtype=np.int64)%p

def dps_free_wedges():
    hs=[]
    for subset in [(0,),(1,),(2,),(0,1),(0,2),(1,2)]:
        h=np.zeros(3,dtype=np.int64)
        for s in subset: h[s]=1
        hs.append((subset,h))
    W=[]
    for subset,h in hs:
        a=np.zeros(9,dtype=np.int64); b=np.zeros(9,dtype=np.int64)
        for row in range(3):
            a[idx(row,0)] = (a[idx(row,0)] + h[row])%p
            a[idx(row,1)] = (a[idx(row,1)] + I*h[row])%p
            b[idx(row,0)] = (b[idx(row,0)] + h[row])%p
            b[idx(row,1)] = (b[idx(row,1)] - I*h[row])%p
        W.append(wedge(a,b))
    return np.array(W,dtype=np.int64)%p

def contains(A,B):
    # row spans: is every row of B in row span A?
    if len(A)==0: return False
    return rank(A)==rank(np.vstack([A,B]))

def main():
    C1,_=comp1_basis(); C2,_=comp2_basis(); T=target_basis(); W=dps_free_wedges()
    allbasis=np.vstack([C1,C2])
    out={
        "prime":p,
        "component_dimensions": {"Lambda2U_Sym2C_rank":rank(C1), "Sym2U_Lambda2C_rank":rank(C2), "direct_sum_rank":rank(allbasis)},
        "target": {"rank":rank(T), "contained_in_component1":contains(C1,T), "contained_in_component2":contains(C2,T)},
        "dps_six_free_wedges": {"rank":rank(W), "contained_in_component1":contains(C1,W), "contained_in_component2":contains(C2,W), "rank_with_target":rank(np.vstack([W,T]))},
        "f6_m8_literal_polarization_obstruction": "Since the six DPS free wedges lie in Sym^2U⊗Lambda^2C and the anti target has 3-dimensional projection to Lambda^2U⊗Sym^2C, two additional free orbits can contribute at most two dimensions to that projection; hence this exact f=6,m=8 completion cannot satisfy the complementary sector.",
    }
    path=OUT/"component_obstruction_f6m8_polarization.json"
    path.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2))
    print(f"SAVED {path}")

if __name__=='__main__':
    main()
