#!/usr/bin/env python3
"""Exact integer determinant for the analysis A-wedge flattening."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp

SESSION=Path(__file__).resolve().parents[1]
OUT=SESSION/"data"/"transpose_component"
OUT.mkdir(parents=True, exist_ok=True)

def idx(i,k): return 3*i+k
Apairs=[(0,1),(0,2),(1,2)]
Api={q:i for i,q in enumerate(Apairs)}
def wedge_A(a,s):
    if a==s: return None,0
    if a<s: return (a,s),1
    return (s,a),-1

def theta_contract(ap,beta):
    i,j=ap
    out=[0]*9
    for k in range(3):
        ai=idx(i,k); bj=idx(j,k)
        if beta==ai: out[bj]-=1
        if beta==bj: out[ai]+=1
    return out

def build():
    F=sp.zeros(27,27)
    for s in range(3):
        for beta in range(9):
            col=s*9+beta
            for r,ap in enumerate(Apairs):
                wa,sgn=wedge_A(r,s)
                if sgn==0: continue
                ar=Api[wa]
                wv=theta_contract(ap,beta)
                for wc,c in enumerate(wv):
                    if c:
                        F[ar*9+wc,col]+=sgn*c
    return F

def main():
    F=build()
    det=int(F.det())
    rk=int(F.rank())
    fac=sp.factorint(abs(det)) if det else {}
    out={"rank_over_Q":rk,"determinant":det,"abs_det_factorization":{str(k):int(v) for k,v in fac.items()},"char_scope":"full rank except characteristics dividing determinant; determinant here shows only characteristic 2 fails."}
    path=OUT/"anti_Awedge_integer_det.json"
    path.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2))
    print(f"SAVED {path}")

if __name__=='__main__':
    main()
