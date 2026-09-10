#!/usr/bin/env python3
"""analysis: first-order anti-sector seven-term deletion test at transported Laderman.

For each deletion from the eight free-bivector Laderman anti witness, compute the
linear span of the remaining seven bivectors plus their Grassmannian tangent spaces
v∧K^9 + K^9∧w.  If this tangent envelope does not contain L_anti, the deletion is
first-order rigid.  If it does, this is only a possible infinitesimal repair signal.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

SCRIPT_DIR=Path(__file__).resolve().parent
WS=SCRIPT_DIR.parent
OUT=WS/"data"/"transport_laderman_tau"
OUT.mkdir(parents=True,exist_ok=True)
P=65521; IROOT=41224

def inv(a): return pow(int(a)%P,-1,P)
def mod(A): return np.asarray(A,dtype=object)%P

def mat_inv(A):
    A=mod(A); n=A.shape[0]
    aug=np.concatenate([A.copy(),np.eye(n,dtype=object)],axis=1)%P; r=0
    for c in range(n):
        piv=next((i for i in range(r,n) if int(aug[i,c])%P),None)
        if piv is None: raise ValueError('singular')
        if piv!=r: aug[[r,piv]]=aug[[piv,r]]
        aug[r,:]=(aug[r,:]*inv(aug[r,c]))%P
        for i in range(n):
            if i!=r and int(aug[i,c])%P: aug[i,:]=(aug[i,:]-aug[i,c]*aug[r,:])%P
        r+=1
    return aug[:,n:]%P

def rref(M):
    M=mod(M).copy(); m,n=M.shape; r=0; piv=[]
    for c in range(n):
        pivrow=next((i for i in range(r,m) if int(M[i,c])%P),None)
        if pivrow is None: continue
        if pivrow!=r: M[[r,pivrow]]=M[[pivrow,r]]
        M[r,:]=(M[r,:]*inv(M[r,c]))%P
        for i in range(m):
            if i!=r and int(M[i,c])%P: M[i,:]=(M[i,:]-M[i,c]*M[r,:])%P
        piv.append(c); r+=1
    return M,r,piv

def rank(M): return rref(M)[1]
def row_contains(B,L):
    rB=rank(B); rBL=rank(np.vstack([B,L])%P); return rB==rBL,rB,rBL,rBL-rB

# load and transport
src_path=SCRIPT_DIR/"laderman_tau_decomp.py"
src=src_path.read_text(); prefix=src.split('print(f"Sum matches T333')[0]
ns={"__file__":str(src_path),"__name__":"defs_only"}
exec(compile(prefix,str(src_path),"exec"),ns)
terms=[(mod(a),mod(b),mod(c)) for a,b,c in ns['terms']]
eps1=mod(ns['eps1']); pi12=mod(ns['pi12'])
Q=eps1@pi12%P; R=np.diag([IROOT,1,1]).astype(object)%P; Qinv=mat_inv(Q); Rinv=mat_inv(R)
def g(a,b,c): return (a@Qinv%P, Q@b@Rinv%P, R@c%P)
transported=[g(a,b,c) for a,b,c in terms]
free_pairs=[(2,5),(3,6),(7,16),(8,18),(9,17),(11,14),(13,15),(20,22)]
rep=[i-1 for i,j in free_pairs]
WEDGE_PAIRS=[(a,b) for a in range(9) for b in range(a+1,9)]
def vec9(M): return np.asarray(M,dtype=object).reshape(9)%P
def wedge(v,w):
    out=np.zeros(36,dtype=object)
    for t,(i,j) in enumerate(WEDGE_PAIRS): out[t]=(v[i]*w[j]-v[j]*w[i])%P
    return out
def tangent_rows(v,w):
    rows=[]
    for a in range(9):
        e=np.zeros(9,dtype=object); e[a]=1
        rows.append(wedge(e,w)); rows.append(wedge(v,e))
    return rows
def anti_target():
    SKEW=[(0,1),(0,2),(1,2)]
    def idx(i,k): return 3*i+k
    T=np.zeros((3,36),dtype=object)
    for r,(a,b) in enumerate(SKEW):
        M=np.zeros((9,9),dtype=object)
        for i in range(3):
            for j in range(3):
                Aij=0
                if (i,j)==(a,b): Aij=1
                elif (i,j)==(b,a): Aij=-1
                if not Aij: continue
                for k in range(3): M[idx(j,k),idx(i,k)]=(M[idx(j,k),idx(i,k)]+Aij)%P
        for t,(i,j) in enumerate(WEDGE_PAIRS): T[r,t]=M[i,j]%P
    return T%P
A=anti_target()
Vs=[]; Ws=[]; B=[]
for i in rep:
    _,b,c=transported[i]
    v=vec9(b); w=vec9(c.T)
    Vs.append(v); Ws.append(w); B.append(wedge(v,w))
B=np.vstack(B)%P
full_ok,full_r,full_aug,full_def=row_contains(B,A)
results=[]
for skip in range(8):
    keep=[i for i in range(8) if i!=skip]
    base=B[keep]
    ok,rB,rBL,defect=row_contains(base,A)
    tan=[]
    for i in keep:
        tan.extend(tangent_rows(Vs[i],Ws[i]))
    env=np.vstack([base]+[np.vstack(tan)])%P
    eok,er,eaug,edef=row_contains(env,A)
    results.append({
        "skipped_free_pair_1based":list(free_pairs[skip]),
        "base_rank":int(rB),"base_aug_rank":int(rBL),"base_defect":int(defect),"base_contains_Lanti":bool(ok),
        "tangent_envelope_rank":int(er),"tangent_aug_rank":int(eaug),"tangent_defect":int(edef),"tangent_contains_Lanti":bool(eok)
    })
out={
    "field":f"F_{P}","full_8_rank":int(full_r),"full_8_contains_Lanti":bool(full_ok),
    "deletion_tangent_results":results,
    "interpretation":"If tangent_contains_Lanti is false, that deletion is first-order rigid. If true, it is only an infinitesimal possibility; full nonlinear m=7 incidence remains open."
}
path=OUT/"laderman_anti_m7_deletion_tangent_F65521.json"
path.write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2)); print(f"SAVED {path}")
