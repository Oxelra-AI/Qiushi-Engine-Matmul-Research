#!/usr/bin/env python3
"""analysis: full-containment and deletion/tangent diagnostics for transported Laderman.

The anti-sector correction shows the eight free standard-tau bivectors span L_anti.
This script checks the full corrected first-slice containment L1 subset span{vec(b)vec(c)^T}
for the transported Laderman scheme over F_65521, then measures what happens when
one fixed term is deleted (candidate (6,8) rank-22 skeleton).  It also computes a
very permissive first-order tangent envelope from the remaining rank-one generators:
if even base+tangent misses L1, the deletion is locally rigid; if it contains L1,
there is only a possible repair direction, not a rank-22 construction.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

SCRIPT_DIR=Path(__file__).resolve().parent
WS=SCRIPT_DIR.parent
OUT=WS/"data"/"transport_laderman_tau"
OUT.mkdir(parents=True, exist_ok=True)
P=65521; IROOT=41224

def inv(a): return pow(int(a)%P,-1,P)
def mod(A): return np.asarray(A,dtype=object)%P

def mat_inv(A):
    A=mod(A); n=A.shape[0]
    aug=np.concatenate([A.copy(),np.eye(n,dtype=object)],axis=1)%P
    r=0
    for c in range(n):
        piv=next((i for i in range(r,n) if int(aug[i,c])%P),None)
        if piv is None: raise ValueError('singular')
        if piv!=r: aug[[r,piv]]=aug[[piv,r]]
        aug[r,:]=(aug[r,:]*inv(aug[r,c]))%P
        for i in range(n):
            if i!=r and int(aug[i,c])%P:
                aug[i,:]=(aug[i,:]-aug[i,c]*aug[r,:])%P
        r+=1
    return aug[:,n:]%P

def rank(M):
    M=mod(M).copy(); m,n=M.shape; r=0
    for c in range(n):
        piv=next((i for i in range(r,m) if int(M[i,c])%P),None)
        if piv is None: continue
        if piv!=r: M[[r,piv]]=M[[piv,r]]
        M[r,:]=(M[r,:]*inv(M[r,c]))%P
        for i in range(m):
            if i!=r and int(M[i,c])%P:
                M[i,:]=(M[i,:]-M[i,c]*M[r,:])%P
        r+=1
        if r==m: break
    return r

def row_contains(B,L):
    rB=rank(B); rBL=rank(np.vstack([B,L])%P)
    return rB==rBL, rB, rBL, rBL-rB

# Load and transport as in transport_laderman_to_standard_tau.py
src_path=SCRIPT_DIR/"laderman_tau_decomp.py"
src=src_path.read_text(); prefix=src.split('print(f"Sum matches T333')[0]
ns={"__file__":str(src_path),"__name__":"defs_only"}
exec(compile(prefix,str(src_path),"exec"),ns)
terms=[(mod(a),mod(b),mod(c)) for a,b,c in ns['terms']]
eps1=mod(ns['eps1']); pi12=mod(ns['pi12']); I3=mod(ns['I3'])
Q=eps1@pi12%P; R=np.diag([IROOT,1,1]).astype(object)%P
Qinv=mat_inv(Q); Rinv=mat_inv(R)
def g(a,b,c): return (a@Qinv%P, Q@b@Rinv%P, R@c%P)
transported=[g(a,b,c) for a,b,c in terms]
fixed=[0,3,9,11,18,20,22]
free_pairs=[(1,4),(2,5),(6,15),(7,17),(8,16),(10,13),(12,14),(19,21)]  # 0-based

# L1 basis: entries (3b+k, 3k+a)
def build_L1():
    rows=[]
    for a in range(3):
        for b in range(3):
            M=np.zeros((9,9),dtype=object)
            for k in range(3): M[3*b+k,3*k+a]=1
            rows.append(M.reshape(81))
    return np.vstack(rows)%P
L=build_L1()

# rank-one matrices from terms
def vec9(M): return np.asarray(M,dtype=object).reshape(9)%P
X=[]; V=[]; W=[]
for a,b,c in transported:
    v=vec9(b); w=vec9(c)
    V.append(v); W.append(w)
    X.append(np.outer(v,w).reshape(81)%P)
X=np.vstack(X)%P

# transpose permutation matrix on 3x3 row-major vectors
def Tvec(v): return np.asarray(v,dtype=object).reshape(3,3).T.reshape(9)%P

full_ok,full_rank,full_aug,full_def=row_contains(X,L)

# tangent bases
def tangent_rankone(v,w):
    rows=[]
    for a in range(9):
        e=np.zeros(9,dtype=object); e[a]=1
        rows.append(np.outer(e,w).reshape(81)%P)
        rows.append(np.outer(v,e).reshape(81)%P)
    return rows

def tangent_fixed(v,w):
    # Determine lambda such that w = lambda*T(v). If unavailable, fall back to rank-one tangent.
    Tv=Tvec(v); lam=None
    for x,y in zip(w,Tv):
        if int(y)%P:
            lam=int(x)*inv(y)%P if lam is None else lam
            if int(x)%P != (lam*int(y))%P:
                lam=None; break
        elif int(x)%P:
            lam=None; break
    if lam is None:
        return tangent_rankone(v,w)
    rows=[]
    for a in range(9):
        e=np.zeros(9,dtype=object); e[a]=1
        dw=(lam*Tvec(e))%P
        rows.append((np.outer(e,w)+np.outer(v,dw)).reshape(81)%P)
    return rows

# For a deletion, compute tangent envelope using remaining terms; both unconstrained and a tau-structured envelope.
def deletion_diag(delete_idx):
    keep=[i for i in range(23) if i!=delete_idx]
    B=X[keep]
    ok,rB,rBL,defect=row_contains(B,L)
    # Unconstrained rank-one tangent envelope for all kept slots.
    tan=[]
    for i in keep:
        tan.extend(tangent_rankone(V[i],W[i]))
    Env=np.vstack([B]+[np.vstack(tan)])%P
    eok,er,eaug,edef=row_contains(Env,L)
    # Tau-structured approximate tangent envelope: fixed slots use fixed tangent; free slots use rep+partner tangent slots.
    stan=[]
    for i in fixed:
        if i!=delete_idx:
            stan.extend(tangent_fixed(V[i],W[i]))
    for i,j in free_pairs:
        if i==delete_idx or j==delete_idx:
            continue
        # Use independent rep variations but include both actual slot tangents; this is still permissive because
        # it does not solve the true incidence linearization, but respects the orbit grouping at the slot level.
        stan.extend(tangent_rankone(V[i],W[i]))
        stan.extend(tangent_rankone(V[j],W[j]))
    SEnv=np.vstack([B]+[np.vstack(stan)])%P
    sok,sr,saug,sdef=row_contains(SEnv,L)
    return {
        "delete_term_1based": delete_idx+1,
        "deleted_kind": "fixed" if delete_idx in fixed else "free_slot",
        "base_rank": int(rB), "base_aug_rank": int(rBL), "base_defect": int(defect), "base_contains_L1": bool(ok),
        "unconstrained_rankone_tangent_envelope_rank": int(er),
        "unconstrained_tangent_aug_rank": int(eaug),
        "unconstrained_tangent_defect": int(edef),
        "unconstrained_tangent_contains_L1": bool(eok),
        "tau_structured_permissive_tangent_envelope_rank": int(sr),
        "tau_structured_tangent_aug_rank": int(saug),
        "tau_structured_tangent_defect": int(sdef),
        "tau_structured_tangent_contains_L1": bool(sok)
    }

fixed_deletions=[deletion_diag(i) for i in fixed]
free_orbit_deletions=[]
for i,j in free_pairs:
    keep=[k for k in range(23) if k not in (i,j)]
    ok,rB,rBL,defect=row_contains(X[keep],L)
    free_orbit_deletions.append({
        "delete_free_pair_1based":[i+1,j+1],
        "base_rank":int(rB),"base_aug_rank":int(rBL),"base_defect":int(defect),"base_contains_L1":bool(ok)
    })

out={
    "field":f"F_{P}",
    "full_23_rank":int(full_rank),"full_23_aug_rank":int(full_aug),"full_23_defect":int(full_def),"full_23_contains_L1":bool(full_ok),
    "fixed_deletion_diagnostics":fixed_deletions,
    "free_orbit_deletion_diagnostics":free_orbit_deletions,
    "interpretation":"Full corrected L1 containment for transported Laderman; deletion+tangent envelopes are local diagnostics only. Tangent containment is not an exact rank-22 construction, while tangent failure would be a strong local obstruction."
}
path=OUT/"transported_laderman_full_containment_tangent_F65521.json"
path.write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
print(f"SAVED {path}")
