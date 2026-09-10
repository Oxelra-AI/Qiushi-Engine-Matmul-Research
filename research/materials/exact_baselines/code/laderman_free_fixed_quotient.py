#!/usr/bin/env python3
"""analysis: quotient structure of transported Laderman free/fixed split.

Question: after transporting Laderman to standard tau, its eight free orbits already
solve the anti-sector. Could a (6,8) rank-22 scheme be obtained by keeping those
free pairs and replacing the seven fixed terms by only six tau-fixed generators?

If the image of L1 modulo the span of the 16 free slot matrices has dimension 7,
then no: six additional fixed generators (indeed any six additional matrices) span
at most six quotient dimensions. This does not rule out (6,8) after moving the free
pairs; it only says the Laderman free-pair anti witness is not itself enough for a
one-fixed-term compression.
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

def rref(M):
    M=mod(M).copy(); m,n=M.shape; r=0; piv=[]
    for c in range(n):
        pivrow=next((i for i in range(r,m) if int(M[i,c])%P),None)
        if pivrow is None: continue
        if pivrow!=r: M[[r,pivrow]]=M[[pivrow,r]]
        M[r,:]=(M[r,:]*inv(M[r,c]))%P
        for i in range(m):
            if i!=r and int(M[i,c])%P:
                M[i,:]=(M[i,:]-M[i,c]*M[r,:])%P
        piv.append(c); r+=1
        if r==m: break
    return M,r,piv

def rank(M): return rref(M)[1]

def row_contains(B,L):
    rB=rank(B); rBL=rank(np.vstack([B,L])%P); return rB==rBL,rB,rBL,rBL-rB

# Load and transport
src_path=SCRIPT_DIR/"laderman_tau_decomp.py"
src=src_path.read_text(); prefix=src.split('print(f"Sum matches T333')[0]
ns={"__file__":str(src_path),"__name__":"defs_only"}
exec(compile(prefix,str(src_path),"exec"),ns)
terms=[(mod(a),mod(b),mod(c)) for a,b,c in ns['terms']]
eps1=mod(ns['eps1']); pi12=mod(ns['pi12'])
Q=eps1@pi12%P; R=np.diag([IROOT,1,1]).astype(object)%P
Qinv=mat_inv(Q); Rinv=mat_inv(R)
def g(a,b,c): return (a@Qinv%P,Q@b@Rinv%P,R@c%P)
transported=[g(a,b,c) for a,b,c in terms]
fixed=[0,3,9,11,18,20,22]
free_pairs=[(1,4),(2,5),(6,15),(7,17),(8,16),(10,13),(12,14),(19,21)]
free_slots=[i for pair in free_pairs for i in pair]

def vec9(M): return np.asarray(M,dtype=object).reshape(9)%P
X=[]
for a,b,c in transported:
    X.append(np.outer(vec9(b),vec9(c)).reshape(81)%P)
X=np.vstack(X)%P

def build_L1():
    rows=[]
    for a in range(3):
        for b in range(3):
            M=np.zeros((9,9),dtype=object)
            for k in range(3): M[3*b+k,3*k+a]=1
            rows.append(M.reshape(81))
    return np.vstack(rows)%P
L=build_L1()

freeX=X[free_slots]
fixedX=X[fixed]
full_ok,full_r,full_aug,full_def=row_contains(X,L)
free_ok,free_r,free_aug,free_def=row_contains(freeX,L)
fixed_ok,fixed_r,fixed_aug,fixed_def=row_contains(fixedX,L)
free_plus_fixed_ok,_,_,_=row_contains(np.vstack([freeX,fixedX]),L)

# image dimension of L modulo free span is free_aug-free_r.
quotient_dim_L_mod_free=free_aug-free_r
# each old fixed deletion against free span
old_fixed_image_ranks=[]
for skip_pos,idx in enumerate(fixed):
    sub_fixed=np.delete(fixedX, skip_pos, axis=0)
    ok,rB,rBL,defect=row_contains(np.vstack([freeX,sub_fixed]),L)
    old_fixed_image_ranks.append({
        "omitted_fixed_term_1based":idx+1,
        "rank_free_plus_six_old_fixed":int(rB),
        "augmented_rank":int(rBL),
        "defect":int(defect),
        "contains_L1":bool(ok)
    })

out={
    "field":f"F_{P}",
    "full_23_contains_L1":bool(full_ok),
    "full_23_rank":int(full_r),
    "free_slots_count":len(free_slots),
    "free_span_rank":int(free_r),
    "rank_free_plus_L1":int(free_aug),
    "L1_quotient_dimension_mod_free_span":int(quotient_dim_L_mod_free),
    "free_span_contains_L1":bool(free_ok),
    "fixed_span_rank":int(fixed_r),
    "rank_fixed_plus_L1":int(fixed_aug),
    "fixed_span_contains_L1":bool(fixed_ok),
    "free_plus_all_7_fixed_contains_L1":bool(free_plus_fixed_ok),
    "old_fixed_deletion_defects":old_fixed_image_ranks,
    "consequence": "With the transported Laderman eight free orbits held fixed, L1 has 6-dimensional image modulo their 16 slot span. Thus a (6,8) compression is dimension-tight, not dimension-impossible: six fixed generators would have to span exactly this residual quotient image. The six old fixed terms obtained by deleting any one of Laderman's seven fixed terms all leave defect 1, so direct deletion fails, but a moved six-fixed replacement is not ruled out."
}
path=OUT/"transported_laderman_free_fixed_quotient_F65521.json"
path.write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
print(f"SAVED {path}")
