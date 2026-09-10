#!/usr/bin/env python3
"""analysis: test seven-subsets of the convention-correct Laderman anti witness.

Input: transported_laderman_standard_tau_F65521.json says the eight free standard-tau
bivectors span L_anti over F_65521 (and Q(i)).  This script recomputes the witness
from the transport data, then checks whether any 7 of the 8 free-orbit representative
bivectors still span L_anti.  A positive result would prove m0 <= 7; a negative
result only says the Laderman witness is minimally eight within this configuration.
"""
from __future__ import annotations
import json
from pathlib import Path
import itertools
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "transport_laderman_tau"
OUT.mkdir(parents=True, exist_ok=True)
P = 65521
I_SQRT_MINUS_ONE = 41224

def inv(a): return pow(int(a) % P, -1, P)

def mod(A): return np.asarray(A, dtype=object) % P

def mat_inv(A):
    A = mod(A); n=A.shape[0]
    aug = np.concatenate([A.copy(), np.eye(n, dtype=object)], axis=1) % P
    r=0
    for c in range(n):
        piv=None
        for i in range(r,n):
            if int(aug[i,c])%P:
                piv=i; break
        if piv is None: raise ValueError('singular')
        if piv != r: aug[[r,piv]]=aug[[piv,r]]
        aug[r,:]=(aug[r,:]*inv(aug[r,c]))%P
        for i in range(n):
            if i!=r and int(aug[i,c])%P:
                aug[i,:]=(aug[i,:]-aug[i,c]*aug[r,:])%P
        r+=1
    return aug[:,n:]%P

def rank(M):
    M=mod(M).copy(); m,n=M.shape; r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if int(M[i,c])%P:
                piv=i; break
        if piv is None: continue
        if piv!=r: M[[r,piv]]=M[[piv,r]]
        M[r,:]=(M[r,:]*inv(M[r,c]))%P
        for i in range(m):
            if i!=r and int(M[i,c])%P:
                M[i,:]=(M[i,:]-M[i,c]*M[r,:])%P
        r+=1
        if r==m: break
    return r

def row_space_contains(B, T):
    rB=rank(B); rBT=rank(np.vstack([B,T]))
    return rB==rBT, rB, rBT

# Load definitions from analysis
src_path=SCRIPT_DIR/"laderman_tau_decomp.py"
src=src_path.read_text(); prefix=src.split('print(f"Sum matches T333')[0]
ns={"__file__":str(src_path),"__name__":"defs_only"}
exec(compile(prefix,str(src_path),"exec"),ns)
terms=[(mod(a),mod(b),mod(c)) for a,b,c in ns['terms']]
eps1=mod(ns['eps1']); pi12=mod(ns['pi12']); eps2=mod(ns['eps2']); I3=mod(ns['I3'])
Q=eps1@pi12%P; R=np.diag([I_SQRT_MINUS_ONE,1,1]).astype(object)%P
Qinv=mat_inv(Q); Rinv=mat_inv(R)

def g(a,b,c):
    return (a@Qinv%P, Q@b@Rinv%P, R@c%P)

transported=[g(a,b,c) for a,b,c in terms]
free_pairs=[(2,5),(3,6),(7,16),(8,18),(9,17),(11,14),(13,15),(20,22)]
rep_indices=[i-1 for i,j in free_pairs]

WEDGE_PAIRS=[(a,b) for a in range(9) for b in range(a+1,9)]
SKEW_PAIRS=[(0,1),(0,2),(1,2)]

def vec9(M): return np.asarray(M,dtype=object).reshape(9)%P

def wedge(v,w):
    out=np.zeros(36,dtype=object)
    for t,(i,j) in enumerate(WEDGE_PAIRS): out[t]=(v[i]*w[j]-v[j]*w[i])%P
    return out

def anti_target():
    def idx(i,k): return 3*i+k
    T=np.zeros((3,36),dtype=object)
    for r,(a,b) in enumerate(SKEW_PAIRS):
        M=np.zeros((9,9),dtype=object)
        for i in range(3):
            for j in range(3):
                Aij=0
                if (i,j)==(a,b): Aij=1
                elif (i,j)==(b,a): Aij=-1
                if Aij==0: continue
                for k in range(3): M[idx(j,k),idx(i,k)]=(M[idx(j,k),idx(i,k)]+Aij)%P
        for t,(i,j) in enumerate(WEDGE_PAIRS): T[r,t]=M[i,j]%P
    return T%P

A=anti_target()
B=[]
for idx0 in rep_indices:
    _,b,c=transported[idx0]
    B.append(wedge(vec9(b), vec9(c.T)))
B=np.vstack(B)%P

full_contains, full_rank, full_aug = row_space_contains(B,A)
subset_results=[]
for skip in range(8):
    sub=np.delete(B, skip, axis=0)
    ok,rB,rBT=row_space_contains(sub,A)
    subset_results.append({
        "skip_free_pair_1based": list(free_pairs[skip]),
        "rank": int(rB),
        "augmented_rank": int(rBT),
        "defect": int(rBT-rB),
        "spans_Lanti": bool(ok)
    })

# also compute which linear coefficients from previous run use each rep nontrivially
coeff_path=OUT/"transported_laderman_standard_tau_F65521.json"
coeffs=json.loads(coeff_path.read_text())["coefficients_A_TARGET_in_eight_rep_basis"]
used_by_target=[]
for j in range(8):
    nz=[r for r in range(3) if int(coeffs[r][j])%P != 0]
    used_by_target.append({"free_pair_1based": list(free_pairs[j]), "target_rows_using_it": nz})

out={
    "field": f"F_{P}",
    "source": "transported Laderman under standard tau, using reps of the eight free pairs",
    "full_8_rank": int(full_rank),
    "full_8_augmented_rank": int(full_aug),
    "full_8_spans_Lanti": bool(full_contains),
    "seven_subset_results": subset_results,
    "any_seven_subset_spans_Lanti": any(x["spans_Lanti"] for x in subset_results),
    "target_coeff_support_in_8_rep_basis": used_by_target,
    "interpretation": "No seven-subset hit would only show this Laderman m=8 witness is internally minimal; it is not an m0>=8 theorem. A seven-subset hit would prove m0<=7."
}
path=OUT/"transported_laderman_m7_subsets_F65521.json"
path.write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
print(f"SAVED {path}")
