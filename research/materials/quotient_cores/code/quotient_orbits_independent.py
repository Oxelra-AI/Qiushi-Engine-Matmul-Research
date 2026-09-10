#!/usr/bin/env python3
"""analysis independent stabilizer orbit computation for rank-2/rank-3 quotients.

Computes the stabilizer of pivot A in GL_3(F2) x GL_3(F2), action
A -> P^T A Q^{-T}, on quotient points F2^9/<pivot>, and saves full orbit data.
This is independent of the peer orbit script, although it uses the same
mathematical convention already checked in analysis.
"""
from __future__ import annotations
import json, time, hashlib
from collections import Counter
from pathlib import Path
import numpy as np

ROOT=Path('research/research_record')
OUT=ROOT/'workspace/data/quotient_branches/quotient_orbits_independent.json'
PIVOTS={'rank2':17,'rank3':273}

def bits_to_mat(mask:int)->np.ndarray:
    return np.array([[(mask>>(3*i+j))&1 for j in range(3)] for i in range(3)],dtype=np.uint8)

def mat_to_bits(M)->int:
    x=0
    for i in range(3):
        for j in range(3):
            if int(M[i,j])&1: x |= 1<<(3*i+j)
    return x

def gf2_rank(M)->int:
    A=(np.asarray(M,dtype=np.uint8)&1).copy(); m,n=A.shape; r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if A[i,c]: piv=i; break
        if piv is None: continue
        if piv!=r: A[[r,piv]]=A[[piv,r]]
        for i in range(m):
            if i!=r and A[i,c]: A[i]^=A[r]
        r+=1
        if r==m: break
    return int(r)

def gf2_inv(M):
    A=(np.asarray(M,dtype=np.uint8)&1).copy(); n=A.shape[0]
    aug=np.concatenate([A,np.eye(n,dtype=np.uint8)],axis=1)
    r=0
    for c in range(n):
        piv=None
        for i in range(r,n):
            if aug[i,c]: piv=i; break
        if piv is None: raise ValueError('singular')
        if piv!=r: aug[[r,piv]]=aug[[piv,r]]
        for i in range(n):
            if i!=r and aug[i,c]: aug[i]^=aug[r]
        r+=1
    return aug[:,n:]&1

def gl3():
    mats=[]
    for mask in range(1<<9):
        M=bits_to_mat(mask)
        if gf2_rank(M)==3: mats.append(M)
    return mats

def quotient_project(a:int,pivot:int)->int:
    if a==0 or a==pivot: return 0
    h=pivot.bit_length()-1
    if (a>>h)&1: a ^= pivot
    low=a & ((1<<h)-1)
    high=(a>>(h+1))<<h
    return low|high

def quotient_lift(q:int,pivot:int)->int:
    h=pivot.bit_length()-1
    low=q & ((1<<h)-1)
    high=(q>>h)<<(h+1)
    return low|high

def apply_pair(P,QinvT,pivot,q):
    A=bits_to_mat(quotient_lift(q,pivot))
    B=(P.T @ A @ QinvT) & 1
    return quotient_project(mat_to_bits(B),pivot)

def orbit_hash(orbits):
    text=json.dumps(orbits,separators=(',',':'),sort_keys=True).encode()
    return hashlib.sha256(text).hexdigest()

def main():
    t0=time.time(); G=gl3(); out={'schema':'s0908_quotient_orbits_independent_v1','gl3_size':len(G),'pivots':{},'elapsed_sec':None}
    for name,pivot in PIVOTS.items():
        A=bits_to_mat(pivot); stab=[]
        for i,P in enumerate(G):
            for j,Q in enumerate(G):
                QinvT=gf2_inv(Q).T & 1
                B=(P.T @ A @ QinvT) & 1
                if mat_to_bits(B)==pivot:
                    stab.append((i,j,P,QinvT))
        # Check action maps nonzero quotient points bijectively.
        perms=[]; action_bad=0
        for i,j,P,QinvT in stab:
            images=[apply_pair(P,QinvT,pivot,q) for q in range(1,256)]
            if sorted(images)!=list(range(1,256)): action_bad+=1
            perms.append(images)
        seen=set(); orbits=[]
        for q in range(1,256):
            if q in seen: continue
            orb=sorted({perm[q-1] for perm in perms})
            # Close under group action in case single pass somehow missed; should not enlarge.
            changed=True; S=set(orb)
            while changed:
                changed=False
                for x in list(S):
                    for perm in perms:
                        y=perm[x-1]
                        if y not in S: S.add(y); changed=True
            orb=sorted(S); orbits.append(orb); seen.update(orb)
        orbits.sort(key=lambda o:(len(o),o[0]))
        reps=[o[0] for o in orbits]
        out['pivots'][name]={
            'pivot':pivot,
            'pivot_matrix_rank':gf2_rank(A),
            'stabilizer_size':len(stab),
            'action_bad_permutations':action_bad,
            'num_orbits':len(orbits),
            'orbit_sizes':[len(o) for o in orbits],
            'orbit_size_hist':dict(sorted(Counter(len(o) for o in orbits).items())),
            'representatives':reps,
            'orbits':orbits,
            'coverage_ok': sorted(sum((o for o in orbits), []))==list(range(1,256)),
            'orbit_hash': orbit_hash(orbits),
        }
    out['elapsed_sec']=time.time()-t0; OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps({k:{kk:v[kk] for kk in ['pivot','pivot_matrix_rank','stabilizer_size','num_orbits','orbit_size_hist','representatives','coverage_ok','orbit_hash']} for k,v in out['pivots'].items()},indent=2,sort_keys=True)); print('saved', OUT)
if __name__=='__main__': main()
