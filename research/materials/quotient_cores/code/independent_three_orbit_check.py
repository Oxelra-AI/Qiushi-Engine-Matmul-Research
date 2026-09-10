#!/usr/bin/env python3
"""analysis: independent check of peer three-orbit quotient details.

This does not import the peer research_record quotient script.  It checks two points:
1. For quotients by pivots of matrix rank 1,2,3, every quotient line (original
   2D subspace containing the pivot) has Wang n=19 capacity as reported.
2. For a multi-bit pivot the quotient map sends an original basis vector to a
   possibly multi-bit quotient vector, so its tensor slice must be XORed into
   every projected quotient coordinate.  The script records the resulting slice
   ranks and compares to a deliberately wrong lowest-bit-only projection.
"""
from __future__ import annotations
import json, sys, time, hashlib
from collections import Counter
from pathlib import Path
import numpy as np
ROOT=Path('research/research_record')
S04=Path('scripts')
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import rref_basis, pack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore
LUT_PATH=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
OUT=ROOT/'workspace/data/domain_dfs_soundness/independent_three_orbit_check.json'
PIVOTS={'rank1':1,'rank2':17,'rank3':273}

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()

def bits_to_mat(mask:int)->np.ndarray:
    return np.array([[(mask>>(3*i+j))&1 for j in range(3)] for i in range(3)],dtype=np.uint8)

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

def quotient_project(a:int,pivot:int)->int:
    if a==0 or a==pivot: return 0
    h=pivot.bit_length()-1
    if (a>>h)&1: a ^= pivot
    low=a & ((1<<h)-1)
    high=(a>>(h+1))<<h
    return low|high

def lift_q(q:int,pivot:int)->int:
    h=pivot.bit_length()-1
    low=q & ((1<<h)-1)
    high=(q>>h)<<(h+1)
    return low|high

def build_t333():
    T=np.zeros((9,9,9),dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j,3*j+k,3*i+k]^=1
    return T

def quotient_tensor_correct(pivot:int):
    T=build_t333(); Q=np.zeros((8,9,9),dtype=np.uint8); images=[]
    for ai in range(9):
        q=quotient_project(1<<ai,pivot)
        bits=[]; m=q
        while m:
            lb=m & -m; qi=lb.bit_length()-1; Q[qi]^=T[ai]; bits.append(qi); m^=lb
        images.append({'original_bit':ai,'q_mask':q,'q_bits':bits})
    return Q,images

def quotient_tensor_wrong_lowbit(pivot:int):
    T=build_t333(); Q=np.zeros((8,9,9),dtype=np.uint8)
    for ai in range(9):
        q=quotient_project(1<<ai,pivot)
        if q:
            lb=q & -q; Q[lb.bit_length()-1]^=T[ai]
    return Q

def line_caps(lut,pivot,target=19):
    cap_hist=Counter(); lb_hist=Counter(); lift_rank_hist=Counter(); repeat=[]
    missing=0
    for q in range(1,256):
        lift=lift_q(q,pivot)
        key=int(pack_basis(rref_basis((pivot,lift))))
        if key not in lut:
            missing+=1; continue
        lb=int(lut[key]); cap=target-lb; rk=gf2_rank(bits_to_mat(lift))
        cap_hist[cap]+=1; lb_hist[lb]+=1; lift_rank_hist[rk]+=1
        if cap>=2: repeat.append({'q':q,'lift':lift,'lb':lb,'cap':cap,'lift_rank':rk})
    return {'pivot':pivot,'target':target,'line_count':255-missing,'missing_lut':missing,'cap_hist':dict(sorted(cap_hist.items())),'lb_hist':dict(sorted(lb_hist.items())),'lift_rank_hist':dict(sorted(lift_rank_hist.items())),'all_cap_le_1':all(int(k)<=1 for k in cap_hist),'repeatable_count':len(repeat),'repeatable':repeat}

def main():
    t0=time.time(); lut,_=load_lut(LUT_PATH); out={'schema':'s0908_independent_three_orbit_check_v1','source_lut':str(LUT_PATH),'source_lut_sha256':sha(LUT_PATH),'line_caps_n19':{},'quotient_tensor_projection':{},'elapsed_sec':None}
    for name,pivot in PIVOTS.items():
        lc=line_caps(lut,pivot,19); out['line_caps_n19'][name]=lc
        Q,img=quotient_tensor_correct(pivot); Qbad=quotient_tensor_wrong_lowbit(pivot)
        out['quotient_tensor_projection'][name]={'pivot':pivot,'pivot_matrix_rank':gf2_rank(bits_to_mat(pivot)),'kernel_check':all((quotient_project(x,pivot)==0)==(x in (0,pivot)) for x in range(512)),'basis_images':img,'has_multibit_basis_image':any(len(r['q_bits'])>1 for r in img),'correct_slice_ranks':[gf2_rank(Q[i]) for i in range(8)],'wrong_lowbit_slice_ranks':[gf2_rank(Qbad[i]) for i in range(8)],'correct_vs_wrong_diff_entries':int(np.count_nonzero(Q^Qbad))}
    out['elapsed_sec']=time.time()-t0; OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
