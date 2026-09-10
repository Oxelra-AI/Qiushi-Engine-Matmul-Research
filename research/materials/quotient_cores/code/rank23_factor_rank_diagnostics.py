#!/usr/bin/env python3
"""Factor-rank diagnostics and simple tensor symmetries for the verified rank-23 F2 scheme."""
from __future__ import annotations
import json, os, sys
from pathlib import Path
from collections import Counter
import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from extract_known_supports import parse_rank23_txt

SRC = Path("data/flip_cpd_inspect/src/khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt")
OUT = Path("data/wang_native/three_orbit_controls/rank23_factor_rank_diagnostics.json")

def bits_to_mat(mask:int)->np.ndarray:
    return np.array([[(mask>>(3*i+j))&1 for j in range(3)] for i in range(3)], dtype=np.uint8)

def mat_to_bits(M:np.ndarray)->int:
    M=np.asarray(M,dtype=np.uint8)&1; out=0
    for i in range(3):
        for j in range(3):
            if int(M[i,j])&1: out|=1<<(3*i+j)
    return out

def tr(mask:int)->int:
    return mat_to_bits(bits_to_mat(mask).T)

def gf2_rank(M:np.ndarray)->int:
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

def build_t333():
    T=np.zeros((9,9,9),dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3): T[3*i+j,3*j+k,3*i+k]^=1
    return T

def vec(mask,n=9): return np.array([(mask>>i)&1 for i in range(n)],dtype=np.uint8)
def recon(terms):
    T=np.zeros((9,9,9),dtype=np.uint8)
    for a,b,c in terms:
        T ^= (vec(a).reshape(9,1,1)*vec(b).reshape(1,9,1)*vec(c).reshape(1,1,9)).astype(np.uint8)
    return T

def diff(terms): return int(np.count_nonzero(recon(terms)!=build_t333()))

# Candidate known tensor automorphisms from trace cyclicity tr(A B C^T):
# Full transpose: (A,B,C)->(B^T,A^T,C^T) is the opposite multiplication swap.
# Cyclic variants need transposes; try all six permutations with optional transpose-all and record exact ones.
from itertools import permutations, product

def maybe_transform(term, perm, tflags):
    xs=list(term)
    ys=[]
    for idx,tf in zip(perm,tflags):
        y=xs[idx]
        if tf: y=tr(y)
        ys.append(y)
    return tuple(ys)

def main():
    terms=[tuple(map(int,t)) for t in parse_rank23_txt(SRC)]
    base_ok=diff(terms)==0
    ranks={slot:Counter() for slot in 'ABC'}
    rank3_terms={slot:[] for slot in 'ABC'}
    for i,t in enumerate(terms):
        for si,slot in enumerate('ABC'):
            r=gf2_rank(bits_to_mat(t[si])); ranks[slot][r]+=1
            if r==3: rank3_terms[slot].append({"term_index":i,"mask":t[si]})
    exact_sym=[]
    for perm in permutations([0,1,2]):
        for flags in product([0,1], repeat=3):
            t2=[maybe_transform(t,perm,flags) for t in terms]
            d=diff(t2)
            if d==0:
                exact_sym.append({"perm":perm,"transpose_flags":flags,"first_slot_rank_hist":dict(Counter(gf2_rank(bits_to_mat(x[0])) for x in t2))})
    out={"source":str(SRC),"base_verified":base_ok,"base_diff":diff(terms),"factor_rank_hist":{k:dict(v) for k,v in ranks.items()},"rank3_terms":rank3_terms,"exact_simple_permutation_transpose_symmetries":exact_sym}
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__': main()
