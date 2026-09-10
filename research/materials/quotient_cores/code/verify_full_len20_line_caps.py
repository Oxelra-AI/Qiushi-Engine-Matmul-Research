#!/usr/bin/env python3
"""Verify full T333 length-20 one-dimensional Wang caps exclude repeats.

For every nonzero A-functional p in F2^9, the 1-dimensional subspace <p>
has Wang LB 19 in the inherited LUT, hence cap20 = 1. Therefore any
Wang-admissible length-20 A-multiset has multiplicity at most one for every p.
This justifies using distinct-support enumeration for the full length-20 target,
provided the LUT-to-Wang semantics is independently accepted.
"""
from __future__ import annotations
import json, sys
from collections import Counter
from pathlib import Path
S04=Path("scripts")
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import rref_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore
LUT=Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUT=Path("data/wang_validation/full_len20_line_caps.json")

def pack_basis(basis):
    # Reverse of unpack convention: low 4 bits dimension, then 9-bit rows.
    key=len(basis)
    for i,b in enumerate(basis): key |= int(b) << (4+9*i)
    return key

def matrix_rank_3x3(a:int)->int:
    rows=[0,0,0]
    for idx in range(9):
        if (a>>idx)&1:
            i,j=divmod(idx,3); rows[i]|=1<<j
    basis=[0]*3; r=0
    for x0 in rows:
        x=x0
        while x:
            p=x.bit_length()-1
            if basis[p]: x^=basis[p]
            else: basis[p]=x; r+=1; break
    return r

def main():
    lut,_=load_lut(LUT)
    records=[]; hist=Counter(); missing=[]
    for p in range(1,512):
        b=tuple(rref_basis([p], n=9))
        key=pack_basis(b)
        lb=lut.get(key)
        if lb is None:
            missing.append({"p":p,"basis":list(b),"key":key}); continue
        lb=int(lb); cap20=20-lb
        hist[(lb,cap20,matrix_rank_3x3(p))]+=1
        if lb!=19 or cap20!=1:
            records.append({"p":p,"basis":list(b),"key":key,"lb":lb,"cap20":cap20,"matrix_rank":matrix_rank_3x3(p)})
    out={"status":"ok" if not missing and not records else "problem","source_lut":str(LUT),"checked_points":511,"hist_lb_cap_rank":{"%s,%s,%s"%k:v for k,v in sorted(hist.items())},"exceptions":records,"missing":missing,"all_lines_lb19_cap1":not missing and not records,"implication":"At length 20, occupancy of each line <p> is <=1, so repeated A-functionals are impossible for a Wang-admissible full support."}
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
