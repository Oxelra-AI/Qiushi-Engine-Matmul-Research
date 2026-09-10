#!/usr/bin/env python3
"""Full Wang cap check for possible sets of repeated E11 quotient directions.

Line caps imply only six quotient directions may repeat and multiplicity is at
most 2.  This script checks every subset D of those six directions against all
E11 Wang rows for the partial doubled multiset 2*D, i.e. tests whether
2|D ∩ U| <= 19-LB(U) for every U.  It classifies which repeat patterns remain
possible before enumerating the remaining distinct support.
"""
from __future__ import annotations

import json, sys, itertools
from collections import Counter
from pathlib import Path

S04=Path("scripts")
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import rref_basis, unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT=Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUT=Path("data/wang_validation/e11_repeat_subset_fullcheck.json")
MASK9=(1<<9)-1; N=19; REPEATABLE=[1,2,3,4,32,36]

def contains_e11(k:int)->bool:
    d=k&0xF
    return d>0 and (((k>>(4+9*(d-1)))&MASK9)==1)

def key9_to_basis8(k:int):
    raw=[]
    for b in unpack_basis(k):
        if b==1: continue
        q=int(b)
        if q&1: q^=1
        q8=0
        for bit in range(1,9):
            if (q>>bit)&1: q8|=1<<(bit-1)
        if q8: raw.append(q8)
    return tuple(rref_basis(raw,n=8)) if raw else tuple()

def points_of_basis(basis):
    pts=set(); d=len(basis)
    for m in range(1,1<<d):
        v=0
        for i,b in enumerate(basis):
            if (m>>i)&1: v^=b
        if v: pts.add(v)
    return pts

def main():
    lut,_=load_lut(LUT)
    rows=[]
    for key,lb0 in lut.items():
        if not contains_e11(int(key)): continue
        cap=N-int(lb0)
        if cap>=N: continue
        pts=points_of_basis(key9_to_basis8(int(key)))
        rows.append((cap, pts, int(lb0), (int(key)&0xF)-1, int(key)))
    recs=[]
    for r in range(0,len(REPEATABLE)+1):
        for D in itertools.combinations(REPEATABLE,r):
            D=set(D); ok=True; worst=None; fail_head=[]
            for cap,pts,lb,dim,key in rows:
                occ=2*len(D & pts)
                margin=cap-occ
                if worst is None or margin < worst['margin']:
                    worst={'margin':margin,'cap':cap,'occ':occ,'lb':lb,'dim8':dim,'key9':key,'inside':sorted(D&pts)}
                if margin<0:
                    ok=False
                    if len(fail_head)<5: fail_head.append({'margin':margin,'cap':cap,'occ':occ,'lb':lb,'dim8':dim,'key9':key,'inside':sorted(D&pts)})
            recs.append({'D':sorted(D),'size':r,'possible_partial_double':ok,'worst':worst,'fail_head':fail_head})
    out={'status':'ok','repeatable_points':REPEATABLE,'records':recs,'possible_by_size':dict(sorted((str(k),v) for k,v in Counter((r['size'],r['possible_partial_double']) for r in recs).items())),'possible_sets':[r for r in recs if r['possible_partial_double']]}
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','possible_sets':out['possible_sets'],'possible_by_size':out['possible_by_size'],'out':str(OUT)},indent=2,sort_keys=True))
if __name__=='__main__': main()
