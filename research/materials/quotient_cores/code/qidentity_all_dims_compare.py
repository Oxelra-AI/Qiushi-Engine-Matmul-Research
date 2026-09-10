#!/usr/bin/env python3
"""analysis: rowwise all-dimensional q-containing identity check.

For each pivot q and each quotient subspace U<=F2^8, compute the ordinary
q-containing full-space capacity 19-L(<q,s(U)>).  Every case with cap<=5 should
appear in the existing quotient E11WANG1 binary with the same native bit-p mask
and cap.  This is the all-dimension rowwise version of the analysis dim<=3 check.
"""
from __future__ import annotations
import hashlib, json, struct, sys, time
from collections import Counter
from itertools import combinations
from pathlib import Path
from typing import Iterable, Sequence
ROOT=Path('research/research_record')
S04=Path('scripts')
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import rref_basis, pack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore
LUT_PATH=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
OUT=ROOT/'workspace/data/quotient_lift/qidentity_all_dims_compare.json'
PIVOTS={'rank2':17,'rank3':273}
QBINS={'rank2':ROOT/'workspace/data/quotient_dfs/rank2_cap5_n19.bin','rank3':ROOT/'workspace/data/quotient_dfs/rank3_cap5_n19.bin'}

def sha(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()

def section_lift(qpoint:int,pivot:int)->int:
    h=pivot.bit_length()-1
    return (qpoint & ((1<<h)-1)) | ((qpoint>>h)<<(h+1))

def rref_subspace_bases(n:int,d:int):
    if d==0: yield tuple(); return
    for pivs_asc in combinations(range(n),d):
        pivs=tuple(sorted(pivs_asc,reverse=True)); free_per=[[j for j in range(p) if j not in pivs] for p in pivs]; total=sum(len(f) for f in free_per)
        for a in range(1<<total):
            rows=[]; bit=0
            for p,free in zip(pivs,free_per):
                row=1<<p
                for j in free:
                    if (a>>bit)&1: row|=1<<j
                    bit+=1
                rows.append(row)
            yield tuple(rows)

def points_of_basis(basis:Sequence[int])->list[int]:
    pts=[]; d=len(basis)
    for m in range(1,1<<d):
        v=0
        for i,b in enumerate(basis):
            if (m>>i)&1: v^=int(b)
        pts.append(v)
    return sorted(pts)

def mask_from_points(pts:Iterable[int])->int:
    m=0
    for p in pts: m|=1<<int(p)
    return m

def load_best(path:Path):
    best={}; rows=0; cap_hist=Counter(); dim_hist=Counter()
    with path.open('rb') as f:
        assert f.read(8)==b'E11WANG1'; n=struct.unpack('<I',f.read(4))[0]
        for _ in range(n):
            cap=struct.unpack('<B',f.read(1))[0]; dim=struct.unpack('<B',f.read(1))[0]; f.read(2); words=struct.unpack('<4Q',f.read(32)); mask=0
            for i,w in enumerate(words): mask|=int(w)<<(64*i)
            rows+=1; cap_hist[cap]+=1; dim_hist[dim]+=1
            if mask not in best or cap<best[mask]: best[mask]=cap
    return rows,best,cap_hist,dim_hist

def lut_lb(lut,basis): return int(lut[int(pack_basis(rref_basis(basis,n=9)))])

def main():
    t0=time.time(); print('Loading LUT...',flush=True); lut,meta=load_lut(LUT_PATH); out={'schema':'s0908_qidentity_all_dims_compare_v1','source_lut':str(LUT_PATH),'source_lut_sha256':sha(LUT_PATH),'lut_coverage_ok':meta.get('coverage_ok'),'pivots':{}}
    for name,pivot in PIVOTS.items():
        print(f'\n=== {name} ===',flush=True); rows,best,bin_cap_hist,bin_dim_hist=load_best(QBINS[name])
        tested=0; cap_le5=0; missing=0; mismatch=0; extra_masks=set(best); cap_hist=Counter(); dim_hist=Counter(); head=[]
        for d in range(1,9):
            for ubasis in rref_subspace_bases(8,d):
                tested+=1; mask=mask_from_points(points_of_basis(ubasis)); qcap=19-lut_lb(lut,[pivot]+[section_lift(u,pivot) for u in ubasis]); cap_hist[qcap]+=1
                if qcap<=5:
                    cap_le5+=1; dim_hist[d]+=1; got=best.get(mask)
                    if got is None:
                        missing+=1
                        if len(head)<20: head.append({'kind':'missing','dim':d,'qcap':qcap,'points_head':points_of_basis(ubasis)[:20]})
                    elif got!=qcap:
                        mismatch+=1
                        if len(head)<20: head.append({'kind':'cap_mismatch','dim':d,'qcap':qcap,'binary_cap':got,'points_head':points_of_basis(ubasis)[:20]})
                    extra_masks.discard(mask)
        out['pivots'][name]={'pivot':pivot,'quotient_binary':str(QBINS[name]),'quotient_binary_sha256':sha(QBINS[name]),'binary_rows':rows,'binary_distinct_masks':len(best),'tested_quotient_subspaces':tested,'reconstructed_cap_le5_rows':cap_le5,'missing':missing,'cap_mismatch':mismatch,'extra_binary_masks_not_reconstructed':len(extra_masks),'cap_hist_all':{str(k):int(v) for k,v in sorted(cap_hist.items())},'dim_hist_cap_le5':{str(k):int(v) for k,v in sorted(dim_hist.items())},'binary_cap_hist':{str(k):int(v) for k,v in sorted(bin_cap_hist.items())},'binary_dim_hist':{str(k):int(v) for k,v in sorted(bin_dim_hist.items())},'problem_head':head}
        print(json.dumps(out['pivots'][name],indent=2,sort_keys=True)[:2000],flush=True)
    out['elapsed_sec']=time.time()-t0; OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('saved',OUT,flush=True)
if __name__=='__main__': main()
