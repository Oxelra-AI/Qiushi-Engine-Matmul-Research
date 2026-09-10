#!/usr/bin/env python3
"""analysis: corrected graph-family double-counting bounds in all quotient dimensions.

Uses the canonical analysis quotient convention (delete highest pivot bit) and
Wang's complete 9D LUT directly.  For every quotient subspace U<=F2^8,
compares the graph-family averaging capacity
    floor(sum_alpha cap20(graph(alpha))/2^(dim U-1))
with the ordinary quotient capacity cap19(<pivot, section(U)>)-1 = 19-L.
Exports genuinely stronger rows with dc_cap <= max_export_cap, in native bit-p
E11WANG1 format.
"""
from __future__ import annotations
import argparse, hashlib, json, struct, sys, time
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
OUTDIR=ROOT/'workspace/data/quotient_lift'; OUTDIR.mkdir(parents=True,exist_ok=True)
PIVOTS={'rank2':17,'rank3':273}

def sha_file(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()

def sha_bytes(b:bytes)->str: return hashlib.sha256(b).hexdigest()

def section_lift(qpoint:int,pivot:int)->int:
    h=pivot.bit_length()-1
    return (qpoint & ((1<<h)-1)) | ((qpoint>>h)<<(h+1))

def rref_subspace_bases(n:int,d:int):
    if d==0:
        yield tuple(); return
    for pivs_asc in combinations(range(n),d):
        pivs=tuple(sorted(pivs_asc,reverse=True))
        free_per=[[j for j in range(p) if j not in pivs] for p in pivs]
        total=sum(len(f) for f in free_per)
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
    for p in pts: m |= 1<<int(p)  # native bit-p convention
    return m

def lut_lb(lut,basis9:Sequence[int])->int:
    return int(lut[int(pack_basis(rref_basis(basis9,n=9)))])

def write_rows(path:Path,rows:list[tuple[int,int,int]])->str:
    data=bytearray(); data.extend(b'E11WANG1'); data.extend(struct.pack('<I',len(rows)))
    for cap,dim,mask in rows:
        data.extend(struct.pack('<BBH',cap,dim,0))
        for i in range(4): data.extend(struct.pack('<Q',(mask>>(64*i))&((1<<64)-1)))
    path.write_bytes(bytes(data)); return sha_bytes(bytes(data))

def analyze(name,pivot,lut,max_export_cap:int):
    t0=time.time(); rows=[]; rec={'pivot':pivot,'dims':{},'improvement_count_all':0,'export_count':0,'dc_cap_hist':Counter(),'qcap_hist':Counter(),'improve_by_dim':Counter(),'export_by_cap':Counter(),'export_by_dim':Counter(),'examples':[]}
    total=0
    for d in range(1,9):
        dim_count=0; dim_imp=0; dim_export=0
        for ubasis in rref_subspace_bases(8,d):
            dim_count+=1; total+=1
            pts=points_of_basis(ubasis); k=len(pts); mask=mask_from_points(pts)
            lifts=[section_lift(u,pivot) for u in ubasis]
            qcap=19-lut_lb(lut,[pivot]+lifts)
            rec['qcap_hist'][qcap]+=1
            capsum=0; graph_caps=[]
            for alpha in range(1<<d):
                gb=[]
                for i,u in enumerate(ubasis):
                    v=section_lift(u,pivot)
                    if (alpha>>i)&1: v^=pivot
                    gb.append(v)
                cap=20-lut_lb(lut,gb)
                capsum+=cap
                if len(rec['examples'])<5: graph_caps.append(cap)
            dc=min(k,capsum//(1<<(d-1)))
            rec['dc_cap_hist'][dc]+=1
            if dc<qcap and dc<k:
                rec['improvement_count_all']+=1; rec['improve_by_dim'][d]+=1; dim_imp+=1
                if dc<=max_export_cap:
                    rows.append((dc,d,mask)); rec['export_count']+=1; rec['export_by_cap'][dc]+=1; rec['export_by_dim'][d]+=1; dim_export+=1
                    if len(rec['examples'])<30:
                        rec['examples'].append({'dim':d,'k':k,'dc_cap':dc,'qcap':qcap,'cap_sum':capsum,'graph_caps_head':graph_caps,'points_head':pts[:20]})
        rec['dims'][str(d)]={'subspaces':dim_count,'improvements':dim_imp,'exports':dim_export}
        print(f"{name} dim {d}: subspaces={dim_count}, improvements={dim_imp}, exports={dim_export}, elapsed={time.time()-t0:.1f}s",flush=True)
    # dedup rows by mask/cap tightest
    best={}
    for cap,dim,mask in rows:
        if mask not in best or cap<best[mask][0]: best[mask]=(cap,dim)
    out_rows=sorted([(cap,dim,mask) for mask,(cap,dim) in best.items()],key=lambda r:(r[0],r[1],r[2]))
    bpath=OUTDIR/f'{name}_dc_all_dims_rows_cap{max_export_cap}.bin'
    bsha=write_rows(bpath,out_rows)
    for k in ['dc_cap_hist','qcap_hist','improve_by_dim','export_by_cap','export_by_dim']:
        rec[k]={str(a):int(b) for a,b in sorted(rec[k].items())}
    rec.update({'tested_subspaces':total,'dedup_export_rows':len(out_rows),'binary_path':str(bpath),'binary_sha256':bsha,'elapsed_sec':time.time()-t0})
    return rec

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--max-export-cap',type=int,default=5); args=ap.parse_args()
    t0=time.time(); print('Loading LUT...',flush=True); lut,meta=load_lut(LUT_PATH); print(f'LUT entries {len(lut)}',flush=True)
    out={'schema':'s0908_dc_all_dims_v1','source_lut':str(LUT_PATH),'source_lut_sha256':sha_file(LUT_PATH),'lut_coverage_ok':meta.get('coverage_ok'),'max_export_cap':args.max_export_cap,'pivots':{}}
    for name,pivot in PIVOTS.items():
        print(f'\n=== {name} pivot={pivot} ===',flush=True); out['pivots'][name]=analyze(name,pivot,lut,args.max_export_cap)
    out['elapsed_sec']=time.time()-t0
    op=OUTDIR/'dc_all_dims.json'; op.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(f'Saved {op} in {out["elapsed_sec"]:.1f}s',flush=True)
if __name__=='__main__': main()
