#!/usr/bin/env python3
"""Block-spread defect/leak analysis for full 3x3 matrix multiplication pools over F2.

The analysis E11 slice argument applies to the full 9-slice tensor with the same
block convention T[3i+j,3j+k,3i+k]=1.  This script verifies the slice-level
excess/leak budget on public/local rank-23 and rank-22/23 pool files when they
are exact full decompositions in the current convention.  It is a calibration for
full rank-20 lower-bound ideas, not a proof.
"""
from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

import numpy as np

GROUP=[7,56,448]


def slice_block_full(a:int)->Tuple[int,int]:
    return a%3, a//3


def build_t333():
    T=np.zeros((9,9,9),dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j,3*j+k,3*i+k]=1
    return T


def rank_int(rows: Iterable[int])->int:
    basis={}; r=0
    for x0 in rows:
        x=int(x0)
        while x:
            p=x.bit_length()-1
            if p in basis: x^=basis[p]
            else:
                basis[p]=x; r+=1; break
    return r


def extract_group(mask:int,g:int)->int:
    return (int(mask)>>(3*g))&7


def project_outside(mask:int,g:int)->int:
    out=0; pos=0
    for h in range(3):
        if h==g: continue
        bits=extract_group(mask,h)
        for k in range(3):
            if (bits>>k)&1: out|=1<<pos
            pos+=1
    return out


def reconstruct(row):
    R=len(row)//3
    rec=np.zeros((9,9,9),dtype=np.uint8)
    for t in range(R):
        u=int(row[3*t]); v=int(row[3*t+1]); w=int(row[3*t+2])
        for a in range(9):
            if (u>>a)&1:
                for b in range(9):
                    if (v>>b)&1:
                        for c in range(9):
                            if (w>>c)&1:
                                rec[a,b,c]^=1
    return rec


def analyze_row(row):
    R=len(row)//3
    terms=[(int(row[3*t]),int(row[3*t+1]),int(row[3*t+2])) for t in range(R)]
    records=[]; fails=[]
    for a in range(9):
        j,i=slice_block_full(a)
        active=[t for t,(u,_v,_w) in enumerate(terms) if (u>>a)&1]
        c=len(active)
        v_leak=[project_outside(terms[t][1],j) for t in active]
        w_leak=[project_outside(terms[t][2],i) for t in active]
        lv=rank_int(v_leak); lw=rank_int(w_leak)
        ok=(c>=3 and lv+lw<=c-3)
        rec={'slice':a,'block':[j,i],'c':c,'leak_v_rank':lv,'leak_w_rank':lw,'leak_sum':lv+lw,'budget':c-3,'ok':ok,'v_pure':lv==0,'w_pure':lw==0}
        records.append(rec)
        if not ok:
            fails.append(rec)
    return {'rank':R,'caps':[r['c'] for r in records],'total_weight':sum(r['c'] for r in records),'records':records,'failures':fails,'all_ok':not fails}


def analyze_pool(path:Path,max_rows:int=1000,brent_spot:int=10):
    arr=np.load(path)
    rows=arr[:max_rows]
    T=build_t333()
    h=collections.Counter(); wh=collections.Counter(); failures=[]; brent_fail=[]
    for idx,row in enumerate(rows):
        an=analyze_row(row)
        if idx<brent_spot:
            diff=int(np.sum(reconstruct(row)^T))
            if diff: brent_fail.append({'row':idx,'diff':diff})
        if not an['all_ok']:
            failures.append({'row':idx,'failures':an['failures'],'caps':an['caps']})
        wh[an['total_weight']]+=1
        for r in an['records']:
            h[(r['c'],r['leak_v_rank'],r['leak_w_rank'])]+=1
    return {'path':str(path),'shape':list(arr.shape),'rows_analyzed':len(rows),'brent_spot_checked':min(brent_spot,len(rows)),'brent_failures':brent_fail,'all_defect_ok':not failures,'failure_head':failures[:5],'total_weight_hist':{str(k):int(v) for k,v in sorted(wh.items())},'capacity_leak_hist':{str(k):int(v) for k,v in sorted(h.items(),key=lambda kv:str(kv[0]))}}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--out',type=Path,default=Path('data/block_spread/full_tensor_defect_leak_analysis.json'))
    ap.add_argument('--max-rows',type=int,default=1000)
    args=ap.parse_args()
    paths=[
        Path('data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank22a.npy'),
        Path('data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank23a.npy'),
    ]
    results=[]
    for p in paths:
        if p.exists():
            results.append(analyze_pool(p,args.max_rows))
    out={'purpose':'full-tensor block-spread defect/leak calibration on available pool files','results':results,'interpretation':'If Brent spot-check fails, the file is not a full T333 pool in this convention and only the local row analysis is diagnostic. Exact full rank-20 use requires a full-tensor encoder/search.'}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(args.out),'results':[{'path':r['path'],'shape':r['shape'],'brent_failures':r['brent_failures'],'all_defect_ok':r['all_defect_ok'],'weight_head':list(r['total_weight_hist'].items())[:8]} for r in results]},indent=2,sort_keys=True))

if __name__=='__main__': main()
