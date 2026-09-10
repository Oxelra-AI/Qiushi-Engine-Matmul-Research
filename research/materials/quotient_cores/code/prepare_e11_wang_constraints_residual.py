#!/usr/bin/env python3
"""Prepare binary E11 Wang constraints with repeated-direction preload.

A length-19 E11 core decomposition is a multiset of quotient A-directions.  The
line constraints show only six nonzero directions can have multiplicity two.
For a repeated subset D, write the multiset as a distinct support S plus one
extra copy of every p in D.  This script subtracts the extra occupancy
|D ∩ U| from every Wang cap and writes residual constraints for enumerating S.

The native DFS then enumerates distinct supports of size 19-|D| with all points
of D forced into S (handled by its prefix mode or by a branch runner).
"""
from __future__ import annotations

import argparse, json, struct, sys
from collections import Counter
from itertools import combinations
from pathlib import Path

S04=Path("scripts")
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import rref_basis, unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT=Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR=Path("data/wang_native/repeats")
MASK9=(1<<9)-1; N=19; MAGIC=b"E11WANG1"
REPEATABLE=[1,2,3,4,32,36]

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

def words_from_basis8(basis):
    words=[0,0,0,0]
    d=len(basis)
    for m in range(1,1<<d):
        v=0
        for i,b in enumerate(basis):
            if (m>>i)&1: v^=b
        if v: words[v>>6] |= 1 << (v&63)
    return tuple(words)

def bit(words,p): return (words[p>>6]>>(p&63))&1

def write_bin(path, records):
    with open(path,'wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I', len(records)))
        for cap,dim,words in records:
            f.write(struct.pack('<BBHQQQQ', cap, dim, 0, *words))

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--max-cap',type=int,default=5)
    ap.add_argument('--max-repeat-size',type=int,default=4)
    ap.add_argument('--repeat-subset',default=None,help='comma-separated repeated points; if omitted build all nonempty subsets up to max size')
    ap.add_argument('--outdir',type=Path,default=OUTDIR)
    args=ap.parse_args(); args.outdir.mkdir(parents=True,exist_ok=True)
    if args.repeat_subset is not None:
        subsets=[tuple(int(x) for x in args.repeat_subset.split(',') if x)]
    else:
        subsets=[]
        for k in range(1,args.max_repeat_size+1):
            subsets.extend(combinations(REPEATABLE,k))
    lut,_=load_lut(LUT)
    base=[]
    for key,lb0 in lut.items():
        if not contains_e11(int(key)): continue
        lb=int(lb0); cap=N-lb
        if cap<0 or cap>args.max_cap or cap>=N: continue
        b=key9_to_basis8(int(key)); words=words_from_basis8(b)
        base.append((cap,len(b),words,lb,int(key)))
    summaries=[]
    for sub in subsets:
        sub=tuple(sorted(set(sub)))
        bad=False; rec=[]; cap_hist=Counter(); neg_head=[]
        for cap,dim,words,lb,key in base:
            extra=sum(bit(words,p) for p in sub)
            rcap=cap-extra
            if rcap<0:
                bad=True
                if len(neg_head)<10: neg_head.append({'key9':key,'dim8':dim,'lb':lb,'base_cap':cap,'extra':extra,'repeat_subset':sub})
            elif rcap <= args.max_cap:
                rec.append((rcap,dim,words)); cap_hist[rcap]+=1
        name='rep_'+'_'.join(map(str,sub))
        bin_path=args.outdir/f'e11_wang_cap{args.max_cap}_{name}.bin'
        if not bad: write_bin(bin_path, rec)
        summaries.append({'repeat_subset':list(sub),'repeat_size':len(sub),'target_distinct_support_size':N-len(sub),'valid_preload':not bad,'negative_head':neg_head,'row_count_written':len(rec) if not bad else 0,'residual_cap_hist':dict(sorted((int(k),int(v)) for k,v in cap_hist.items())),'binary_path':str(bin_path) if not bad else None})
    out={'status':'ok','max_cap':args.max_cap,'base_row_count':len(base),'repeatable_points':REPEATABLE,'subset_count':len(subsets),'summaries':summaries}
    path=args.outdir/f'residual_cap{args.max_cap}_manifest.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','base_row_count':len(base),'subset_count':len(subsets),'valid_subsets':sum(1 for s in summaries if s['valid_preload']),'invalid_subsets':sum(1 for s in summaries if not s['valid_preload']),'manifest':str(path),'valid_head':[s for s in summaries if s['valid_preload']][:10]},indent=2,sort_keys=True))

if __name__=='__main__': main()
