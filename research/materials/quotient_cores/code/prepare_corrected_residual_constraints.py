#!/usr/bin/env python3
"""analysis: prepare corrected residual Wang rows for repeated E11 directions.

For a 19-term A-multiset with doubled direction set D (multiplicity exactly 2 on
D, exactly 1 on S\D, 0 outside S), write the multiset as S + extra(D).  The
original Wang row |M∩U| <= cap becomes

    |S∩U| <= cap - |D∩U| .

The distinct support S has size 19-|D| and must contain D.  Therefore D is
immediately impossible if |D∩U| > cap-|D∩U| for some row U, i.e. if
2|D∩U| > cap.

Important repair relative to the peer residual preparation: the source rows must
be ALL E11 Wang rows before subtracting the extra copy, not only rows with base
cap<=max_cap, because a row with base cap 6,7,8,... can become a small residual
cap after the repeated directions are subtracted.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, struct, sys, time
from collections import Counter
from pathlib import Path

S04=Path('scripts')
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import rref_basis, unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
OUT=Path('data/domain_dfs_soundness/repeats_corrected')
N=19; MASK9=(1<<9)-1; MAGIC=b'E11WANG1'; REPEATABLE=[1,2,3,4,32,36]

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
    w=[0,0,0,0]
    for m in range(1,1<<len(basis)):
        v=0
        for i,b in enumerate(basis):
            if (m>>i)&1: v^=b
        if v: w[v>>6] |= 1 << (v&63)
    return tuple(w)

def bit(words,p): return (words[p>>6]>>(p&63))&1

def write_bin(path:Path, rows):
    blob=bytearray(); blob.extend(MAGIC); blob.extend(struct.pack('<I',len(rows)))
    for cap,dim,words in rows:
        blob.extend(struct.pack('<BBHQQQQ', int(cap), int(dim), 0, *[int(x) for x in words]))
    path.write_bytes(bytes(blob)); return hashlib.sha256(bytes(blob)).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--max-residual-cap',type=int,default=5)
    ap.add_argument('--outdir',type=Path,default=OUT)
    args=ap.parse_args(); args.outdir.mkdir(parents=True,exist_ok=True)
    t0=time.time()
    lut,_=load_lut(LUT)
    all_rows=[]; base_cap_hist=Counter(); dim_hist=Counter(); lb_hist=Counter()
    for key,lb0 in lut.items():
        key=int(key); lb=int(lb0)
        if not contains_e11(key): continue
        cap=N-lb
        if cap<0 or cap>=N: continue
        basis=key9_to_basis8(key); words=words_from_basis8(basis); dim=len(basis)
        all_rows.append((cap,dim,words,lb,key))
        base_cap_hist[cap]+=1; dim_hist[dim]+=1; lb_hist[lb]+=1
    summaries=[]; possible=[]
    for r in range(1,len(REPEATABLE)+1):
        for D0 in itertools.combinations(REPEATABLE,r):
            D=tuple(D0); invalid_extra=False; invalid_preload=False; neg_head=[]; preload_fail_head=[]; rec=[]; hist=Counter(); newly_small=0; worst=None
            for cap,dim,words,lb,key in all_rows:
                extra=sum(bit(words,p) for p in D)
                rcap=cap-extra
                margin=rcap-extra
                if worst is None or margin < worst['preload_margin']:
                    worst={'base_cap':cap,'residual_cap':rcap,'extra_occ':extra,'preload_margin':margin,'lb':lb,'dim8':dim,'key9':key,'inside':[p for p in D if bit(words,p)]}
                if rcap<0:
                    invalid_extra=True
                    if len(neg_head)<10: neg_head.append({'base_cap':cap,'extra_occ':extra,'lb':lb,'dim8':dim,'key9':key,'inside':[p for p in D if bit(words,p)]})
                    continue
                if extra>rcap:
                    invalid_preload=True
                    if len(preload_fail_head)<10: preload_fail_head.append({'base_cap':cap,'residual_cap':rcap,'extra_occ':extra,'lb':lb,'dim8':dim,'key9':key,'inside':[p for p in D if bit(words,p)]})
                if rcap <= args.max_residual_cap:
                    rec.append((rcap,dim,words)); hist[rcap]+=1
                    if cap > args.max_residual_cap:
                        newly_small += 1
            status = 'possible' if (not invalid_extra and not invalid_preload) else ('negative_residual' if invalid_extra else 'forced_D_violates_residual')
            name='rep_'+'_'.join(map(str,D))
            bin_path=args.outdir/f'e11_wang_rescap{args.max_residual_cap}_{name}.bin'
            sha=None
            if status=='possible': sha=write_bin(bin_path, rec)
            entry={'D':list(D),'repeat_size':len(D),'status':status,'target_distinct_support_size':N-len(D),'force_points':list(D),
                   'row_count_written':len(rec) if status=='possible' else 0,'residual_cap_hist':dict(sorted((int(k),int(v)) for k,v in hist.items())),
                   'rows_newly_small_after_extra':newly_small if status=='possible' else 0,
                   'binary_path':str(bin_path) if status=='possible' else None,'binary_sha256':sha,'worst':worst,'negative_head':neg_head,'preload_fail_head':preload_fail_head}
            summaries.append(entry)
            if status=='possible': possible.append(entry)
    out={'schema':'s0908_corrected_residual_constraints_v1','status':'ok','source_lut':str(LUT),'max_residual_cap':args.max_residual_cap,
         'repeatable_points':REPEATABLE,'all_e11_row_count':len(all_rows),'base_cap_hist_all':dict(sorted((int(k),int(v)) for k,v in base_cap_hist.items())),
         'dim_hist_all':dict(sorted((int(k),int(v)) for k,v in dim_hist.items())),'lb_hist_all':dict(sorted((int(k),int(v)) for k,v in lb_hist.items())),
         'summary_by_size_status':{str(k):int(v) for k,v in Counter((e['repeat_size'],e['status']) for e in summaries).items()},
         'possible_count':len(possible),'possible':possible,'summaries':summaries,'elapsed_sec':time.time()-t0,
         'meaning':'Correct repeat residual rows start from all E11 Wang rows, subtract only the extra copy of D, force D once in S, and include rows whose residual cap is small.'}
    path=args.outdir/f'corrected_residual_cap{args.max_residual_cap}_manifest.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('summaries','possible')} | {'possible_head':possible[:20], 'manifest':str(path)}, indent=2, sort_keys=True))

if __name__=='__main__': main()
