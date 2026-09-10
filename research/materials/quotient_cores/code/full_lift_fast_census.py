#!/usr/bin/env python3
"""Fast census of full rank-20 lift-bit constraints from WANG512 rows.

Uses the peer-generated full_tensor WANG512 cap<=5 dim<=3 row binary for length 20.
For a fixed pivot q, each full row W yields constraints on quotient point p and
lift bit eps in a_i=s(p)+eps q. Rows containing q and dim<=3 reproduce low-cap
quotient occupation rows; rows not containing q impose extra eps constraints.
"""
from __future__ import annotations
import json, struct, time, hashlib
from collections import Counter
from pathlib import Path

ROOT=Path('research/research_record')
FULL=Path('data/wang_native/full_tensor/full_wang512_cap5_len20_all_dim3.bin')
OUT=ROOT/'workspace/data/quotient_lift/full_lift_fast_census.json'
PIVOTS={'rank2':17,'rank3':273}

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()

def bit(words,p): return (words[p>>6]>>(p&63))&1

def lift0(p,pivot):
    h=pivot.bit_length()-1
    low=p & ((1<<h)-1)
    high=(p>>h)<<(h+1)
    return low|high

def main():
    t0=time.time()
    pivot_maps={}
    for name,pivot in PIVOTS.items():
        arr=[]
        for p in range(1,256):
            a0=lift0(p,pivot); arr.append((p,a0,a0^pivot))
        pivot_maps[name]=arr
    out={'schema':'s0908_full_lift_fast_census_v1','source_full_wang512':str(FULL),'source_sha256':sha(FULL),'row_scope':'length20 cap<=5 dim<=3 from full tensor Wang LUT','pivots':{},'elapsed_sec':None}
    for name,pivot in PIVOTS.items():
        out['pivots'][name]={'pivot':pivot,'rows':0,'contains_q':0,'not_contains_q':0,'quotient_like_contains_q':0,'extra_not_containing_nontrivial':0,'cap_rhs_hist':Counter(),'pattern_hist':Counter(),'strong_rows_head':[]}
    with FULL.open('rb') as f:
        magic=f.read(8); assert magic==b'WANG512\x01', magic
        n=struct.unpack('<I',f.read(4))[0]
        for idx in range(n):
            cap,dim,res=struct.unpack('<BBH',f.read(4)); words=list(struct.unpack('<8Q',f.read(64)))
            for name,pivot in PIVOTS.items():
                rec=out['pivots'][name]; rec['rows']+=1
                cq=bool(bit(words,pivot)); rhs=cap-(1 if cq else 0)
                only0=only1=both=0
                for p,a0,a1 in pivot_maps[name]:
                    m0=bool(bit(words,a0)); m1=bool(bit(words,a1))
                    if m0 and m1: both+=1
                    elif m0: only0+=1
                    elif m1: only1+=1
                if cq: rec['contains_q']+=1
                else: rec['not_contains_q']+=1
                if cq and only0==0 and only1==0: rec['quotient_like_contains_q']+=1
                if (not cq) and (only0 or only1 or both): rec['extra_not_containing_nontrivial']+=1
                rec['cap_rhs_hist'][(cq,rhs)] += 1
                rec['pattern_hist'][(cq,rhs,only0,only1,both)] += 1
                if (not cq) and rhs>=0 and (only0+only1+both)>0:
                    score=only0+only1+2*both-rhs
                    if rhs<=2 or score>=10 or both>0:
                        strong={'row_index':idx,'cap20':cap,'rhs_after_q':rhs,'dim':dim,'only0':only0,'only1':only1,'both':both,'score':score}
                        head=rec['strong_rows_head']; head.append(strong); head.sort(key=lambda r:(r['rhs_after_q'],-r['score'],-r['both'],r['row_index']))
                        if len(head)>30: head.pop()
    # Convert counters to JSONable and add common heads.
    for name,rec in out['pivots'].items():
        rec['cap_rhs_hist']={str(k):v for k,v in sorted(rec['cap_rhs_hist'].items(),key=lambda kv:(kv[0][0],kv[0][1]))}
        common=rec['pattern_hist'].most_common(25)
        rec['pattern_hist_head']=[{'contains_q':k[0],'rhs_after_q':k[1],'only0':k[2],'only1':k[3],'both':k[4],'rows':v} for k,v in common]
        rec['pattern_count']=len(rec['pattern_hist'])
        del rec['pattern_hist']
    out['elapsed_sec']=time.time()-t0; OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({name:{k:rec[k] for k in ['pivot','rows','contains_q','not_contains_q','quotient_like_contains_q','extra_not_containing_nontrivial','pattern_count']} for name,rec in out['pivots'].items()},indent=2,sort_keys=True)); print('saved',OUT)
if __name__=='__main__': main()
