#!/usr/bin/env python3
"""Export focused E11WANG1 pair-row binaries from analysis mining logs.

The analysis pair-propagation DFS forms every unordered pair of the supplied
pair rows, so this script deliberately exports small, evidence-selected row
sets instead of whole cap-7 files.  Selection sources are the actual Wang rows
violated by branch-specific CEGAR supports.  Rows are copied byte-for-byte from
the corrected E11WANG1 all-row binary and written in the same format.
"""
from __future__ import annotations
import argparse, hashlib, json, struct
from collections import Counter
from pathlib import Path
MAGIC=b'E11WANG1'; REC='<BBHQQQQ'; RECSZ=struct.calcsize(REC)

def sha(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''):
            h.update(c)
    return h.hexdigest()

def load_raw_rows(path:Path):
    d=path.read_bytes(); assert d[:8]==MAGIC, (path,d[:8])
    n=struct.unpack('<I',d[8:12])[0]
    assert len(d)==12+n*RECSZ, (len(d),12+n*RECSZ)
    rows=[]
    for idx in range(n):
        off=12+idx*RECSZ
        rec=d[off:off+RECSZ]
        cap,dim,pad,w0,w1,w2,w3=struct.unpack(REC,rec)
        mask=int(w0)|(int(w1)<<64)|(int(w2)<<128)|(int(w3)<<192)
        rows.append({'idx':idx,'cap':int(cap),'dim':int(dim),'popcount':mask.bit_count(),'rec':rec})
    return rows

def write_rows(path:Path, recs:list[bytes]):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I',len(recs)))
        for r in recs: f.write(r)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--mining',type=Path,required=True)
    ap.add_argument('--all-rows',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--max-rows',type=int,default=128)
    ap.add_argument('--allowed-caps',default='4,5,7,10,13,16')
    ap.add_argument('--label',default='mined')
    args=ap.parse_args()
    mining=json.loads(args.mining.read_text()); allrows=load_raw_rows(args.all_rows)
    allowed={int(x) for x in args.allowed_caps.split(',') if x.strip()}
    score=Counter(); firstpos={}
    for rr,round_rec in enumerate(mining.get('rounds',[])):
        for pos,idx in enumerate(round_rec.get('violation_rows',[])):
            idx=int(idx); score[idx]+=1
            firstpos.setdefault(idx,(rr,pos))
    selected=[]
    for idx,cnt in score.items():
        r=allrows[idx]
        if r['cap'] not in allowed: continue
        selected.append((idx,cnt,r['cap'],r['dim'],r['popcount'],firstpos[idx]))
    selected.sort(key=lambda t:(-t[1], t[2], t[3], -t[4], t[5], t[0]))
    selected=selected[:args.max_rows]
    recs=[allrows[idx]['rec'] for idx,_,_,_,_,_ in selected]
    write_rows(args.output,recs)
    # Pair builder keeps only pairs with threshold target(19)-c1-c2>0.
    useful_pairs=0; threshold_hist=Counter()
    for i in range(len(selected)):
        for j in range(i+1,len(selected)):
            th=19-selected[i][2]-selected[j][2]
            if th>0:
                useful_pairs+=1; threshold_hist[th]+=1
    meta={'schema':'s0908_export_mined_pair_rows_v1','label':args.label,'mining':str(args.mining),'mining_sha256':sha(args.mining),'all_rows':str(args.all_rows),'all_rows_sha256':sha(args.all_rows),'allowed_caps':sorted(allowed),'max_rows':args.max_rows,'selected_count':len(selected),'selected_head':[{'idx':idx,'score':cnt,'cap':cap,'dim':dim,'popcount':pc,'first_round':fp[0],'first_pos':fp[1]} for idx,cnt,cap,dim,pc,fp in selected[:50]],'selected_cap_hist':{str(k):int(v) for k,v in sorted(Counter(t[2] for t in selected).items())},'selected_dim_hist':{str(k):int(v) for k,v in sorted(Counter(t[3] for t in selected).items())},'pair_count_if_all_pairs':len(selected)*(len(selected)-1)//2,'useful_pair_count_threshold_positive':useful_pairs,'useful_pair_threshold_hist':{str(k):int(v) for k,v in sorted(threshold_hist.items())},'output':str(args.output),'output_sha256':sha(args.output)}
    mp=args.output.with_suffix(args.output.suffix+'.meta.json'); mp.write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps(meta,indent=2,sort_keys=True))

if __name__=='__main__': main()
