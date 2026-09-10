#!/usr/bin/env python3
"""Merge a capacity prefix from an E11WANG1 binary with rows violated in mining logs."""
from __future__ import annotations
import argparse, hashlib, json, struct
from collections import Counter
from pathlib import Path
MAGIC=b'E11WANG1'; REC='<BBHQQQQ'; SZ=struct.calcsize(REC)

def sha(p:Path)->str:
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()

def load_rows(p:Path):
    d=p.read_bytes(); assert d[:8]==MAGIC, (p,d[:8])
    n=struct.unpack('<I',d[8:12])[0]; assert len(d)==12+n*SZ, (len(d),12+n*SZ)
    rows=[]
    for i in range(n):
        off=12+i*SZ; rec=d[off:off+SZ]; cap,dim,pad,w0,w1,w2,w3=struct.unpack(REC,rec)
        rows.append({'idx':i,'cap':int(cap),'dim':int(dim),'rec':rec})
    return rows

def write_rows(p:Path,recs):
    p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I',len(recs)))
        for r in recs: f.write(r)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--all-rows',type=Path,required=True)
    ap.add_argument('--mining',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--prefix-cap',type=int,default=3)
    ap.add_argument('--label',default='merged')
    args=ap.parse_args()
    rows=load_rows(args.all_rows); mining=json.loads(args.mining.read_text())
    idxs={r['idx'] for r in rows if 0<int(r['cap'])<=args.prefix_cap}
    for rr in mining.get('rounds',[]):
        for idx in rr.get('violation_rows',[]): idxs.add(int(idx))
    idxs=sorted(idxs)
    recs=[rows[i]['rec'] for i in idxs]
    write_rows(args.output,recs)
    hist=Counter(rows[i]['cap'] for i in idxs); dim=Counter(rows[i]['dim'] for i in idxs)
    meta={'schema':'s0908_merge_cap_prefix_with_mining_rows_v1','label':args.label,'all_rows':str(args.all_rows),'all_rows_sha256':sha(args.all_rows),'mining':str(args.mining),'mining_sha256':sha(args.mining),'prefix_cap':args.prefix_cap,'output':str(args.output),'output_sha256':sha(args.output),'row_count':len(idxs),'added_beyond_prefix':sum(1 for i in idxs if rows[i]['cap']>args.prefix_cap),'cap_hist':{str(k):int(v) for k,v in sorted(hist.items())},'dim_hist':{str(k):int(v) for k,v in sorted(dim.items())},'row_index_head':idxs[:50],'row_index_tail':idxs[-50:]}
    mp=args.output.with_suffix(args.output.suffix+'.meta.json'); mp.write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps(meta,indent=2,sort_keys=True))
if __name__=='__main__': main()
