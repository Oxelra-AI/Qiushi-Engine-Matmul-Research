#!/usr/bin/env python3
"""Filter an E11WANG1 row binary by capacity range."""
from __future__ import annotations
import argparse, hashlib, json, struct
from collections import Counter
from pathlib import Path
MAGIC=b'E11WANG1'; REC='<BBHQQQQ'

def sha(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''):
            h.update(c)
    return h.hexdigest()

def load_rows(path:Path):
    d=path.read_bytes(); assert d[:8]==MAGIC, path
    n=struct.unpack('<I',d[8:12])[0]; off=12; sz=struct.calcsize(REC); rows=[]
    for _ in range(n):
        r=struct.unpack_from(REC,d,off); off+=sz; rows.append(r)
    assert off==len(d)
    return rows

def write_rows(path:Path,rows):
    with path.open('wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I',len(rows)))
        for cap,dim,pad,w0,w1,w2,w3 in rows:
            f.write(struct.pack(REC,int(cap),int(dim),0,int(w0),int(w1),int(w2),int(w3)))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',type=Path,required=True); ap.add_argument('--output',type=Path,required=True); ap.add_argument('--min-cap',type=int,default=0); ap.add_argument('--max-cap',type=int,required=True); ap.add_argument('--label',default='filtered')
    args=ap.parse_args(); rows=load_rows(args.input); out=[r for r in rows if args.min_cap<=int(r[0])<=args.max_cap]
    args.output.parent.mkdir(parents=True,exist_ok=True); write_rows(args.output,out)
    hist=Counter(int(r[0]) for r in out); dim=Counter(int(r[1]) for r in out)
    meta={'schema':'s0908_filter_e11wang_rows_v1','label':args.label,'input':str(args.input),'input_sha256':sha(args.input),'input_rows':len(rows),'min_cap':args.min_cap,'max_cap':args.max_cap,'output':str(args.output),'output_rows':len(out),'output_sha256':sha(args.output),'cap_hist':{str(k):int(v) for k,v in sorted(hist.items())},'dim_hist':{str(k):int(v) for k,v in sorted(dim.items())}}
    mp=args.output.with_suffix(args.output.suffix+'.meta.json'); mp.write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps(meta,indent=2,sort_keys=True))
if __name__=='__main__': main()
