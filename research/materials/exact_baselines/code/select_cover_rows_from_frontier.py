#!/usr/bin/env python3
"""Select Wang cover rows from frontier certificates and write a compact binary.

The analysis cover DFS stores indices relative to a cover binary (e.g. all cap 6/7
rows).  This script collects the certificate row indices appearing in selected
outputs, optionally adds the first N cover rows as a control set, and writes a
small E11WANG1 binary for faster replay.
"""
from __future__ import annotations
import argparse, hashlib, json, re, struct, time
from collections import Counter
from pathlib import Path
MAGIC=b'E11WANG1'; REC='<BBHQQQQ'; RECSZ=struct.calcsize(REC)

def load_records(path:Path):
    data=path.read_bytes(); assert data[:8]==MAGIC; n=struct.unpack_from('<I',data,8)[0]; off=12; recs=[]
    for i in range(n):
        rec=data[off:off+RECSZ]; off+=RECSZ; cap=rec[0]; dim=rec[1]; recs.append((cap,dim,rec))
    return recs

def collect_indices(paths):
    ids=set(); detail=[]
    for p in paths:
        obj=json.loads(Path(p).read_text())
        # recursively walk lists/dicts for cover_certificates_head entries
        def walk(x):
            if isinstance(x,dict):
                if 'cover_certificates_head' in x:
                    for c in x['cover_certificates_head']:
                        if isinstance(c,dict) and 'row' in c:
                            ids.add(int(c['row'])); detail.append({'path':str(p),'row':int(c['row']),'cap':c.get('cap'),'depth':c.get('depth'),'residual':c.get('residual'),'future_out':c.get('future_out'),'need':c.get('need')})
                for v in x.values(): walk(v)
            elif isinstance(x,list):
                for v in x: walk(v)
        walk(obj)
    return ids,detail

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--cover-source',type=Path,required=True); ap.add_argument('--output',type=Path,required=True); ap.add_argument('--add-first',type=int,default=0); ap.add_argument('jsons',nargs='*')
    args=ap.parse_args(); t0=time.time(); recs=load_records(args.cover_source); ids=set(range(min(args.add_first,len(recs)))); ids_from,detail=collect_indices(args.jsons); ids|=ids_from; order=sorted(i for i in ids if 0<=i<len(recs)); blob=bytearray(); blob.extend(MAGIC); blob.extend(struct.pack('<I',len(order))); hist=Counter(); dims=Counter()
    for i in order:
        cap,dim,rec=recs[i]; hist[cap]+=1; dims[dim]+=1; blob.extend(rec)
    args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_bytes(blob)
    meta={'schema':'s0908_selected_cover_rows_v1','cover_source':str(args.cover_source),'output':str(args.output),'output_rows':len(order),'add_first':args.add_first,'selected_indices':order,'cap_hist':{str(k):int(v) for k,v in sorted(hist.items())},'dim_hist':{str(k):int(v) for k,v in sorted(dims.items())},'sha256':hashlib.sha256(blob).hexdigest(),'source_jsons':[str(p) for p in args.jsons],'certificate_details_head':detail[:50],'elapsed_sec':time.time()-t0}
    args.output.with_suffix(args.output.suffix+'.meta.json').write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps(meta,indent=2,sort_keys=True))
if __name__=='__main__': main()
