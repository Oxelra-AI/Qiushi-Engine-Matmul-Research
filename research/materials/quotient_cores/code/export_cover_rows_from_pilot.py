#!/usr/bin/env python3
"""Export E11WANG1 cover rows referenced by a cover-DFS pilot certificate head.

This is a tiny helper for analysis: if a cover-pruning run shows useful cover
certificates, copy those referenced rows from the cover row table into a small
cover binary for focused replay experiments.
"""
from __future__ import annotations
import argparse, hashlib, json, struct
from pathlib import Path
MAGIC=b'E11WANG1'; REC='<BBHQQQQ'; RECSZ=struct.calcsize(REC)

def sha(p:Path):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1<<20), b''):
            h.update(c)
    return h.hexdigest()

def load_raw(path:Path):
    d=path.read_bytes(); assert d[:8]==MAGIC
    n=struct.unpack('<I',d[8:12])[0]; assert len(d)==12+n*RECSZ
    rows=[]
    for i in range(n):
        off=12+i*RECSZ; rec=d[off:off+RECSZ]
        cap,dim,pad,w0,w1,w2,w3=struct.unpack(REC,rec)
        mask=int(w0)|(int(w1)<<64)|(int(w2)<<128)|(int(w3)<<192)
        rows.append({'idx':i,'cap':int(cap),'dim':int(dim),'popcount':mask.bit_count(),'rec':rec})
    return rows

def write(path:Path,recs):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I',len(recs)))
        for r in recs: f.write(r)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--pilot',type=Path,required=True)
    ap.add_argument('--cover-rows',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    pilot=json.loads(args.pilot.read_text())
    idxs=[]
    certs=[]
    certs.extend(pilot.get('cover_certificates_head', []))
    for rr in pilot.get('results', []):
        certs.extend(rr.get('cover_certificates_head', []))
    for cert in certs:
        # analysis records cover-row index within the supplied cover-constraints file.
        idxs.append(int(cert['row']))
    idxs=sorted(set(idxs))
    rows=load_raw(args.cover_rows)
    recs=[rows[i]['rec'] for i in idxs]
    write(args.output,recs)
    meta={'schema':'s0908_export_cover_rows_from_pilot_v1','pilot':str(args.pilot),'pilot_sha256':sha(args.pilot),'cover_rows':str(args.cover_rows),'cover_rows_sha256':sha(args.cover_rows),'selected_indices':idxs,'selected_count':len(idxs),'selected_rows':[{'idx':i,'cap':rows[i]['cap'],'dim':rows[i]['dim'],'popcount':rows[i]['popcount']} for i in idxs],'output':str(args.output),'output_sha256':sha(args.output)}
    args.output.with_suffix(args.output.suffix+'.meta.json').write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps(meta,indent=2,sort_keys=True))
if __name__=='__main__': main()
