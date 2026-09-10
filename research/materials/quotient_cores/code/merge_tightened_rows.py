#!/usr/bin/env python3
"""Merge a native E11WANG1 row binary with tightened rows, keeping min cap per mask."""
from __future__ import annotations
import argparse, json, struct, hashlib
from collections import Counter
from pathlib import Path
MAGIC=b'E11WANG1'; REC='<BBHQQQQ'; SZ=struct.calcsize(REC)

def sha(p:Path):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()

def load(p:Path, source:str):
    d=p.read_bytes(); assert d[:8]==MAGIC, (p,d[:8])
    n=struct.unpack('<I',d[8:12])[0]; assert len(d)==12+n*SZ, (p,len(d),12+n*SZ)
    rows=[]
    for i in range(n):
        rec=d[12+i*SZ:12+(i+1)*SZ]
        cap,dim,pad,w0,w1,w2,w3=struct.unpack(REC,rec)
        mask=int(w0)|(int(w1)<<64)|(int(w2)<<128)|(int(w3)<<192)
        rows.append({'source':source,'source_index':i,'cap':int(cap),'dim':int(dim),'mask':mask,'rec':rec})
    return rows

def pack(cap:int,dim:int,mask:int):
    words=[(mask>>(64*j))&((1<<64)-1) for j in range(4)]
    return struct.pack(REC,cap,dim,0,*words)

def write(p:Path, rows):
    p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I',len(rows)))
        for r in rows: f.write(pack(r['cap'],r['dim'],r['mask']))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--base',type=Path,required=True); ap.add_argument('--tight',type=Path,required=True); ap.add_argument('--output',type=Path,required=True); ap.add_argument('--label',required=True); args=ap.parse_args()
    base=load(args.base,'base'); tight=load(args.tight,'tight')
    best={}; provenance={}; replaced=0; added=0; equal=0
    for r in base:
        best[r['mask']]={'cap':r['cap'],'dim':r['dim'],'mask':r['mask']}; provenance[r['mask']]={'base_cap':r['cap'],'base_dim':r['dim'],'base_index':r['source_index']}
    for r in tight:
        old=best.get(r['mask'])
        if old is None:
            best[r['mask']]={'cap':r['cap'],'dim':r['dim'],'mask':r['mask']}; provenance[r['mask']]={'tight_cap':r['cap'],'tight_dim':r['dim'],'tight_index':r['source_index']}; added+=1
        elif r['cap']<old['cap']:
            provenance[r['mask']].update({'tight_cap':r['cap'],'tight_dim':r['dim'],'tight_index':r['source_index'],'replaced_old_cap':old['cap']})
            old['cap']=r['cap']; old['dim']=r['dim']; replaced+=1
        elif r['cap']==old['cap']:
            equal+=1
    rows=sorted(best.values(), key=lambda r:(r['cap'],r['dim'],r['mask']))
    write(args.output,rows)
    cap_hist=Counter(r['cap'] for r in rows); dim_hist=Counter(r['dim'] for r in rows)
    meta={'schema':'s0908_merge_tightened_rows_v1','label':args.label,'base':str(args.base),'base_sha256':sha(args.base),'tight':str(args.tight),'tight_sha256':sha(args.tight),'output':str(args.output),'output_sha256':sha(args.output),'base_count':len(base),'tight_count':len(tight),'output_count':len(rows),'tight_added_new_masks':added,'tight_replaced_base_caps':replaced,'tight_equal_caps':equal,'cap_hist':{str(k):int(v) for k,v in sorted(cap_hist.items())},'dim_hist':{str(k):int(v) for k,v in sorted(dim_hist.items())},'replaced_head':[{'mask_hex':hex(m),**p} for m,p in list(provenance.items()) if 'replaced_old_cap' in p][:50]}
    args.output.with_suffix(args.output.suffix+'.meta.json').write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps(meta,indent=2,sort_keys=True))
if __name__=='__main__': main()
