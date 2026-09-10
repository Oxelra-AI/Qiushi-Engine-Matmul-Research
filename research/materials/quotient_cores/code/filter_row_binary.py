#!/usr/bin/env python3
"""Filter E11WANG1 row binary by cap range."""
from __future__ import annotations
import argparse, hashlib, json, struct, time
from collections import Counter
from pathlib import Path
MAGIC=b'E11WANG1'
REC='<BBHQQQQ'; RECSZ=struct.calcsize(REC)

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',type=Path,required=True); ap.add_argument('--min-cap',type=int,default=0); ap.add_argument('--max-cap',type=int,default=255); ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args(); t0=time.time(); data=args.input.read_bytes(); assert data[:8]==MAGIC; n=struct.unpack_from('<I',data,8)[0]; off=12
    out=[]; hist=Counter(); inhist=Counter()
    for i in range(n):
        rec=data[off:off+RECSZ]; off+=RECSZ
        cap,dim,res,*ws=struct.unpack(REC,rec); inhist[cap]+=1
        if args.min_cap<=cap<=args.max_cap:
            out.append(rec); hist[cap]+=1
    blob=bytearray(); blob.extend(MAGIC); blob.extend(struct.pack('<I',len(out))); blob.extend(b''.join(out))
    args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_bytes(blob)
    meta={'schema':'s0908_filter_row_binary_v1','input':str(args.input),'output':str(args.output),'min_cap':args.min_cap,'max_cap':args.max_cap,'input_rows':n,'output_rows':len(out),'input_cap_hist':{str(k):int(v) for k,v in sorted(inhist.items())},'output_cap_hist':{str(k):int(v) for k,v in sorted(hist.items())},'sha256':hashlib.sha256(blob).hexdigest(),'elapsed_sec':time.time()-t0}
    mp=args.output.with_suffix(args.output.suffix+'.meta.json'); mp.write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n'); print(json.dumps(meta,indent=2,sort_keys=True))
if __name__=='__main__': main()
