#!/usr/bin/env python3
"""Take first N rows from an E11WANG1 row binary."""
from __future__ import annotations
import argparse, hashlib, json, struct, time
from collections import Counter
from pathlib import Path
REC='<BBHQQQQ'; RECSZ=struct.calcsize(REC); MAGIC=b'E11WANG1'

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',type=Path,required=True); ap.add_argument('--n',type=int,required=True); ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args(); t0=time.time(); data=args.input.read_bytes(); assert data[:8]==MAGIC; n=struct.unpack_from('<I',data,8)[0]; take=min(args.n,n); off=12
    recs=[]; hist=Counter()
    for i in range(n):
        rec=data[off:off+RECSZ]; off+=RECSZ
        if i<take:
            cap=rec[0]; hist[cap]+=1; recs.append(rec)
    blob=bytearray(); blob.extend(MAGIC); blob.extend(struct.pack('<I',len(recs))); blob.extend(b''.join(recs))
    args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_bytes(blob)
    meta={'schema':'s0908_slice_row_binary_v1','input':str(args.input),'output':str(args.output),'input_rows':n,'take':take,'cap_hist':{str(k):int(v) for k,v in sorted(hist.items())},'sha256':hashlib.sha256(blob).hexdigest(),'elapsed_sec':time.time()-t0}
    args.output.with_suffix(args.output.suffix+'.meta.json').write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps(meta,indent=2,sort_keys=True))
if __name__=='__main__': main()
