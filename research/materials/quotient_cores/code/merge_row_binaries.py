#!/usr/bin/env python3
"""Merge E11WANG1 row binaries preserving order."""
from __future__ import annotations
import argparse, hashlib, json, struct, time
from collections import Counter
from pathlib import Path
MAGIC=b'E11WANG1'; REC='<BBHQQQQ'; RECSZ=struct.calcsize(REC)

def read_recs(path):
    data=Path(path).read_bytes(); assert data[:8]==MAGIC, path; n=struct.unpack_from('<I',data,8)[0]; off=12; out=[]; hist=Counter()
    for i in range(n):
        rec=data[off:off+RECSZ]; off+=RECSZ; hist[rec[0]]+=1; out.append(rec)
    return out,hist

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--output',type=Path,required=True); ap.add_argument('inputs',nargs='+')
    args=ap.parse_args(); t0=time.time(); recs=[]; hists={}; hist=Counter()
    for p in args.inputs:
        rs,h=read_recs(Path(p)); recs.extend(rs); hists[str(p)]={str(k):int(v) for k,v in sorted(h.items())}; hist.update(h)
    blob=bytearray(); blob.extend(MAGIC); blob.extend(struct.pack('<I',len(recs))); blob.extend(b''.join(recs))
    args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_bytes(blob)
    meta={'schema':'s0908_merge_row_binaries_v1','inputs':[str(p) for p in args.inputs],'input_hists':hists,'output':str(args.output),'rows':len(recs),'cap_hist':{str(k):int(v) for k,v in sorted(hist.items())},'sha256':hashlib.sha256(blob).hexdigest(),'elapsed_sec':time.time()-t0}
    args.output.with_suffix(args.output.suffix+'.meta.json').write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps(meta,indent=2,sort_keys=True))
if __name__=='__main__': main()
