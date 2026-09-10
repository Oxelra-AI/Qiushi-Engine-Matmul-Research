#!/usr/bin/env python3
"""Export the analysis minimized lift-bit obstruction as native E11WANG1 rows.

The row is not a quotient-Wang row; it is a valid monotone A-side lift cut for
rank-2 pivot 17 in the analysis high-pivot/native-bit-p quotient coordinates.
It can nevertheless be consumed by the same upper-bound DFS because its semantics
is |support cap A| <= 11.
"""
from __future__ import annotations
import hashlib, json, struct
from pathlib import Path
ROOT=Path('research/research_record')
CUT_JSON=ROOT/'workspace/data/quotient_lift/minimized_lift_cut_peer.json'
QBIN=ROOT/'workspace/data/quotient_dfs/rank2_cap5_n19.bin'
OUTDIR=ROOT/'workspace/data/quotient_lift'
ROWBIN=OUTDIR/'rank2_peer_lift_cut_row.bin'
MERGED=OUTDIR/'rank2_cap5_plus_peer_lift_cut.bin'
MANIFEST=OUTDIR/'rank2_peer_lift_cut_row_manifest.json'

def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()

def write_rows(path, rows):
    with path.open('wb') as f:
        f.write(b'E11WANG1'); f.write(struct.pack('<I',len(rows)))
        for cap,dim,mask in rows:
            f.write(struct.pack('<BBH',cap,dim,0))
            for i in range(4): f.write(struct.pack('<Q',(mask>>(64*i))&((1<<64)-1)))

def read_payload_after_count(path):
    b=path.read_bytes(); assert b[:8]==b'E11WANG1'; n=struct.unpack('<I',b[8:12])[0]; return n,b[12:]

def main():
    data=json.loads(CUT_JSON.read_text()); pts=[int(x) for x in data['cut']['points']]; rhs=int(data['cut']['rhs'])
    mask=0
    for p in pts: mask |= 1<<p
    write_rows(ROWBIN,[(rhs,0,mask)])
    n,payload=read_payload_after_count(QBIN)
    row_n,row_payload=read_payload_after_count(ROWBIN)
    merged=bytearray(); merged.extend(b'E11WANG1'); merged.extend(struct.pack('<I',n+row_n)); merged.extend(payload); merged.extend(row_payload)
    MERGED.write_bytes(bytes(merged))
    manifest={'schema':'s0908_rank2_lift_cut_row_v1','semantics':'valid upper row |support cap cut_points| <= rhs for rank2 pivot 17, derived from all-Wang lift-bit infeasibility certificate','cut_json':str(CUT_JSON),'cut_points':pts,'rhs':rhs,'row_mask_hex':hex(mask),'row_binary':str(ROWBIN),'row_binary_sha256':sha(ROWBIN),'source_quotient_binary':str(QBIN),'source_quotient_binary_sha256':sha(QBIN),'source_rows':n,'merged_binary':str(MERGED),'merged_binary_sha256':sha(MERGED),'merged_rows':n+row_n}
    MANIFEST.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    print(json.dumps(manifest,indent=2,sort_keys=True))
if __name__=='__main__': main()
