#!/usr/bin/env python3
"""analysis: merge rank-2 cap<=5 quotient rows with multiple lift-cut orbit row files.

Rows are in native E11WANG1 format.  The cap<=5 quotient rows are kept first;
extra lift cuts are deduplicated by their 256-bit mask and cap/rhs.
"""
from __future__ import annotations
import argparse, hashlib, json, struct
from pathlib import Path

ROOT=Path('research/research_record')
BASE=ROOT/'workspace/data/quotient_dfs/rank2_cap5_n19.bin'
DEFAULT_ROWS=[
    ROOT/'workspace/data/quotient_lift/transport/rank2_lift_cut_transport_rows.bin',
    ROOT/'workspace/data/quotient_lift/transport/rank2_survivor2_lift_cut_transport_rows.bin',
]
OUTDIR=ROOT/'workspace/data/quotient_lift/transport'
OUTDIR.mkdir(parents=True,exist_ok=True)
MAGIC=b'E11WANG1'
REC='<BBHQQQQ'


def sha(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''):
            h.update(c)
    return h.hexdigest()


def load_rows(path:Path):
    d=path.read_bytes(); assert d[:8]==MAGIC, path
    n=struct.unpack('<I',d[8:12])[0]; off=12; rows=[]; sz=struct.calcsize(REC)
    for _ in range(n):
        cap,dim,pad,w0,w1,w2,w3=struct.unpack_from(REC,d,off); off+=sz
        rows.append((int(cap),int(dim),int(w0),int(w1),int(w2),int(w3)))
    assert off==len(d), (path,off,len(d))
    return rows


def write_rows(path:Path, rows):
    with path.open('wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I',len(rows)))
        for cap,dim,w0,w1,w2,w3 in rows:
            f.write(struct.pack(REC,int(cap),int(dim),0,int(w0),int(w1),int(w2),int(w3)))


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--base',type=Path,default=BASE); ap.add_argument('--row-file',type=Path,action='append',default=[]); ap.add_argument('--label',default='two_orbits')
    args=ap.parse_args(); row_files=args.row_file or DEFAULT_ROWS
    base_rows=load_rows(args.base)
    extras=[]; seen=set(); per=[]
    for rp in row_files:
        rows=load_rows(rp); added=0; dup=0
        for r in rows:
            key=(r[0],r[2],r[3],r[4],r[5])
            if key in seen:
                dup+=1; continue
            seen.add(key); extras.append(r); added+=1
        per.append({'path':str(rp),'sha256':sha(rp),'rows':len(rows),'new_unique_rows':added,'duplicates_with_prior_extra':dup})
    outbin=OUTDIR/f'rank2_cap5_plus_{args.label}_lift_cut_orbits.bin'
    manifest=OUTDIR/f'rank2_cap5_plus_{args.label}_lift_cut_orbits_manifest.json'
    write_rows(outbin,base_rows+extras)
    out={'schema':'s0908_merge_rank2_lift_cut_orbits_v1','base':str(args.base),'base_sha256':sha(args.base),'base_rows':len(base_rows),'row_files':per,'unique_extra_rows':len(extras),'merged_binary':str(outbin),'merged_rows':len(base_rows)+len(extras),'merged_sha256':sha(outbin),'label':args.label}
    manifest.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__': main()
