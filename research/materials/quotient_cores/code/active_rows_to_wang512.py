#!/usr/bin/env python3
"""Convert pivot-fixed active JSONL rows to a WANG512 binary for safe DFS.

The active JSONL rows contain full masks and original full caps.  When safe DFS
is run with --force-prefix pivot, these rows impose the same full occupation
constraints.  This converter can add the 255 span(p,a) pair rows explicitly so
that lift-bit/pair constraints are present even if a dominance pass removed
some two-dimensional rows from the active core used by CP-SAT.
"""
from __future__ import annotations
import argparse, json, struct
from collections import Counter
from pathlib import Path

MAGIC=b"WANG512\x01"


def points_from_words(words):
    pts=[]
    for wi,w0 in enumerate(words):
        w=int(w0)
        while w:
            lb=w & -w
            b=lb.bit_length()-1
            p=wi*64+b
            if 1 <= p <= 511: pts.append(p)
            w ^= lb
    return pts


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--active',type=Path,required=True)
    ap.add_argument('--pivot',type=int,required=True)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--add-pairs',action='store_true')
    args=ap.parse_args()
    rows=[]; seen=set(); cap_hist=Counter(); dim_hist=Counter()
    if args.add_pairs:
        done=set()
        for a in range(1,512):
            if a==args.pivot: continue
            b=a^args.pivot
            if b==0 or b==args.pivot: continue
            pair=tuple(sorted((a,b)))
            if pair in done: continue
            done.add(pair)
            words=[0]*8
            for p in (args.pivot,pair[0],pair[1]):
                words[p>>6] |= 1 << (p&63)
            key=(2,2,tuple(words))
            seen.add((2,tuple(words)))
            rows.append((2,2,tuple(words)))
            cap_hist[2]+=1; dim_hist[2]+=1
    with args.active.open() as f:
        for line in f:
            if not line.strip(): continue
            r=json.loads(line)
            cap=int(r['cap']); dim=int(r.get('dim',0)); words=tuple(int(w) for w in r['words'])
            key=(cap,words)
            if key in seen: continue
            seen.add(key); rows.append((cap,dim,words)); cap_hist[cap]+=1; dim_hist[dim]+=1
    args.out.parent.mkdir(parents=True,exist_ok=True)
    with args.out.open('wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I',len(rows)))
        for cap,dim,words in rows:
            f.write(struct.pack('<BBH',cap,dim,0))
            for w in words: f.write(struct.pack('<Q',int(w)))
    meta={'schema':'active_rows_to_wang512_v1','active':str(args.active),'pivot':args.pivot,'add_pairs':args.add_pairs,'rows':len(rows),'cap_hist':dict(sorted((int(k),int(v)) for k,v in cap_hist.items())),'dim_hist':dict(sorted((int(k),int(v)) for k,v in dim_hist.items())),'out':str(args.out),'size_bytes':args.out.stat().st_size,'expected_size_bytes':12+68*len(rows),'size_matches':args.out.stat().st_size==12+68*len(rows)}
    args.out.with_suffix('.meta.json').write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps(meta,indent=2,sort_keys=True))

if __name__=='__main__': main()
