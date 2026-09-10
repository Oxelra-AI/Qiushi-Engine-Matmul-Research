#!/usr/bin/env python3
"""Export selected analysis mixed-source support cuts to a compact binary file.

The JSON cut bitsets use bit p-1 for quotient direction p.  The binary file uses
256-bit words with bit p for p=1..255, matching E11WANG1 row masks.
"""
from __future__ import annotations
import argparse, hashlib, json, struct, time
from collections import Counter
from pathlib import Path

IN = Path("data/mixed_source_cuts/unique_nondominated_cuts_top50k.json")
OUTDIR = Path("data/domain_dfs_soundness")
MAGIC = b"MIXCUT1\0"  # 8 bytes


def words_from_bitset(bs: int):
    w = [0,0,0,0]
    for p in range(1,256):
        if (bs >> (p-1)) & 1:
            w[p>>6] |= 1 << (p&63)
    return tuple(w)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--input', type=Path, default=IN)
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    ap.add_argument('--max-cuts', type=int, default=1440)
    ap.add_argument('--min-gap', type=int, default=6)
    ap.add_argument('--min-K', type=int, default=15)
    ap.add_argument('--require-lam-ne-nu', action='store_true')
    args=ap.parse_args(); args.outdir.mkdir(parents=True, exist_ok=True)
    t0=time.time()
    data=json.loads(args.input.read_text())
    recs=[]; packed=[]; hist=Counter(); gaps=Counter(); names=[]
    for rec in data['cuts']:
        if int(rec['gap_K_minus_LD']) < args.min_gap or int(rec['K']) < args.min_K:
            continue
        if args.require_lam_ne_nu and int(rec.get('lam_B',-1)) == int(rec.get('nu_C',-2)):
            continue
        K=int(rec['K']); w1=words_from_bitset(int(rec['coeff1_bitset'])); w2=words_from_bitset(int(rec['coeff2_bitset']))
        # Sanity: coefficient sets should be disjoint and count agree with JSON.
        c1=sum(x.bit_count() for x in w1); c2=sum(x.bit_count() for x in w2)
        counts=rec.get('coeff_counts_0_1_2')
        if counts is not None and (c1 != int(counts[1]) or c2 != int(counts[2])):
            raise ValueError((rec, c1, c2))
        packed.append((K,w1,w2))
        recs.append({k:rec[k] for k in ('mu','lam_B','nu_C','K','L_D','gap_K_minus_LD','rank_tuple','r_tuple','coeff_counts_0_1_2') if k in rec})
        hist[K]+=1; gaps[int(rec['gap_K_minus_LD'])]+=1
        if len(recs) >= args.max_cuts:
            break
    blob=bytearray(); blob.extend(MAGIC); blob.extend(struct.pack('<I', len(packed)))
    for K,w1,w2 in packed:
        blob.extend(struct.pack('<BBHQQQQQQQQ', K, 0, 0, *w1, *w2))
    tag=f"mixed_cuts_gap{args.min_gap}_K{args.min_K}_n{len(packed)}"
    if args.require_lam_ne_nu: tag += '_lamne'
    bin_path=args.outdir/(tag+'.bin')
    bin_path.write_bytes(bytes(blob))
    meta={
        'schema':'s0908_mixed_cut_binary_v1','source_json':str(args.input),'binary_path':str(bin_path),
        'binary_sha256':hashlib.sha256(bytes(blob)).hexdigest(),'cut_count':len(packed),'params':{'input':str(args.input),'outdir':str(args.outdir),'max_cuts':args.max_cuts,'min_gap':args.min_gap,'min_K':args.min_K,'require_lam_ne_nu':args.require_lam_ne_nu},
        'K_hist':dict(sorted((int(k),int(v)) for k,v in hist.items())),
        'gap_hist':dict(sorted((int(k),int(v)) for k,v in gaps.items())),
        'cuts_head':recs[:20], 'elapsed_sec':time.time()-t0,
        'semantics':'Each cut is a lower bound sum(c_p x_p)>=K with coeff1 and coeff2 masks over quotient directions p=1..255.'
    }
    meta_path=args.outdir/(tag+'.meta.json')
    meta_path.write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps(meta,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
