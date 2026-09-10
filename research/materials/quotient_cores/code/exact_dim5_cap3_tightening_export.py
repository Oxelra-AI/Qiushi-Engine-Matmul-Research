#!/usr/bin/env python3
"""Exact enumeration for dim-5 cap-3 quotient-row tightening.

For each native quotient Wang row U with dim=5 and cap=3, test whether three
points inside U can satisfy all strict child rows V<=U with cap<3.  If no such
triple exists, then the cap-3 row is recursively implied to have cap<=2 under
those child rows.  This exports lowered cap-2 rows as an experimental/prunable
necessary-condition family with an exact replay record.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, struct, time
from collections import Counter
from pathlib import Path

ROOT=Path('research/research_record')
OUTDIR=ROOT/'workspace/data/quotient_lift/tightening'
OUTDIR.mkdir(parents=True,exist_ok=True)
ROWS={'rank2':Path('data/wang_native/quotient_binaries/rank2_all_n19.bin'),
      'rank3':Path('data/wang_native/quotient_binaries/rank3_all_n19.bin')}
MAGIC=b'E11WANG1'; REC='<BBHQQQQ'; SZ=struct.calcsize(REC)


def sha(path:Path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()


def load_rows(path:Path):
    d=path.read_bytes(); assert d[:8]==MAGIC
    n=struct.unpack('<I',d[8:12])[0]; assert len(d)==12+n*SZ
    rows=[]; hist=Counter()
    for i in range(n):
        cap,dim,pad,w0,w1,w2,w3=struct.unpack(REC,d[12+i*SZ:12+(i+1)*SZ])
        mask=int(w0)|(int(w1)<<64)|(int(w2)<<128)|(int(w3)<<192)
        rows.append({'idx':i,'cap':int(cap),'dim':int(dim),'mask':mask,'words':(int(w0),int(w1),int(w2),int(w3)),'pop':mask.bit_count()})
        hist[(int(dim),int(cap))]+=1
    return rows, {'path':str(path),'sha256':sha(path),'count':n,'dim_cap_hist':{f'{d}:{c}':int(v) for (d,c),v in sorted(hist.items())}}


def pts(mask:int): return [i for i in range(1,256) if (mask>>i)&1]


def pack_row(cap:int, dim:int, mask:int):
    words=[(mask>>(64*j)) & ((1<<64)-1) for j in range(4)]
    return struct.pack(REC,int(cap),int(dim),0,*words)


def write_rows(path:Path,recs):
    with path.open('wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I',len(recs)))
        for r in recs: f.write(r)


def test_row(U, allrows):
    Umask=U['mask']; Upts=pts(Umask); pos={p:i for i,p in enumerate(Upts)}
    # strict child rows with cap<3 and mask subset U; only cap2 rows matter for distinct triples,
    # but keep cap1 in counts for provenance.
    child=[]; child_hist=Counter(); child_dim_hist=Counter()
    for r in allrows:
        m=r['mask']
        if m==0 or m==Umask: continue
        if (m & ~Umask)!=0: continue
        if r['cap']>=3: continue
        cm=0
        for p in Upts:
            if (m>>p)&1: cm |= 1<<pos[p]
        if cm.bit_count()<=r['cap']: continue
        child.append({'idx':r['idx'],'cap':r['cap'],'dim':r['dim'],'cmask':cm,'pop':cm.bit_count()})
        child_hist[r['cap']]+=1; child_dim_hist[r['dim']]+=1
    feasible=None; triple_count=0; blocked_by=Counter(); first_blocks=[]
    # For target=3, a triple violates a child iff child cap<=2 and child contains the triple;
    # cap1 rows cannot contain three distinct points if their active pop <= 1, but the generic
    # condition below is still exact.
    for comb in itertools.combinations(range(len(Upts)),3):
        triple_count+=1; tm=(1<<comb[0])|(1<<comb[1])|(1<<comb[2])
        bad=None
        for ci,ch in enumerate(child):
            if (tm & ch['cmask']) == tm and 3 > ch['cap']:
                bad=ci; break
        if bad is None:
            feasible=[Upts[i] for i in comb]; break
        blocked_by[child[bad]['idx']]+=1
        if len(first_blocks)<20:
            first_blocks.append({'triple':[Upts[i] for i in comb],'child_idx':child[bad]['idx'],'child_cap':child[bad]['cap'],'child_dim':child[bad]['dim']})
    return {'feasible_triple':feasible,'triple_count_checked':triple_count,'child_count':len(child),'child_cap_hist':dict(sorted(child_hist.items())),'child_dim_hist':dict(sorted(child_dim_hist.items())),'top_blocking_children':[{'idx':idx,'count':cnt} for idx,cnt in blocked_by.most_common(10)],'first_blocks':first_blocks}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--pivot',choices=['rank2','rank3'],required=True); args=ap.parse_args(); t0=time.time()
    rows,meta=load_rows(ROWS[args.pivot]); cand=[r for r in rows if r['dim']==5 and r['cap']==3]
    tightened=[]; feasible=[]; results=[]; child_hist=Counter(); child_dim_hist=Counter()
    for j,U in enumerate(cand):
        res=test_row(U,rows)
        for k,v in res['child_cap_hist'].items(): child_hist[int(k)]+=v
        for k,v in res['child_dim_hist'].items(): child_dim_hist[int(k)]+=v
        rr={'row_idx':U['idx'],'dim':U['dim'],'old_cap':U['cap'],'new_cap_if_tightened':2,'pop':U['pop'],'result':res}
        if res['feasible_triple'] is None: tightened.append(U)
        else: feasible.append({'row_idx':U['idx'],'triple':res['feasible_triple']})
        if len(results)<100 or res['feasible_triple'] is not None: results.append(rr)
        if (j+1)%100==0 or j+1==len(cand): print(args.pivot,j+1,'/',len(cand),'tightened',len(tightened),'feasible',len(feasible),flush=True)
    outbin=OUTDIR/f'{args.pivot}_dim5_cap3_tightened_to_cap2_rows.bin'
    write_rows(outbin,[pack_row(2,r['dim'],r['mask']) for r in tightened])
    out={'schema':'s0908_exact_dim5_cap3_tightening_v1','meaning':'Each reported row U originally has quotient cap 3. Exhaustive enumeration found no 3-point subset of U satisfying all strict child rows V<=U with cap<3, so U may be used as cap<=2 provided this child-row derivation is included in the proof chain. This is not a standalone full branch proof.','pivot':args.pivot,'rows_meta':meta,'candidate_count':len(cand),'tightened_count':len(tightened),'feasible_count':len(feasible),'feasible_examples':feasible[:20],'aggregate_child_cap_hist':dict(sorted(child_hist.items())),'aggregate_child_dim_hist':dict(sorted(child_dim_hist.items())),'results_head':results,'tightened_row_indices':[r['idx'] for r in tightened],'output_rows':str(outbin),'output_rows_sha256':sha(outbin),'elapsed_sec':time.time()-t0}
    outjson=OUTDIR/f'{args.pivot}_dim5_cap3_tightened_to_cap2_exact.json'; outjson.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'json':str(outjson),'binary':str(outbin),'candidate_count':len(cand),'tightened_count':len(tightened),'feasible_count':len(feasible),'sha256':sha(outbin),'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__': main()
