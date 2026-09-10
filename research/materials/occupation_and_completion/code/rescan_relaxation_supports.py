#!/usr/bin/env python3
"""analysis: rescan supports found by a row-family relaxation against stronger tests.

Input is a JSON output from the bitset DFS containing `solutions_head` records.
For each support it checks all non-ambient E11 Wang rows in the cap<=16 binary,
and optionally the analysis mixed-source lower cuts.
"""
from __future__ import annotations
import argparse, json, struct, hashlib, time
from collections import Counter
from pathlib import Path
ROOT=Path('research/research_record')
FULL=ROOT/'workspace/data/domain_dfs_soundness/e11_wang_cap16_rebuilt.bin'
MIX=ROOT/'workspace/data/domain_dfs_soundness/mixed_cuts_gap6_K15_n1440.bin'
OUT=ROOT/'workspace/data/domain_dfs_soundness/rescan_relaxation_supports.json'
WORDS=4; MAGIC=b'E11WANG1'; REC='<BBHQQQQ'; RECSZ=struct.calcsize(REC)

def sha(p):
    h=hashlib.sha256();
    with Path(p).open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()

def bit(ws,p): return (ws[p>>6]>>(p&63))&1

def mask_from_support(S):
    w=[0,0,0,0]
    for p in S: w[p>>6] |= 1<<(p&63)
    return w

def pop4(ws): return sum(int(x).bit_count() for x in ws)

def load_rows(path):
    data=Path(path).read_bytes(); assert data[:8]==MAGIC, path
    n=struct.unpack_from('<I',data,8)[0]; rows=[]; off=12
    for i in range(n):
        cap,dim,res,*ws=struct.unpack_from(REC,data,off); off+=RECSZ
        rows.append((int(cap),int(dim),[int(x) for x in ws]))
    return rows

def load_cuts(path):
    if not path or not Path(path).exists(): return []
    data=Path(path).read_bytes(); assert data[:8]==b'MIXCUT1\0', path
    n=struct.unpack_from('<I',data,8)[0]; off=12; cuts=[]
    for i in range(n):
        K,flags,res=struct.unpack_from('<BBH',data,off); off+=4
        w1=list(struct.unpack_from('<QQQQ',data,off)); off+=32
        w2=list(struct.unpack_from('<QQQQ',data,off)); off+=32
        cuts.append((int(K),[int(x) for x in w1],[int(x) for x in w2]))
    return cuts

def support_rows_from_run(obj):
    sol=[]
    if 'results' in obj:
        for r in obj['results']:
            sol.extend(r.get('solutions_head',[]))
    sol.extend(obj.get('solutions_head',[]))
    # de-duplicate while preserving order
    out=[]; seen=set()
    for s in sol:
        t=tuple(s)
        if t not in seen:
            seen.add(t); out.append(list(s))
    return out

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--run',type=Path,required=True); ap.add_argument('--full',type=Path,default=FULL); ap.add_argument('--mix',type=Path,default=MIX); ap.add_argument('--out',type=Path,default=OUT); ap.add_argument('--max-first-violations',type=int,default=20)
    args=ap.parse_args(); t0=time.time()
    obj=json.loads(args.run.read_text()); supports=support_rows_from_run(obj); rows=load_rows(args.full); cuts=load_cuts(args.mix)
    records=[]; pass_full=0; pass_mixed=0; pass_both=0
    for si,S in enumerate(supports):
        sm=mask_from_support(S); viol=[]; caphist=Counter(); dimhist=Counter(); max_excess=0
        for ri,(cap,dim,rw) in enumerate(rows):
            occ=pop4([sm[k]&rw[k] for k in range(WORDS)])
            if occ>cap:
                if len(viol)<args.max_first_violations:
                    viol.append({'row_index':ri,'cap':cap,'dim':dim,'occupancy':occ,'excess':occ-cap})
                caphist[str(cap)] += 1; dimhist[str(dim)] += 1; max_excess=max(max_excess,occ-cap)
        mv=[]; mixed_pass=True
        for ci,(K,w1,w2) in enumerate(cuts):
            lhs=pop4([sm[k]&w1[k] for k in range(WORDS)]) + pop4([sm[k]&w2[k] for k in range(WORDS)])
            # w2 counts as coefficient 2; w1 includes coefficient>=1 mask from exporter, so lhs=|w1|+|w2|.
            if lhs<K:
                mixed_pass=False
                if len(mv)<args.max_first_violations: mv.append({'cut_index':ci,'K':K,'lhs':lhs,'deficit':K-lhs})
        full_pass=(len(viol)==0 and sum(caphist.values())==0)
        pass_full += int(full_pass); pass_mixed += int(mixed_pass); pass_both += int(full_pass and mixed_pass)
        records.append({'support_index':si,'support':S,'size':len(S),'distinct_size':len(set(S)),'full_wang_pass':full_pass,'full_wang_violation_count':sum(caphist.values()),'full_wang_violation_cap_hist':dict(caphist),'full_wang_violation_dim_hist':dict(dimhist),'max_wang_excess':max_excess,'first_wang_violations':viol,'mixed_pass':mixed_pass,'mixed_violation_count':len(mv) if not mixed_pass else 0,'first_mixed_violations':mv})
    out={'schema':'s0908_rescan_relaxation_supports_v1','run_path':str(args.run),'run_timeout':obj.get('all_complete',None) is False or any(r.get('timeout') for r in obj.get('results',[])),'run_total_solutions_reported':obj.get('total_solutions',obj.get('solutions')),'supports_head_read':len(supports),'full_rows_path':str(args.full),'full_rows_sha256':sha(args.full),'full_rows_count':len(rows),'mixed_cuts_path':str(args.mix),'mixed_cuts_sha256':sha(args.mix),'mixed_cuts_count':len(cuts),'pass_full_wang':pass_full,'pass_mixed_cuts':pass_mixed,'pass_both':pass_both,'records':records,'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
