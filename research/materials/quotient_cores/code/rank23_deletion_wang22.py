#!/usr/bin/env python3
"""Check 22-term A-multisets obtained by deleting one term from known rank-23 schemes.

A rank-23 exact scheme gives a validated point near the rank-22 construction
problem.  Deleting one A-factor is not a tensor algorithm, but if the resulting
22-term A-multiset satisfies all n=22 Wang occupation rows, it is a cheap
candidate for fixed-A Brent completion with different B/C factors.  This script
checks all deletions in one streaming pass through the complete n=22 WANG512
binary.
"""
from __future__ import annotations
import argparse, json, sys, time
from collections import Counter
from pathlib import Path
from typing import List, Tuple

SCRIPT=Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path: sys.path.insert(0,str(SCRIPT))
from pivot_fixed_orbit_lp import load_binary_rows, bit_in, binary_header  # type: ignore
from pivot_fixed_full_wang import parse_multiset_arg  # type: ignore
from extract_known_supports import parse_rank23_txt  # type: ignore

DEFAULT_BINARY=Path('data/pivot_fixed_n22_binary/full_wang512_cap21_len22_all_dim9_allbinding.bin')
FLIP=Path('data/flip_cpd_inspect/src/khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt')
CTRL=Path('data/pivot_fixed/pivot17_rank23_transformed_control.json')
PEER=Path('data/quotient_lift/pivot_fixed/rank2_n23_cn122_control.json')


def load_sources(extra:List[str]):
    sources=[]
    if FLIP.exists():
        terms=parse_rank23_txt(FLIP); sources.append(('flip_rank23_text',[int(a) for a,b,c in terms],str(FLIP)))
    if CTRL.exists():
        sources.append(('pivot17_transformed_rank23',parse_multiset_arg(str(CTRL)),str(CTRL)))
    if PEER.exists():
        sources.append(('peer_cn122_rank23',parse_multiset_arg(str(PEER)),str(PEER)))
    for p in extra:
        sources.append((Path(p).stem,parse_multiset_arg(p),p))
    # Deduplicate by exact A-multiset.
    seen=set(); out=[]
    for name,A,path in sources:
        key=tuple(A)
        if key in seen: continue
        seen.add(key); out.append((name,A,path))
    return out


def check_source(binary:Path, A:List[int], name:str, max_report:int=8):
    n=len(A); assert n==23, (name,n)
    counts=Counter(A)
    # Candidate d deletes index d, with deleted A value A[d].
    viol=[0]*n; excess=[0]*n; max_ex=[0]*n; head=[[] for _ in range(n)]
    tight23=0; rows=0; t0=time.time(); cap_hist=Counter(); dim_hist=Counter()
    for idx,cap,dim,words in load_binary_rows(binary):
        rows+=1; cap_hist[cap]+=1; dim_hist[dim]+=1
        occ=sum(m for p,m in counts.items() if bit_in(words,p))
        # cap is n22 cap. The original rank23 scheme would be tested against cap+1.
        if occ==cap+1: tight23+=1
        for d,a in enumerate(A):
            od=occ-(1 if bit_in(words,int(a)) else 0)
            if od>cap:
                viol[d]+=1; ex=od-cap; excess[d]+=ex; max_ex[d]=max(max_ex[d],ex)
                if len(head[d])<max_report:
                    head[d].append({'row_index':idx,'cap':cap,'dim':dim,'occ_after_delete':od,'excess':ex})
    recs=[]
    for d,a in enumerate(A):
        cand=A[:d]+A[d+1:]
        recs.append({'delete_index':d,'deleted_A':int(a),'candidate_A_multiset':cand,'violation_count':viol[d],'excess_total':excess[d],'max_excess':max_ex[d],'violation_head':head[d],'distinct_count':len(set(cand)),'max_multiplicity':max(Counter(cand).values())})
    recs.sort(key=lambda r:(r['violation_count'],r['excess_total'],r['max_excess'],r['delete_index']))
    return {'name':name,'rank23_A_multiset':[int(x) for x in A],'rows_checked':rows,'cap_hist':dict(sorted((int(k),int(v)) for k,v in cap_hist.items())),'dim_hist':dict(sorted((int(k),int(v)) for k,v in dim_hist.items())),'rank23_tight_against_n23_count':tight23,'best_deletions':recs[:10],'passing_deletions':[r for r in recs if r['violation_count']==0],'elapsed_sec':time.time()-t0}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--binary',type=Path,default=DEFAULT_BINARY); ap.add_argument('--extra',action='append',default=[]); ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args(); t0=time.time(); sources=load_sources(args.extra)
    results=[]
    for name,A,path in sources:
        print(f'checking {name} ({path})',flush=True)
        r=check_source(args.binary,A,name); r['source_path']=path; results.append(r)
        print(f"  passing={len(r['passing_deletions'])} best_viol={r['best_deletions'][0]['violation_count']} deletedA={r['best_deletions'][0]['deleted_A']}",flush=True)
    out={'schema':'rank23_deletion_wang22_v1','binary':binary_header(args.binary),'source_count':len(sources),'results':results,'total_passing':sum(len(r['passing_deletions']) for r in results),'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(args.out),'sources':len(sources),'total_passing':out['total_passing'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))
if __name__=='__main__': main()
