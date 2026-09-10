#!/usr/bin/env python3
r"""analysis: candidate-local quotient-rank cuts for saturated source sets of size 1 or 2.

For a source set S of saturated contractions and one side B/C, all terms in the
source union have their side factor in W=sum_{q in S} side_space(L(q)).  Hence
for every target t,

    sum_{p: t(p)=1 and q(p)=0 for all q in S} x_p >= rank(pi_W side_space(L(t))).

This script evaluates singleton and pair source sets on known E11-core supports.
"""
from __future__ import annotations
import argparse, json, sys, time
from collections import Counter
from itertools import combinations
from pathlib import Path
from typing import Dict, Sequence, Tuple
import numpy as np
SCRIPTS=Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))
from complete_core_and_transversal import ROOT
from quotient_rank_cuts import build_contractions, count_on_mask, counts_from_A, load_candidate_As, point_mask_for_q, projection_rank_mod_space, sum_basis

OUTDIR=ROOT/'workspace/data/quotient_rank_cuts'
ALLMASK=(1<<255)-1


def eval_candidate_sources(name: str, A: Sequence[int], contractions: Dict[int,dict], masks: Dict[int,int], max_source_size:int=2, max_store:int=100) -> dict:
    counts=counts_from_A(A)
    nonzero=[q for q,c in contractions.items() if int(c['rank'])>0]
    weights={q: count_on_mask(counts,masks[q]) for q in nonzero}
    saturated=[q for q in nonzero if weights[q]==int(contractions[q]['rank'])]
    by_size=Counter(); by_side=Counter(); by_req=Counter(); by_target_sat=Counter(); by_source_rank_pattern=Counter()
    nontriv=0; violations=[]; source_sets_scanned=0
    cache={}
    for k in range(1, max_source_size+1):
        for sources in combinations(saturated,k):
            source_sets_scanned += 1
            union=0
            for q in sources: union |= masks[q]
            for side in ('B','C'):
                side_key='B_space' if side=='B' else 'C_space'
                ck=(side, tuple(sources))
                if ck not in cache:
                    W=sum_basis([contractions[q][side_key] for q in sources],9)
                    cache[ck]=(W,len(W))
                W,Wdim=cache[ck]
                if Wdim>=9: continue
                for target in nonzero:
                    req=projection_rank_mod_space(contractions[target][side_key], W, 9)
                    if req<=0: continue
                    outside=masks[target] & (~union) & ALLMASK
                    lhs=count_on_mask(counts,outside)
                    nontriv += 1
                    if lhs < req:
                        target_sat=(weights[target]==int(contractions[target]['rank']))
                        by_size[k]+=1; by_side[side]+=1; by_req[int(req)]+=1; by_target_sat[str(target_sat)]+=1
                        by_source_rank_pattern[tuple(sorted(int(contractions[q]['rank']) for q in sources))]+=1
                        if len(violations)<max_store:
                            violations.append({
                                'source_size': k,
                                'side': side,
                                'sources': [int(q) for q in sources],
                                'source_ranks': [int(contractions[q]['rank']) for q in sources],
                                'source_weights': [weights[q] for q in sources],
                                'W_dim': Wdim,
                                'target': int(target),
                                'target_rank': int(contractions[target]['rank']),
                                'target_weight': weights[target],
                                'target_saturated': bool(target_sat),
                                'requirement': int(req),
                                'outside_lhs': int(lhs),
                                'outside_point_count': int(outside.bit_count()),
                                'outside_points_in_candidate': [int(p) for p,c in sorted(counts.items()) if c and ((outside>>(int(p)-1))&1)],
                            })
    return {
        'name': name,
        'term_count': len(A),
        'distinct_A_points': len(counts),
        'multiplicity_hist': {str(k):int(v) for k,v in sorted(Counter(counts.values()).items())},
        'saturated_contraction_count': len(saturated),
        'saturated_by_rank': {str(k): int(v) for k,v in sorted(Counter(int(contractions[q]['rank']) for q in saturated).items())},
        'source_sets_scanned': source_sets_scanned,
        'nontrivial_guarded_instances': nontriv,
        'violated_guarded_instances': sum(by_size.values()),
        'violations_by_source_size': {str(k):int(v) for k,v in sorted(by_size.items())},
        'violations_by_side': dict(by_side),
        'violations_by_requirement': {str(k):int(v) for k,v in sorted(by_req.items())},
        'violations_by_target_saturated': dict(by_target_sat),
        'violations_by_source_rank_pattern': {','.join(map(str,k)):int(v) for k,v in sorted(by_source_rank_pattern.items())},
        'violations_head': violations,
    }


def load_v3_long_As() -> Dict[str, list[int]]:
    out={}
    p=ROOT/'workspace/data/core_complete_transversal/core_e11_saturation_v3_complete_long.json'
    if p.exists():
        d=json.loads(p.read_text())
        for r in d.get('rounds',[]):
            if r.get('status') in ('OPTIMAL','FEASIBLE') and 'support' in r:
                out[f"v3_long_round{r['round']}"]=[int(x) for x in r['support']]
    return out


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--max-source-size',type=int,default=2)
    ap.add_argument('--max-store',type=int,default=100)
    ap.add_argument('--include-v3-long',action='store_true')
    ap.add_argument('--out',type=Path,default=OUTDIR/'candidate_source_qcut_scan.json')
    args=ap.parse_args(); args.out.parent.mkdir(parents=True,exist_ok=True)
    t0=time.time()
    T=np.load(ROOT/'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8)%2
    contractions=build_contractions(T); masks={q: point_mask_for_q(q) for q in contractions}
    cands=load_candidate_As()
    if args.include_v3_long: cands.update(load_v3_long_As())
    print(f'Loaded {len(cands)} candidate/control A-lists')
    results=[]
    for i,(name,A) in enumerate(cands.items(),1):
        st=time.time(); rec=eval_candidate_sources(name,A,contractions,masks,args.max_source_size,args.max_store); rec['elapsed_sec']=round(time.time()-st,3); results.append(rec)
        print(json.dumps({'idx':i,'name':name,'sat':rec['saturated_contraction_count'],'srcsets':rec['source_sets_scanned'],'nontriv':rec['nontrivial_guarded_instances'],'viol':rec['violated_guarded_instances'],'by_size':rec['violations_by_source_size'],'by_side':rec['violations_by_side'],'sec':rec['elapsed_sec']},sort_keys=True))
    highlights={r['name']:r for r in results if r['name']=='cn122_E11_core_rank21_genuine' or r['violated_guarded_instances']==0 or r['name'] in ('v2_round5','v2_long_round17','v2_long_round18','v3_long_round12','v3_long_round14')}
    res={'schema':'candidate_source_qcut_scan_v1','field':'F2','core':'E11','max_source_size':args.max_source_size,'candidate_count':len(cands),'rank_distribution':{str(k):int(v) for k,v in sorted(Counter(c['rank'] for c in contractions.values()).items())},'results':results,'highlights':highlights,'elapsed_sec':round(time.time()-t0,3)}
    args.out.write_text(json.dumps(res,indent=2,sort_keys=True)+'\n')
    print(f'Saved {args.out}')
if __name__=='__main__': main()
