#!/usr/bin/env python3
"""analysis: generalized free A/B residual search for k-slot retained neighborhoods.

For a verified rank-23 scheme, delete one term and choose k slots among the
remaining 22 whose A and B factors may be replaced arbitrarily.  Retained old
columns form L.  Let E=pi(col(D)) modulo L.  For arbitrary free A/B slots, each
slot has the same attainable set: images in E of rank-one 9x9 matrices
a\otimes b.  If this attainable set spans E and k>=dim(E), the script lifts
representatives, solves C, and verifies the Brent equations.  If it does not
span E, the selected retained-column neighborhood is exactly impossible.
"""
from __future__ import annotations
import argparse, itertools, json, sys, time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
import residual_repair_geometry as rg  # type: ignore
from ab_residual_block_search import build_final_and_verify  # type: ignore
from free_ab_k3_scan import reduce_with_expr_basis, add_tag_to_basis  # type: ignore

OUTDIR=Path('data/free_ab_k')

def attainable_basis(tagged_basis, d:int):
    basis=[]; a_examined=0; nonzero_pairs=0
    if d==0:
        return 0, [], 0, 0
    for a in range(1,512):
        a_examined+=1
        rem_cols=[]; tag_cols=[]
        for beta in range(9):
            rem,tag=rg.reduce_by_basis(tagged_basis, rg.vec_mask9_to_outer81(a,1<<beta))
            rem_cols.append(rem); tag_cols.append(tag)
        deps=reduce_with_expr_basis(rem_cols)
        for bmask in deps:
            tag=0
            for beta in range(9):
                if (bmask>>beta)&1: tag^=tag_cols[beta]
            if tag:
                nonzero_pairs+=1
                if add_tag_to_basis(basis,tag,a,bmask,d):
                    return d,basis,a_examined,nonzero_pairs
    return rg.tags_rank([t for t,_a,_b in basis]),basis,a_examined,nonzero_pairs

def scan_source(name:str, terms:Sequence[Tuple[int,int,int]], D_cols:Sequence[int], k:int, stop_on_witness:bool=True):
    out={'source':name,'k':k,'delete_records':[],'aggregate':Counter(),'witness_paths':[]}
    for del_idx in range(len(terms)):
        seed_terms=list(terms[:del_idx]+terms[del_idx+1:])
        rec={'delete_index':del_idx,'deleted_A':int(terms[del_idx][0]),'hist':Counter(),'examples':[],'blocks_tested':0}
        for block in itertools.combinations(range(22),k):
            retained=[rg.vec_mask9_to_outer81(a,b) for i,(a,b,_c) in enumerate(seed_terms) if i not in block]
            tagged,E,rank_L,d=rg.build_quotient_basis(retained,D_cols)
            rec['blocks_tested']+=1
            if d>k:
                rec['hist'][f'd{d}_gt_k']+=1; out['aggregate'][f'd{d}_gt_k']+=1; continue
            tr,basis,a_examined,npairs=attainable_basis(tagged,d)
            if tr<d:
                key=f'd{d}_tagrank{tr}'
                rec['hist'][key]+=1; out['aggregate'][key]+=1
                if len(rec['examples'])<20:
                    rec['examples'].append({'block':list(block),'d':d,'rank_L':rank_L,'tag_rank':tr,'tag_basis':basis,'a_examined':a_examined,'nonzero_pairs_seen':npairs})
                continue
            # Construct using first d basis vectors, fill remaining repair slots with old slot factors.
            A_choices=[]; B_choices=[]
            for j in range(k):
                if j<d:
                    _tag,a,b=basis[j]; A_choices.append(a); B_choices.append(b)
                else:
                    slot=block[j]; A_choices.append(seed_terms[slot][0]); B_choices.append(seed_terms[slot][1])
            vr=build_final_and_verify(seed_terms,block,A_choices,B_choices)
            detail={'block':list(block),'d':d,'rank_L':rank_L,'tag_rank':tr,'tag_basis':basis[:d],'verify_status':vr['status'],'brent_diff':vr.get('brent_diff')}
            if vr['status']=='VERIFIED':
                wp=OUTDIR/f'rank22_freeAB_k{k}_{name}_del{del_idx}_block_'+'_'.join(map(str,block))+'.json'
                wp.write_text(json.dumps({'source':name,'delete_index':del_idx,'block':list(block),**vr},indent=2,sort_keys=True)+'\n')
                out['witness_paths'].append(str(wp)); rec['hist']['verified_witness']+=1; out['aggregate']['verified_witness']+=1; rec['examples'].append(detail)
                if stop_on_witness:
                    out['delete_records'].append({**rec,'hist':dict(rec['hist'])}); out['aggregate']=dict(out['aggregate']); return out
            else:
                rec['hist']['tag_full_but_verify_failed']+=1; out['aggregate']['tag_full_but_verify_failed']+=1
                if len(rec['examples'])<20: rec['examples'].append(detail)
        out['delete_records'].append({**rec,'hist':dict(rec['hist'])})
    out['aggregate']=dict(out['aggregate']); return out

def main():
    global OUTDIR
    ap=argparse.ArgumentParser(); ap.add_argument('--sources',default='cn122_qmm'); ap.add_argument('--k',type=int,default=4); ap.add_argument('--outdir',type=Path,default=OUTDIR); ap.add_argument('--no-stop',action='store_true')
    args=ap.parse_args(); OUTDIR=args.outdir; OUTDIR.mkdir(parents=True,exist_ok=True)
    t0=time.time(); sources=rg.load_sources(); D_cols=rg.D_columns_as_ints(); names=[x.strip() for x in args.sources.split(',') if x.strip()]
    out={'schema':'s0908_free_ab_k_scan_v1','meaning':'Exact free-A/B retained-neighborhood residual search. A witness is verified on Brent equations; no witness only excludes the scanned local neighborhoods.','k':args.k,'results':{},'witness_paths':[]}
    for name in names:
        print(f'=== scan {name} k={args.k} ===',flush=True)
        rr=scan_source(name,sources[name],D_cols,args.k,stop_on_witness=not args.no_stop)
        out['results'][name]=rr; out['witness_paths'].extend(rr['witness_paths'])
        print(json.dumps({'source':name,'aggregate':rr['aggregate'],'witnesses':rr['witness_paths']},indent=2),flush=True)
        if out['witness_paths'] and not args.no_stop: break
    out['elapsed_sec']=time.time()-t0
    op=OUTDIR/f'free_ab_k{args.k}_scan.json'; op.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(op),'witness_paths':out['witness_paths'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))
if __name__=='__main__': main()
