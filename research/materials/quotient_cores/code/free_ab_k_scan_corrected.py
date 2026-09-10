#!/usr/bin/env python3
"""analysis corrected free A/B residual search for k-slot retained neighborhoods.

This repairs the quotient remainder issue in the first free-A/B scan.  The
canonical reducer eliminates every pivot bit, so the map
v -> (outside_remainder, E_tag) is linear.  For a retained column span L and
E=pi(col(D)), when a repair block has dim(E)=k, a rank-22 repair with free
A/B slots exists exactly when the images of rank-one columns a\otimes b lying
inside L+E span E.  The script checks that exact case and verifies any witness
by solving K C^T=D and checking all Brent equations.

Blocks with dim(E)<k are recorded separately: they may use cancellation of
outside quotient components and are not ruled out by the E-intersection test.
"""
from __future__ import annotations
import argparse, itertools, json, sys, time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
import residual_repair_geometry as rg  # type: ignore
from ab_residual_block_search import build_final_and_verify  # type: ignore
from free_ab_k3_scan import reduce_with_expr_basis  # type: ignore

OUTDIR=Path('data/free_ab_corrected')

def canonical_reduce(basis: Dict[int, Tuple[int,int]], v: int) -> Tuple[int,int]:
    """Linear normal form modulo the echelon basis; eliminate all pivot bits."""
    x=int(v); tag=0
    for p in sorted(basis.keys(), reverse=True):
        if (x>>p)&1:
            bv,bt=basis[p]
            x ^= bv
            tag ^= bt
    return x, tag

def rank_tags(tags: Iterable[int]) -> int:
    return rg.tags_rank([int(t) for t in tags if int(t)])

def add_tag_basis(basis: List[Tuple[int,int,int]], tag:int, a:int, b:int, target:int) -> bool:
    old=rank_tags(t for t,_a,_b in basis)
    new=rank_tags([t for t,_a,_b in basis]+[tag])
    if new>old:
        basis.append((int(tag),int(a),int(b)))
    return new>=target

def attainable_intersection_basis(tagged_basis: Dict[int,Tuple[int,int]], d:int) -> Tuple[int,List[Tuple[int,int,int]],dict]:
    """Basis for rank-one images that land in L+E, represented by E tags."""
    basis: List[Tuple[int,int,int]]=[]
    stats=Counter(); max_kernel_dim=0
    if d==0:
        return 0,basis,dict(stats)
    for a in range(1,512):
        rem_cols=[]; tag_cols=[]
        for beta in range(9):
            rem,tag=canonical_reduce(tagged_basis, rg.vec_mask9_to_outer81(a,1<<beta))
            rem_cols.append(rem); tag_cols.append(tag)
        deps=reduce_with_expr_basis(rem_cols)
        if deps:
            stats['a_with_kernel']+=1
            max_kernel_dim=max(max_kernel_dim, rank_tags(deps))
        for bmask in deps:
            tag=0
            for beta in range(9):
                if (int(bmask)>>beta)&1:
                    tag ^= tag_cols[beta]
            if tag:
                stats['nonzero_tag_pairs']+=1
                if add_tag_basis(basis,tag,a,int(bmask),d):
                    stats['a_examined_until_span']=a
                    stats['max_kernel_rank_seen']=max_kernel_dim
                    return d,basis,dict(stats)
    stats['a_examined_until_span']=511
    stats['max_kernel_rank_seen']=max_kernel_dim
    return rank_tags(t for t,_a,_b in basis),basis,dict(stats)

def linearity_self_test(tagged_basis: Dict[int,Tuple[int,int]], vectors: Sequence[int]) -> bool:
    # Deterministic small closure sample: r(u+v)=r(u)+r(v).
    for i,u in enumerate(vectors[:30]):
        ru,tu=canonical_reduce(tagged_basis,u)
        for v in vectors[i:i+30]:
            rv,tv=canonical_reduce(tagged_basis,v)
            rw,tw=canonical_reduce(tagged_basis,u^v)
            if rw!=(ru^rv) or tw!=(tu^tv):
                return False
    return True

def scan_source(name:str, terms:Sequence[Tuple[int,int,int]], D_cols:Sequence[int], k:int, stop_on_witness:bool=True) -> dict:
    out={'source':name,'k':k,'delete_records':[],'aggregate':Counter(),'witness_paths':[],'strictly_unsettled_d_lt_k':0}
    for del_idx in range(len(terms)):
        seed_terms=list(terms[:del_idx]+terms[del_idx+1:])
        rec={'delete_index':del_idx,'deleted_A':int(terms[del_idx][0]),'hist':Counter(),'examples':[],'blocks_tested':0}
        for block in itertools.combinations(range(22),k):
            retained=[rg.vec_mask9_to_outer81(a,b) for i,(a,b,_c) in enumerate(seed_terms) if i not in block]
            tagged,E,rank_L,d=rg.build_quotient_basis(retained,D_cols)
            rec['blocks_tested']+=1
            if d>k:
                key=f'd{d}_gt_k'; rec['hist'][key]+=1; out['aggregate'][key]+=1; continue
            # Self-test linearity on D reps and some retained/new elementary columns for first few examples.
            if len(rec['examples'])<2:
                sample=list(D_cols)
                for i,(a,b,_c) in enumerate(seed_terms[:5]):
                    sample.append(rg.vec_mask9_to_outer81(a,b))
                    sample.append(rg.vec_mask9_to_outer81(a,1<<(i%9)))
                if not linearity_self_test(tagged,sample):
                    raise RuntimeError('canonical quotient reducer failed linearity self-test')
            tag_r,basis,stats=attainable_intersection_basis(tagged,d)
            if d<k:
                key=f'd{d}_lt_k_tagrank{tag_r}'
                rec['hist'][key]+=1; out['aggregate'][key]+=1; out['strictly_unsettled_d_lt_k']+=1
                if len(rec['examples'])<12:
                    rec['examples'].append({'block':list(block),'d':d,'rank_L':rank_L,'tag_rank_in_E':tag_r,'status':'d_lt_k_unsettled','basis_head':basis[:min(4,len(basis))],'stats':stats})
                continue
            # d==k exact case.
            if tag_r<d:
                key=f'd{d}_eq_k_tagrank{tag_r}'
                rec['hist'][key]+=1; out['aggregate'][key]+=1
                if len(rec['examples'])<12:
                    rec['examples'].append({'block':list(block),'d':d,'rank_L':rank_L,'tag_rank_in_E':tag_r,'basis_head':basis[:min(4,len(basis))],'stats':stats})
                continue
            A_choices=[]; B_choices=[]
            for j in range(k):
                _tag,a,b=basis[j]
                A_choices.append(a); B_choices.append(b)
            vr=build_final_and_verify(seed_terms,block,A_choices,B_choices)
            detail={'block':list(block),'d':d,'rank_L':rank_L,'tag_rank_in_E':tag_r,'tag_basis':basis[:d],'verify_status':vr['status'],'brent_diff':vr.get('brent_diff'),'stats':stats}
            if vr['status']=='VERIFIED':
                wp=OUTDIR/f'rank22_corrected_freeAB_k{k}_{name}_del{del_idx}_block_'+'_'.join(map(str,block))+'.json'
                wp.write_text(json.dumps({'source':name,'delete_index':del_idx,'block':list(block),**vr},indent=2,sort_keys=True)+'\n')
                out['witness_paths'].append(str(wp)); rec['hist']['verified_witness']+=1; out['aggregate']['verified_witness']+=1; rec['examples'].append(detail)
                if stop_on_witness:
                    out['delete_records'].append({**rec,'hist':dict(rec['hist'])}); out['aggregate']=dict(out['aggregate']); return out
            else:
                rec['hist']['tag_span_but_verify_failed']+=1; out['aggregate']['tag_span_but_verify_failed']+=1
                rec['examples'].append(detail)
        out['delete_records'].append({**rec,'hist':dict(rec['hist'])})
    out['aggregate']=dict(out['aggregate'])
    return out

def positive_controls(sources: Dict[str,Sequence[Tuple[int,int,int]]], D_cols:Sequence[int], source_name:str) -> dict:
    """Recover original deleted blocks in exact d=k rank-23 controls.

    When d<k, the original deleted columns can have quotient components outside E
    that cancel between slots, so the E-intersection/tag-span path is not meant
    to recover them.  Those cases are recorded but are not counted as failures.
    """
    terms=list(sources[source_name])
    recs=[]; ok=0; total=0; skipped_d_lt_k=0
    for k in [1,2,3]:
        for block23 in itertools.combinations(range(23),k):
            retained=[terms[i] for i in range(23) if i not in block23]
            retained_cols=[rg.vec_mask9_to_outer81(a,b) for a,b,_c in retained]
            tagged,E,rank_L,d=rg.build_quotient_basis(retained_cols,D_cols)
            tag_r,basis,stats=attainable_intersection_basis(tagged,d)
            orig_tags=[]; orig_rem_zero=True
            for i in block23:
                rem,tag=canonical_reduce(tagged,rg.vec_mask9_to_outer81(terms[i][0],terms[i][1]))
                orig_rem_zero = orig_rem_zero and (rem==0)
                orig_tags.append(tag)
            if d < k:
                skipped_d_lt_k += 1
                if len(recs)<40:
                    recs.append({'k':k,'block23':list(block23),'rank_L':rank_L,'d':d,'tag_rank_intersection':tag_r,'original_rem_zero':orig_rem_zero,'original_tag_rank':rank_tags(orig_tags),'case':'d_lt_k_not_this_path','stats':stats})
                continue
            total+=1
            good=(d==k and orig_rem_zero and rank_tags(orig_tags)==d)
            if good: ok+=1
            if len(recs)<40 or not good:
                recs.append({'k':k,'block23':list(block23),'rank_L':rank_L,'d':d,'tag_rank_intersection':tag_r,'original_rem_zero':orig_rem_zero,'original_tag_rank':rank_tags(orig_tags),'good':good,'stats':stats})
    return {'source':source_name,'ok_d_eq_k':ok,'total_d_eq_k':total,'all_d_eq_k_ok':ok==total,'skipped_d_lt_k':skipped_d_lt_k,'records_head':recs}

def main():
    global OUTDIR
    ap=argparse.ArgumentParser(); ap.add_argument('--sources',default='cn122_qmm'); ap.add_argument('--k',type=int,default=3); ap.add_argument('--outdir',type=Path,default=OUTDIR); ap.add_argument('--no-stop',action='store_true'); ap.add_argument('--positive-control',action='store_true')
    args=ap.parse_args(); OUTDIR=args.outdir; OUTDIR.mkdir(parents=True,exist_ok=True)
    t0=time.time(); sources=rg.load_sources(); D_cols=rg.D_columns_as_ints(); names=[x.strip() for x in args.sources.split(',') if x.strip()]
    out={'schema':'s0908_free_ab_k_scan_corrected_v1','meaning':'Corrected canonical-quotient free A/B residual scan. d>k is impossible; d=k tag-span is exact; d<k is recorded as unresolved because outside components may cancel.','k':args.k,'results':{},'witness_paths':[],'positive_controls':{}}
    if args.positive_control:
        for name in names:
            print(f'positive control {name}',flush=True)
            pc=positive_controls(sources,D_cols,name)
            out['positive_controls'][name]=pc
            print(json.dumps({'source':name,'ok_d_eq_k':pc['ok_d_eq_k'],'total_d_eq_k':pc['total_d_eq_k'],'all_d_eq_k_ok':pc['all_d_eq_k_ok'],'skipped_d_lt_k':pc['skipped_d_lt_k']},indent=2),flush=True)
            if not pc['all_d_eq_k_ok']:
                raise SystemExit('positive control failed on d=k cases')
    for name in names:
        print(f'=== corrected free A/B scan {name} k={args.k} ===',flush=True)
        rr=scan_source(name,sources[name],D_cols,args.k,stop_on_witness=not args.no_stop)
        out['results'][name]=rr; out['witness_paths'].extend(rr['witness_paths'])
        print(json.dumps({'source':name,'aggregate':rr['aggregate'],'unsettled_d_lt_k':rr.get('strictly_unsettled_d_lt_k'),'witnesses':rr['witness_paths']},indent=2),flush=True)
        if out['witness_paths'] and not args.no_stop: break
    out['elapsed_sec']=time.time()-t0
    op=OUTDIR/f'free_ab_k{args.k}_scan_corrected.json'; op.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(op),'witness_paths':out['witness_paths'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))
if __name__=='__main__': main()
