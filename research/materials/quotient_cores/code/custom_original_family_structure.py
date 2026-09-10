#!/usr/bin/env python3
"""analysis: original-source graph-family structure for a custom lift obstruction.

This is the parameterized version of original_family_structure.py.  It
scans every original full-tensor Wang LUT row before cross-family deduplication,
keeps q-avoiding rows whose lift-bit inequality rejects at least one assignment
on the chosen point set, groups them by quotient projection U=pi(W), and reports
whether a single genuine graph family already rejects all lift assignments.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from collections import Counter
from pathlib import Path
from typing import Sequence

ROOT=Path('research/research_record')
OUTDIR=ROOT/'workspace/data/quotient_lift/transport'
OUTDIR.mkdir(parents=True,exist_ok=True)
SCRIPTS=ROOT/'workspace/scripts'
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))
from lift_bit_feasibility_allrows import LUT_PATH, PIVOTS, in_span, load_lut, section_lift, sha_file  # type: ignore
S04=Path('scripts')
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import unpack_basis  # type: ignore

PIVOT=PIVOTS['rank2']

def sha_obj(obj)->str:
    return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def parse_points(s:str)->list[int]:
    return [int(x) for x in s.replace('[','').replace(']','').split(',') if x.strip()]

def load_points(path:Path)->list[int]:
    d=json.loads(path.read_text())
    if d.get('minimized_points'):
        return [int(x) for x in d['minimized_points']]
    if d.get('cut',{}).get('points'):
        return [int(x) for x in d['cut']['points']]
    if d.get('cut_points'):
        return [int(x) for x in d['cut_points']]
    raise ValueError(f'no points in {path}')

def quotient_project(a:int,pivot:int=PIVOT)->int:
    if a==0 or a==pivot: return 0
    h=pivot.bit_length()-1
    if (a>>h)&1: a ^= pivot
    return (a & ((1<<h)-1)) | ((a>>(h+1))<<h)

def subspace_nonzero_points(basis:Sequence[int])->list[int]:
    pts=[0]
    for b in basis:
        pts += [x ^ int(b) for x in pts]
    return [x for x in pts if x]

def quotient_umask_from_basis(basis:Sequence[int])->int:
    m=0
    for v in subspace_nonzero_points(basis):
        p=quotient_project(v)
        if p: m |= 1<<p
    return m

def reject_mask_for_constraint(z:int,o:int,cap:int,n:int)->int:
    rm=0
    for assn in range(1<<n):
        occ=0
        for i in range(n):
            b=(assn>>i)&1
            if ((z>>i)&1) and b==0: occ+=1
            elif ((o>>i)&1) and b==1: occ+=1
        if occ>cap: rm |= 1<<assn
    return rm

def bits(assn:int,n:int)->list[int]: return [(assn>>i)&1 for i in range(n)]

def strip_family(f:dict, universe:int):
    out={k:v for k,v in f.items() if k not in ('reject_mask','unique_ineqs')}
    out['unique_ineq_count']=len(f['unique_ineqs'])
    out['covered_assignments']=int(f['reject_mask'].bit_count())
    out['infeasible_alone']=f['reject_mask']==universe
    out['cap_hist']={str(k):int(v) for k,v in sorted(f['cap_hist'].items())}
    out['active_hist']={str(k):int(v) for k,v in sorted(f['active_hist'].items())}
    out['source_dim_hist']={str(k):int(v) for k,v in sorted(f['source_dim_hist'].items())}
    return out

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--points'); ap.add_argument('--points-json',type=Path); ap.add_argument('--label',default='custom'); ap.add_argument('--top',type=int,default=20)
    args=ap.parse_args()
    A=parse_points(args.points) if args.points else load_points(args.points_json)
    n=len(A); assert n<=20, n
    nassign=1<<n; universe=(1<<nassign)-1
    t0=time.time(); print('Loading LUT...',flush=True); lut,meta=load_lut(LUT_PATH)
    lifts=[(section_lift(p,PIVOT), section_lift(p,PIVOT)^PIVOT) for p in A]
    stats=Counter(); full_cap_hist=Counter(); rel_cap_hist=Counter(); rel_active_hist=Counter(); rel_dim_hist=Counter(); q_viol=[]
    exact_dim_masks=[0]*10; exact_dim_counts=[0]*10; exact_dim_unique=[set() for _ in range(10)]
    reject_cache={}; families={}
    Aset=set(A)
    for idx,(key,lb0) in enumerate(lut.items()):
        if idx and idx%500000==0:
            print(f'  scanned {idx:,}/{len(lut):,}; relevant={stats["relevant_nonq_rows"]:,}; families={len(families):,}; elapsed={time.time()-t0:.1f}s',flush=True)
        basis=unpack_basis(int(key)); d=len(basis); lb=int(lb0); cap=20-lb
        if cap>=20:
            stats['skipped_cap_ge_20']+=1; continue
        if cap<0:
            stats['negative_cap_rows']+=1; continue
        stats['rows_used']+=1; full_cap_hist[cap]+=1
        pairs=tuple((int(b).bit_length()-1,int(b)) for b in basis if b)
        if in_span(PIVOT,pairs):
            stats['q_containing']+=1; occ=1; pts=[]
            for p,(a0,a1) in zip(A,lifts):
                b0=in_span(a0,pairs); b1=in_span(a1,pairs)
                if b0!=b1: raise AssertionError(('q containing mismatch',idx,p,basis,b0,b1))
                if b0: occ+=1; pts.append(p)
            if occ>cap:
                stats['q_violations']+=1
                if len(q_viol)<20: q_viol.append({'idx':idx,'dim':d,'lb':lb,'cap20':cap,'occ_with_q':occ,'projected_points':pts,'basis9':[int(x) for x in basis]})
            continue
        stats['nonq']+=1; z=0; o=0; active=0
        for i,(a0,a1) in enumerate(lifts):
            b0=in_span(a0,pairs); b1=in_span(a1,pairs)
            if b0 and b1: raise AssertionError(('nonq both lifts',idx,A[i],basis))
            if b0: z|=1<<i; active+=1
            elif b1: o|=1<<i; active+=1
        if active==0:
            stats['nonq_no_active']+=1; continue
        stats['nonq_active']+=1
        if active<=cap:
            stats['nonq_tautological']+=1; continue
        stats['relevant_nonq_rows']+=1; rel_cap_hist[cap]+=1; rel_active_hist[active]+=1; rel_dim_hist[d]+=1
        key3=(z,o,cap); rm=reject_cache.get(key3)
        if rm is None:
            rm=reject_mask_for_constraint(z,o,cap,n); reject_cache[key3]=rm
        exact_dim_masks[d] |= rm; exact_dim_counts[d]+=1; exact_dim_unique[d].add(key3)
        umask=quotient_umask_from_basis(basis)
        upts={p for p in range(1,256) if (umask>>p)&1}
        active_points=[p for p in A if p in upts]
        if len(active_points)!=active: raise AssertionError(('active projection mismatch',idx,active,active_points))
        fam=families.get(umask)
        if fam is None:
            fam={'quotient_umask':int(umask),'quotient_dim':int(d),'quotient_size':int((1<<d)-1),'active_points':active_points,'row_count':0,'reject_mask':0,'cap_hist':Counter(),'active_hist':Counter(),'source_dim_hist':Counter(),'row_head':[],'unique_ineqs':set()}
            families[umask]=fam
        fam['row_count']+=1; fam['reject_mask']|=rm; fam['cap_hist'][cap]+=1; fam['active_hist'][active]+=1; fam['source_dim_hist'][d]+=1; fam['unique_ineqs'].add(key3)
        if len(fam['row_head'])<6:
            fam['row_head'].append({'idx':idx,'source_basis9':[int(x) for x in basis],'source_dim':d,'source_lb':lb,'source_cap20':cap,'active':active,'eps0_points':[A[i] for i in range(n) if (z>>i)&1],'eps1_points':[A[i] for i in range(n) if (o>>i)&1],'reject_count':int(rm.bit_count())})
    frecs=[strip_family(f,universe) for f in families.values()]
    frecs.sort(key=lambda f:(not f['infeasible_alone'],-f['covered_assignments'],-f['row_count'],f['quotient_dim'],f['quotient_umask']))
    prefix=0; dim_prefix=[]
    for D in range(1,9):
        prefix |= exact_dim_masks[D]
        survivors=[a for a in range(nassign) if ((prefix>>a)&1)==0]
        dim_prefix.append({'max_source_dim':D,'original_relevant_row_count':int(sum(exact_dim_counts[:D+1])),'unique_inequality_count':int(sum(len(exact_dim_unique[d]) for d in range(D+1))),'covered_assignments':int(prefix.bit_count()),'uncovered_assignments':int(nassign-prefix.bit_count()),'all_covered':prefix==universe,'survivor_assignment_head':[{'assignment_int':int(a),'bits_in_point_order':bits(a,n)} for a in survivors[:16]]})
    union=0
    for f in families.values(): union |= f['reject_mask']
    single=[f for f in frecs if f['infeasible_alone']]
    top=frecs[:args.top]
    out={'schema':'s0908_custom_original_family_structure_v1','source_lut':str(LUT_PATH),'source_lut_sha256':sha_file(LUT_PATH),'lut_coverage_ok':meta.get('coverage_ok'),'pivot_name':'rank2','pivot':PIVOT,'label':args.label,'points':A,'point_count':n,'assignment_count':nassign,'stats':{str(k):int(v) for k,v in sorted(stats.items())},'full_cap_hist_used':{str(k):int(v) for k,v in sorted(full_cap_hist.items())},'relevant_original_cap_hist':{str(k):int(v) for k,v in sorted(rel_cap_hist.items())},'relevant_original_active_hist':{str(k):int(v) for k,v in sorted(rel_active_hist.items())},'relevant_original_dim_hist':{str(k):int(v) for k,v in sorted(rel_dim_hist.items())},'unique_rejecting_inequality_count_global':len(reject_cache),'q_containing_violation_count':int(stats.get('q_violations',0)),'q_containing_violations_head':q_viol,'original_family_count_with_rejecting_rows':len(frecs),'single_original_graph_family_infeasible_count':len(single),'single_original_graph_family_infeasible_head':single[:20],'top_original_graph_families_by_assignment_coverage':top,'dimension_prefix_cover_original_rows':dim_prefix,'global_union_all_original_graph_rows':{'covered_assignments':int(union.bit_count()),'all_covered':union==universe,'uncovered_assignments':int(nassign-union.bit_count())},'interpretation':{'family_mechanism':'single original graph family exists' if single else 'no single original graph family rejects all assignments; obstruction needs multiple quotient projections for this point set','dimension_prefix_status':'computed from original rows before cross-family deduplication'},'top_original_graph_families_sha256':sha_obj(top),'elapsed_sec':time.time()-t0}
    outpath=OUTDIR/f'original_family_structure_{args.label}.json'
    outpath.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','label':args.label,'points':A,'relevant_original_rows':out['stats'].get('relevant_nonq_rows'),'unique_rejecting_inequalities':out['unique_rejecting_inequality_count_global'],'families':out['original_family_count_with_rejecting_rows'],'single_family_infeasible_count':out['single_original_graph_family_infeasible_count'],'dimension_prefix_cover':dim_prefix,'global_all_covered':out['global_union_all_original_graph_rows'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True),flush=True)
    print('saved',outpath,flush=True)

if __name__=='__main__': main()
