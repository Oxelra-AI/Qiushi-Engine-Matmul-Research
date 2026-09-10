#!/usr/bin/env python3
"""analysis: explain the corrected 12-point lift-bit obstruction.

Given the analysis pivot-17 cut A, rebuild the exact all-Wang lift-bit
constraints in the corrected high-pivot coordinates, then ask what kind of
constraint family makes the lift bits impossible.

For each non-q full Wang row W we record the local inequality on lift bits
  #{p in A : chosen lift of p lies in W} <= cap20(W).
Rows are grouped by their quotient projection U=pi(W).  A single U gives the
usual graph-family constraints over U; multiple U's interact through shared
lift variables.  The script computes:
  * dimension and active-size coverage of the constraints;
  * whether any single graph family is already lift-bit infeasible;
  * a small family cover and a small row cover of all 2^12 assignments;
  * witnesses/certificates for the selected row cover.

This is an explanatory/reuse asset, not a complete rank lower-bound proof.
"""
from __future__ import annotations
import hashlib, json, sys, time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable

ROOT=Path('research/research_record')
OUT=ROOT/'workspace/data/quotient_lift/obstruction_structure.json'
SCRIPTS=ROOT/'workspace/scripts'
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0,str(SCRIPTS))
from lift_bit_feasibility_allrows import (  # type: ignore
    LUT_PATH, PIVOTS, build_constraints_all, load_lut, sha_file, section_lift
)
S04=Path('scripts')
if str(S04) not in sys.path:
    sys.path.insert(0,str(S04))
from wang_capacity_lazy import rref_basis, pack_basis  # type: ignore

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:
    cp_model=None

PIVOT=PIVOTS['rank2']
A=[9,33,99,160,184,189,192,209,215,224,249,254]
NASSIGN=1<<len(A)
UNIVERSE=(1<<NASSIGN)-1


def sha_obj(obj)->str:
    return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def quotient_project(a:int,pivot:int=PIVOT)->int:
    if a==0 or a==pivot:
        return 0
    h=pivot.bit_length()-1
    if (a>>h)&1:
        a ^= pivot
    low=a & ((1<<h)-1)
    high=(a>>(h+1))<<h
    return low|high


def quotient_mask_from_basis9(basis:Iterable[int], pivot:int=PIVOT)->int:
    bs=list(map(int,basis)); mask=0
    for m in range(1,1<<len(bs)):
        v=0
        for i,b in enumerate(bs):
            if (m>>i)&1:
                v ^= b
        p=quotient_project(v,pivot)
        if p:
            mask |= 1<<p
    return mask


def points_from_mask(mask:int)->list[int]:
    return [p for p in range(1,256) if (mask>>p)&1]


def reject_mask_for_constraint(z:int,o:int,cap:int,n:int=len(A))->int:
    # bit assignment assn is 1 iff rejected by this inequality.
    rm=0
    active=(z|o)
    for assn in range(1<<n):
        occ=0
        zz=z; oo=o
        # n=12; simple loop is fine.
        for i in range(n):
            b=(assn>>i)&1
            if ((zz>>i)&1) and b==0:
                occ+=1
            elif ((oo>>i)&1) and b==1:
                occ+=1
        if occ>cap:
            rm |= 1<<assn
    return rm


def assn_bits(assn:int,n:int=len(A))->list[int]:
    return [(assn>>i)&1 for i in range(n)]


def summarize_constraints(constraints, sources):
    recs=[]; family={}  # Umask -> aggregate
    for cid,(z,o,cap) in enumerate(constraints):
        src=sources[(z,o)]
        umask=quotient_mask_from_basis9(src['basis'])
        active=(z|o).bit_count()
        u_cut_points=[A[i] for i in range(len(A)) if ((z|o)>>i)&1]
        # Sanity: active points should equal A cap U.
        upts=set(points_from_mask(umask))
        if set(u_cut_points)!={p for p in A if p in upts}:
            raise AssertionError(('active mismatch',cid,u_cut_points,sorted(p for p in A if p in upts),src))
        rmask=reject_mask_for_constraint(z,o,cap)
        rec={'cid':cid,'z':int(z),'o':int(o),'cap':int(cap),'active':int(active),'reject_count':int(rmask.bit_count()),'reject_mask':rmask,'source_dim':int(src['dim']),'source_lb':int(src['lb']),'source_cap20':int(src['cap20']),'source_basis9':[int(x) for x in src['basis']],'quotient_umask':int(umask),'quotient_dim':int(src['dim']),'active_points':u_cut_points,'eps0_points':[A[i] for i in range(len(A)) if (z>>i)&1],'eps1_points':[A[i] for i in range(len(A)) if (o>>i)&1]}
        recs.append(rec)
        f=family.setdefault(umask,{'quotient_umask':umask,'quotient_dim':int(src['dim']),'quotient_size':(1<<int(src['dim']))-1,'cut_points':[p for p in A if p in upts],'constraint_ids':[],'reject_mask':0,'cap_hist':Counter(),'active_hist':Counter(),'source_dim_hist':Counter()})
        f['constraint_ids'].append(cid); f['reject_mask'] |= rmask; f['cap_hist'][int(cap)]+=1; f['active_hist'][int(active)]+=1; f['source_dim_hist'][int(src['dim'])]+=1
    # normalize families
    fams=[]
    for f in family.values():
        fams.append({**{k:v for k,v in f.items() if k not in ('cap_hist','active_hist','source_dim_hist')},'constraint_count':len(f['constraint_ids']),'covered_assignments':int(f['reject_mask'].bit_count()),'infeasible_alone':f['reject_mask']==UNIVERSE,'cap_hist':dict(sorted((int(k),int(v)) for k,v in f['cap_hist'].items())),'active_hist':dict(sorted((int(k),int(v)) for k,v in f['active_hist'].items())),'source_dim_hist':dict(sorted((int(k),int(v)) for k,v in f['source_dim_hist'].items()))})
    fams.sort(key=lambda f:(-f['covered_assignments'], -f['constraint_count'], f['quotient_dim'], f['quotient_umask']))
    return recs,fams


def greedy_cover(items, universe:int=UNIVERSE, max_steps:int|None=None):
    # items: list dict with reject_mask and id-like fields.
    covered=0; chosen=[]; remaining=set(range(len(items)))
    while covered!=universe and remaining:
        best=None; best_gain=-1
        inv=universe ^ covered
        for i in list(remaining):
            gain=(items[i]['reject_mask'] & inv).bit_count()
            if gain>best_gain:
                best=i; best_gain=gain
        if best is None or best_gain<=0:
            break
        chosen.append(best); covered |= items[best]['reject_mask']; remaining.remove(best)
        if max_steps and len(chosen)>=max_steps:
            break
    # deletion minimize in reverse repeatedly.
    changed=True
    while changed:
        changed=False
        for i in list(chosen):
            cov=0
            for j in chosen:
                if j!=i: cov |= items[j]['reject_mask']
            if cov==universe:
                chosen.remove(i); changed=True
    return chosen, covered==universe


def exact_min_cover_cp(items, time_limit=60.0, upper_bound:int|None=None):
    if cp_model is None:
        return {'status':'UNAVAILABLE'}
    model=cp_model.CpModel(); y=[model.NewBoolVar(f'y_{i}') for i in range(len(items))]
    # Upper bound from greedy helps.
    if upper_bound is not None:
        model.Add(sum(y)<=upper_bound)
    # For every assignment, at least one chosen item rejects it.
    coverers=[[] for _ in range(NASSIGN)]
    for i,it in enumerate(items):
        m=it['reject_mask']
        while m:
            lsb=m & -m; a=lsb.bit_length()-1; coverers[a].append(y[i]); m^=lsb
    for a,lst in enumerate(coverers):
        if not lst:
            return {'status':'UNCOVERED_ASSIGNMENT','assignment':a,'bits':assn_bits(a)}
        model.Add(sum(lst)>=1)
    model.Minimize(sum(y))
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(time_limit); solver.parameters.num_search_workers=8
    status=solver.Solve(model); sname=solver.StatusName(status)
    selected=[]
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        selected=[i for i,v in enumerate(y) if solver.Value(v)]
    return {'status':sname,'objective':len(selected) if selected else None,'best_bound':solver.BestObjectiveBound() if status in (cp_model.OPTIMAL,cp_model.FEASIBLE,cp_model.UNKNOWN) else None,'wall_time':solver.WallTime(),'conflicts':solver.NumConflicts(),'branches':solver.NumBranches(),'selected_indices':selected}


def selected_constraint_certificate(recs, selected):
    # For each assignment choose the first selected constraint that rejects it.
    cert=[]; use=Counter(); covered=0
    for assn in range(NASSIGN):
        found=None
        for local_idx,cid in enumerate(selected):
            if (recs[cid]['reject_mask']>>assn)&1:
                found=cid; break
        if found is None:
            raise AssertionError(('selected constraints do not cover',assn))
        use[found]+=1; covered |= 1<<assn
        if len(cert)<64:  # keep a readable head; full cover stored by selected rows themselves.
            r=recs[found]
            cert.append({'assignment_int':assn,'bits':assn_bits(assn),'constraint_id':found,'cap':r['cap'],'active':r['active'],'source_dim':r['source_dim'],'source_lb':r['source_lb'],'source_basis9':r['source_basis9'],'eps0_points':r['eps0_points'],'eps1_points':r['eps1_points']})
    return {'assignments_covered':covered.bit_count(),'all_assignments_covered':covered==UNIVERSE,'constraint_use_hist_top':[{'constraint_id':int(k),'count':int(v)} for k,v in use.most_common()],'certificate_head':cert,'certificate_head_only':True}


def main():
    t0=time.time(); print('Loading LUT...',flush=True); lut,meta=load_lut(LUT_PATH)
    print('Building all corrected constraints for 12-point cut...',flush=True)
    bundle=build_constraints_all(lut,PIVOT,A,max_dim=9,progress=0)
    constraints=bundle['constraints']; sources=bundle['source']
    print(f'constraints {len(constraints)}',flush=True)
    recs,fams=summarize_constraints(constraints,sources)
    all_mask=0
    for r in recs: all_mask |= r['reject_mask']
    dim_cover=[]
    for D in range(1,9):
        m=0; n=0
        for r in recs:
            if r['source_dim']<=D:
                m |= r['reject_mask']; n+=1
        dim_cover.append({'max_source_dim':D,'constraint_count':n,'covered_assignments':m.bit_count(),'all_covered':m==UNIVERSE})
    single_infeasible=[f for f in fams if f['infeasible_alone']]
    print(f'families {len(fams)}, single infeasible {len(single_infeasible)}',flush=True)
    # Greedy and CP covers.
    gcon, gok=greedy_cover(recs)
    print(f'greedy constraints {len(gcon)} ok={gok}',flush=True)
    gcf=selected_constraint_certificate(recs,gcon) if gok else None
    # For exact constraint cover, use greedy upper bound and a modest time limit.
    exact_con=exact_min_cover_cp(recs,time_limit=60,upper_bound=len(gcon) if gok else None)
    print('exact/CP constraint cover', {k:exact_con.get(k) for k in ['status','objective','best_bound','wall_time']}, flush=True)
    chosen_con=exact_con['selected_indices'] if exact_con.get('selected_indices') else gcon
    chosen_con_cert=selected_constraint_certificate(recs,chosen_con)
    # Family cover.
    gfam,gfok=greedy_cover(fams)
    print(f'greedy families {len(gfam)} ok={gfok}',flush=True)
    exact_fam=exact_min_cover_cp(fams,time_limit=60,upper_bound=len(gfam) if gfok else None)
    print('exact/CP family cover', {k:exact_fam.get(k) for k in ['status','objective','best_bound','wall_time']}, flush=True)
    chosen_fam=exact_fam['selected_indices'] if exact_fam.get('selected_indices') else gfam
    # Map chosen rows/families to readable records, dropping giant reject masks.
    def strip_reject(r):
        return {k:v for k,v in r.items() if k!='reject_mask'}
    chosen_constraints=[strip_reject(recs[i]) for i in chosen_con]
    chosen_family_records=[]
    for idx in chosen_fam:
        f=fams[idx]
        fr={k:v for k,v in f.items() if k!='reject_mask'}
        fr['constraint_head']=[strip_reject(recs[cid]) for cid in f['constraint_ids'][:12]]
        chosen_family_records.append(fr)
    out={'schema':'s0908_lift_obstruction_structure_v1','source_lut':str(LUT_PATH),'source_lut_sha256':sha_file(LUT_PATH),'lut_coverage_ok':meta.get('coverage_ok'),'pivot_name':'rank2','pivot':PIVOT,'cut_points':A,'cut_rhs':len(A)-1,'constraint_count':len(constraints),'builder_stats':bundle['stats'],'dedup_cap_hist':bundle['dedup_cap_hist'],'active_hist_nonq':bundle['active_hist_nonq'],'global_unsat_by_union':all_mask==UNIVERSE,'dimension_prefix_cover':dim_cover,'family_count':len(fams),'single_graph_family_infeasible_count':len(single_infeasible),'single_graph_family_infeasible_head':[{k:v for k,v in f.items() if k!='reject_mask'} for f in single_infeasible[:20]],'top_families_by_assignment_coverage':[{k:v for k,v in f.items() if k!='reject_mask'} for f in fams[:20]],'greedy_constraint_cover_size':len(gcon),'greedy_constraint_cover_ok':gok,'greedy_constraint_cover_certificate':gcf,'cp_constraint_cover':{k:v for k,v in exact_con.items() if k!='selected_indices'},'chosen_constraint_cover_source':'cp' if exact_con.get('selected_indices') else 'greedy','chosen_constraint_cover_size':len(chosen_con),'chosen_constraint_ids':[int(i) for i in chosen_con],'chosen_constraint_cover':chosen_constraints,'chosen_constraint_cover_certificate':chosen_con_cert,'greedy_family_cover_size':len(gfam),'greedy_family_cover_ok':gfok,'cp_family_cover':{k:v for k,v in exact_fam.items() if k!='selected_indices'},'chosen_family_cover_source':'cp' if exact_fam.get('selected_indices') else 'greedy','chosen_family_cover_size':len(chosen_fam),'chosen_family_indices':[int(i) for i in chosen_fam],'chosen_family_cover':chosen_family_records,'interpretation':{'single_family_vs_overlap':'single graph-family obstruction' if single_infeasible else 'no single quotient graph family covers all assignments; infeasibility is caused by overlapping lift-bit requirements across multiple quotient subspaces','averaging_status':'analysis showed graph-family averaging gives zero stronger pure occupation rows, so this file examines exact lift-bit relations rather than averaged support rows.'},'elapsed_sec':time.time()-t0}
    out['chosen_constraint_cover_sha256']=sha_obj(out['chosen_constraint_cover'])
    out['chosen_family_cover_sha256']=sha_obj(out['chosen_family_cover'])
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','constraints':len(constraints),'families':len(fams),'single_family_infeasible':len(single_infeasible),'dim_cover':dim_cover,'chosen_constraint_cover_size':len(chosen_con),'chosen_constraint_source':out['chosen_constraint_cover_source'],'chosen_family_cover_size':len(chosen_fam),'chosen_family_source':out['chosen_family_cover_source'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True),flush=True)
    print('saved',OUT,flush=True)

if __name__=='__main__':
    main()
