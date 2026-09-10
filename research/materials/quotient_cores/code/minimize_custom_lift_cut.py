#!/usr/bin/env python3
"""analysis: lift-bit feasibility and minimization for a custom quotient support.

Input is either an explicit comma-separated support or the first fully admissible
support from a CEGAR JSON.  The script rebuilds all full-Wang lift-bit constraints
in the corrected analysis high-pivot coordinates.  If the support is infeasible,
it greedily minimizes to an inclusion-minimal lift-incompatible subset and, when
small enough, writes an all-assignment witness certificate analogous to analysis.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from collections import Counter
from pathlib import Path
from typing import Sequence

ROOT=Path('research/research_record')
OUTDIR=ROOT/'workspace/data/quotient_lift/transport'
OUTDIR.mkdir(parents=True,exist_ok=True)
SCRIPT_DIR=ROOT/'workspace/scripts'
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
from lift_bit_feasibility_allrows import (  # type: ignore
    LUT_PATH, PIVOTS, build_constraints_all, load_lut, sha_file
)

def sha_obj(obj)->str:
    return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def parse_support(s:str)->list[int]:
    return [int(x) for x in s.replace('[','').replace(']','').split(',') if x.strip()]

def load_support_from_json(path:Path)->list[int]:
    d=json.loads(path.read_text())
    # Prefer first round marked fully admissible.
    for r in d.get('rounds',[]):
        if r.get('fully_quotient_wang_admissible') and r.get('support'):
            return [int(x) for x in r['support']]
    # Else use first support-looking round.
    for r in d.get('rounds',[]):
        if r.get('support'):
            return [int(x) for x in r['support']]
    raise ValueError(f'no support found in {path}')

def restrict_constraints(constraints, keep_orig_indices):
    pos={old:i for i,old in enumerate(keep_orig_indices)}
    best={}
    for z,o,cap in constraints:
        zz=0; oo=0; active=0
        for old,new in pos.items():
            if (z>>old)&1:
                zz|=1<<new; active+=1
            elif (o>>old)&1:
                oo|=1<<new; active+=1
        if active>cap:
            key=(zz,oo)
            if key not in best or cap<best[key]: best[key]=cap
    out=[(z,o,c) for (z,o),c in best.items()]
    out.sort(key=lambda t:(t[2],(t[0]|t[1]).bit_count(),t[0],t[1]))
    return out

def feasible_dfs(constraints,m,find_all=False):
    inc_count=[]
    for v in range(m):
        c=sum(1 for z,o,cap in constraints if ((z|o)>>v)&1)
        inc_count.append((c,v))
    order=[v for c,v in sorted(inc_count,reverse=True)]
    inc=[[[],[]] for _ in range(m)]
    for ci,(z,o,cap) in enumerate(constraints):
        for v in range(m):
            if (z>>v)&1: inc[v][0].append(ci)
            if (o>>v)&1: inc[v][1].append(ci)
    occ=[0]*len(constraints); assign=[None]*m
    stats={'nodes':0,'leaves':0,'prunes':0,'solutions':0,'max_depth':0}; prune_depth=Counter(); first_solution=None; first_conflicts=[]
    t0=time.time()
    def rec(depth):
        nonlocal first_solution
        stats['nodes']+=1; stats['max_depth']=max(stats['max_depth'],depth)
        if depth==m:
            stats['leaves']+=1; stats['solutions']+=1
            if first_solution is None: first_solution=[int(x) for x in assign]
            return not find_all
        v=order[depth]
        for val in (0,1):
            touched=[]; bad=None
            for ci in inc[v][val]:
                occ[ci]+=1; touched.append(ci)
                if occ[ci]>constraints[ci][2]: bad=ci; break
            stop=False
            if bad is None:
                assign[v]=val; stop=rec(depth+1); assign[v]=None
            else:
                stats['prunes']+=1; prune_depth[depth+1]+=1
                if len(first_conflicts)<30:
                    z,o,cap=constraints[bad]
                    first_conflicts.append({'depth':depth+1,'var_compact':v,'value':val,'constraint_id':bad,'cap':cap,'active':(z|o).bit_count(),'eps0_compact':[i for i in range(m) if (z>>i)&1],'eps1_compact':[i for i in range(m) if (o>>i)&1]})
            for ci in reversed(touched): occ[ci]-=1
            if stop: return True
        return False
    rec(0); stats['elapsed_sec']=time.time()-t0
    return {'feasible':stats['solutions']>0,'stats':stats,'order':order,'first_solution':first_solution,'first_conflicts':first_conflicts,'prune_depth':{str(k):int(v) for k,v in sorted(prune_depth.items())}}

def occupation_for_assignment(zmask:int,omask:int,assignment:int,n:int)->int:
    occ=0
    for i in range(n):
        b=(assignment>>i)&1
        if ((zmask>>i)&1) and b==0: occ+=1
        if ((omask>>i)&1) and b==1: occ+=1
    return occ

def make_assignment_certificate(points, constraints, source_map, max_assignments:int=1<<16):
    n=len(points)
    if (1<<n)>max_assignments:
        return {'made':False,'reason':f'{1<<n} assignments exceeds limit {max_assignments}'}
    cert=[]; use=Counter(); cap_hist=Counter(); dim_hist=Counter(); active_hist=Counter(); max_excess=0
    for assn in range(1<<n):
        found=None
        for cid,(z,o,cap) in enumerate(constraints):
            occ=occupation_for_assignment(z,o,assn,n)
            if occ>cap:
                src=source_map.get((z,o),{})
                found={'assignment_int':assn,'bits_in_point_order':[(assn>>i)&1 for i in range(n)],'violating_constraint_id':cid,'cap':int(cap),'occ':int(occ),'excess':int(occ-cap),'active':int((z|o).bit_count()),'eps0_points':[points[i] for i in range(n) if (z>>i)&1],'eps1_points':[points[i] for i in range(n) if (o>>i)&1],'source_basis9':[int(x) for x in src.get('basis',[])],'source_dim':int(src.get('dim',-1)),'source_lb':int(src.get('lb',-1)),'source_cap20':int(src.get('cap20',cap)),'source_lut_index_in_iteration':int(src.get('idx',-1))}
                use[cid]+=1; cap_hist[cap]+=1; dim_hist[found['source_dim']]+=1; active_hist[(z|o).bit_count()]+=1; max_excess=max(max_excess,occ-cap)
                break
        if found is None: raise AssertionError(('assignment not certified',assn))
        cert.append(found)
    return {'made':True,'assignment_count':len(cert),'all_assignments_certified':True,'max_excess_in_chosen_violations':max_excess,'chosen_violation_cap_hist':{str(k):int(v) for k,v in sorted(cap_hist.items())},'chosen_violation_dim_hist':{str(k):int(v) for k,v in sorted(dim_hist.items())},'chosen_violation_active_hist':{str(k):int(v) for k,v in sorted(active_hist.items())},'distinct_constraints_used':len(use),'top_constraints_used':[{'constraint_id':int(k),'count':int(v)} for k,v in use.most_common(20)],'certificate':cert,'certificate_sha256':sha_obj(cert)}

def compact_sources_for_restricted(full_source, full_constraints, keep):
    # Build a best source map for restricted constraints matching restrict_constraints's best caps.
    pos={old:i for i,old in enumerate(keep)}; best={}
    for z,o,cap in full_constraints:
        zz=0; oo=0; active=0
        for old,new in pos.items():
            if (z>>old)&1: zz|=1<<new; active+=1
            elif (o>>old)&1: oo|=1<<new; active+=1
        if active>cap:
            key=(zz,oo)
            if key not in best or cap<best[key][0]: best[key]=(cap, full_source.get((z,o),{}))
    return {k:v[1] for k,v in best.items()}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--pivot-name',choices=['rank2','rank3'],default='rank2'); ap.add_argument('--support'); ap.add_argument('--support-json',type=Path); ap.add_argument('--label',default='custom'); ap.add_argument('--cert-limit',type=int,default=65536)
    args=ap.parse_args()
    if args.support: support=parse_support(args.support)
    elif args.support_json: support=load_support_from_json(args.support_json)
    else: raise SystemExit('give --support or --support-json')
    pivot=PIVOTS[args.pivot_name]
    t0=time.time(); print('Loading LUT...',flush=True); lut,meta=load_lut(LUT_PATH)
    print(f'Building all corrected constraints for {args.label}, support size {len(support)}...',flush=True)
    bundle=build_constraints_all(lut,pivot,support,max_dim=9,progress=0)
    full_constraints=bundle['constraints']
    initial=feasible_dfs(full_constraints,len(support),find_all=False)
    print('initial feasible?',initial['feasible'],initial['stats'],flush=True)
    current=list(range(len(support))); history=[]; minimized=None; final=None; deletions=[]; cert=None
    if not initial['feasible']:
        changed=True
        while changed:
            changed=False
            for old in list(current):
                trial=[x for x in current if x!=old]
                rc=restrict_constraints(full_constraints,trial)
                res=feasible_dfs(rc,len(trial),find_all=False)
                history.append({'try_remove_index':old,'try_remove_point':support[old],'remaining_points':[support[i] for i in trial],'constraint_count':len(rc),'feasible_after_removal':res['feasible'],'stats':res['stats']})
                print(f"try remove {support[old]} -> feasible={res['feasible']} constraints={len(rc)} nodes={res['stats']['nodes']}",flush=True)
                if not res['feasible']:
                    current=trial; changed=True
                    print('  removed; current', [support[i] for i in current], flush=True)
                    break
        minimized=[support[i] for i in current]
        final_constraints=restrict_constraints(full_constraints,current)
        final_source=compact_sources_for_restricted(bundle['source'],full_constraints,current)
        final=feasible_dfs(final_constraints,len(current),find_all=True)
        for old in current:
            trial=[x for x in current if x!=old]
            rc=restrict_constraints(full_constraints,trial)
            res=feasible_dfs(rc,len(trial),find_all=False)
            deletions.append({'remove_point':support[old],'feasible':res['feasible'],'constraint_count':len(rc),'stats':res['stats'],'first_solution_bits_compact':res['first_solution']})
        if len(current)<=20:
            cert=make_assignment_certificate(minimized,final_constraints,final_source,max_assignments=args.cert_limit)
    out={'schema':'s0908_custom_lift_cut_minimization_v1','source_lut':str(LUT_PATH),'source_lut_sha256':sha_file(LUT_PATH),'lut_coverage_ok':meta.get('coverage_ok'),'pivot_name':args.pivot_name,'pivot':pivot,'label':args.label,'support':support,'builder_stats':bundle['stats'],'q_violations_head':bundle['q_violations'],'full_constraint_count':len(full_constraints),'initial_check':initial,'greedy_history':history,'minimized_indices':current if minimized is not None else None,'minimized_points':minimized,'cut':({'points':minimized,'rhs':len(minimized)-1,'meaning':f'sum over points <= {len(minimized)-1} for {args.pivot_name} pivot, by full-Wang lift-bit infeasibility'} if minimized is not None else None),'final_constraint_count':len(restrict_constraints(full_constraints,current)) if minimized is not None else None,'final_exact_check':final,'one_point_deletion_checks':deletions,'assignment_certificate':cert,'total_elapsed_sec':time.time()-t0}
    if cert and cert.get('made'): out['assignment_certificate_sha256']=cert['certificate_sha256']
    path=OUTDIR/f'{args.pivot_name}_{args.label}_lift_cut_minimized.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'label':args.label,'initial_feasible':initial['feasible'],'minimized_points':minimized,'minimized_size':len(minimized) if minimized else None,'all_deletions_feasible':all(d['feasible'] for d in deletions) if deletions else None,'certificate_made':bool(cert and cert.get('made')),'elapsed_sec':out['total_elapsed_sec']},indent=2,sort_keys=True),flush=True)
    print('saved',path,flush=True)

if __name__=='__main__': main()
