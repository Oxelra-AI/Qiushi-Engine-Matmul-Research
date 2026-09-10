#!/usr/bin/env python3
"""CP-SAT lazy solver for selected initial Wang capacity dimensions.

Unlike wang_capacity_solve_enhanced.py, this can add all dim 8 hyperplane
constraints at the start while keeping dimensions 4--7 lazy.  The immediate
use is the code-theoretic rank-20 T-level problem with dim 1,2,3,8 cuts.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path
from typing import Dict, Sequence, Tuple

SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
from wang_capacity_lazy import unpack_basis, subspace_points_from_basis, all_subset_span_keys, occupancy_of_key, matrix_rank_of_mask

CANON_BY_RANK={1:1,2:1|16,3:1|16|256}


def load_lut(path:Path):
    with path.open('rb') as f: payload=pickle.load(f)
    return payload['lut'], payload.get('meta',{})


def parse_dims(s:str):
    out=[]
    for part in s.split(','):
        part=part.strip()
        if not part: continue
        if '-' in part:
            a,b=map(int,part.split('-',1)); out.extend(range(a,b+1))
        else: out.append(int(part))
    return sorted(set(out))


def find_violations(sol:Dict[int,int], s:int, lut:Dict[int,int], max_cuts:int=0):
    t0=time.time(); keys=all_subset_span_keys(sorted(sol)); viol=[]
    for key in keys:
        lb=lut[key]; occ=occupancy_of_key(key,sol); cap=s-lb
        if occ>cap:
            viol.append({'key':key,'dim':key&0xF,'basis':list(unpack_basis(key)),'lb':lb,'cap':cap,'occupancy':occ,'excess':occ-cap})
    viol.sort(key=lambda v:(v['excess'],v['lb'],v['occupancy'],-v['dim']), reverse=True)
    stats={'support_size':len(sol),'total_multiplicity':sum(sol.values()),'unique_subset_spans':len(keys),'violation_count':len(viol),'violations_by_dim':dict(Counter(v['dim'] for v in viol)),'violations_by_lb':dict(Counter(v['lb'] for v in viol)),'elapsed_sec':time.time()-t0}
    return (viol[:max_cuts] if max_cuts and len(viol)>max_cuts else viol), stats


def solve(lut, s:int, init_dims:Sequence[int], branch_rank:int, solver_time:float, max_iters:int, max_cuts_per_iter:int, out:Path):
    from ortools.sat.python import cp_model
    model=cp_model.CpModel(); points=list(range(1,512)); x={p:model.NewIntVar(0,s,f'x_{p}') for p in points}
    model.Add(sum(x.values())==s)
    if branch_rank:
        canon=CANON_BY_RANK[branch_rank]; model.Add(x[canon]>=1)
        if branch_rank>=2:
            for p in points:
                if matrix_rank_of_mask(p)<branch_rank: model.Add(x[p]==0)
        print(f'branch rank {branch_rank}: fixed {canon}, lower ranks excluded if needed')
    added=set(); cuts=[]
    def add_cut(key:int, reason:str):
        if key in added: return False
        lb=lut[key]; cap=s-lb; pts=subspace_points_from_basis(unpack_basis(key))
        model.Add(sum(x[p] for p in pts)<=cap)
        added.add(key); cuts.append({'key':key,'dim':key&0xF,'lb':lb,'cap':cap,'point_count':len(pts),'reason':reason}); return True
    t0=time.time()
    init_set=set(init_dims)
    for key in sorted(lut):
        d=key&0xF
        if d in init_set: add_cut(key, 'initial_selected_dims')
    print(f'Initial dims {list(init_dims)}: cuts={len(added):,} elapsed={time.time()-t0:.1f}s by_dim={dict(Counter(c["dim"] for c in cuts))}')
    history=[]; final_status=None; final_solution=None
    for it in range(1,max_iters+1):
        solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=solver_time; solver.parameters.num_search_workers=8; solver.parameters.random_seed=9000+it
        st=time.time(); status=solver.Solve(model); elapsed=time.time()-st
        names={cp_model.OPTIMAL:'OPTIMAL',cp_model.FEASIBLE:'FEASIBLE',cp_model.INFEASIBLE:'INFEASIBLE',cp_model.MODEL_INVALID:'MODEL_INVALID',cp_model.UNKNOWN:'UNKNOWN'}
        sname=names.get(status,str(status)); entry={'iteration':it,'solver_status':sname,'cut_count':len(added),'solve_elapsed_sec':elapsed}
        print(f'iter {it}: {sname} cuts={len(added):,} solve={elapsed:.1f}s')
        if status in (cp_model.INFEASIBLE, cp_model.MODEL_INVALID): final_status=sname; history.append(entry); break
        if status not in (cp_model.OPTIMAL,cp_model.FEASIBLE): final_status=sname; history.append(entry); break
        sol={p:solver.Value(x[p]) for p in points if solver.Value(x[p])}
        entry['solution']={str(k):v for k,v in sorted(sol.items())}; entry['support_size']=len(sol); entry['max_mult']=max(sol.values()) if sol else 0; entry['rank_count']=dict(Counter(matrix_rank_of_mask(p) for p in sol for _ in range(sol[p])))
        viol,stats=find_violations(sol,s,lut,max_cuts=max_cuts_per_iter)
        entry['check_stats']=stats; entry['violations_head']=viol[:50]
        print(f'  support={len(sol)} ranks={entry["rank_count"]} maxmult={entry["max_mult"]} spans={stats["unique_subset_spans"]:,} violations={stats["violation_count"]:,} by_dim={stats["violations_by_dim"]} check={stats["elapsed_sec"]:.1f}s')
        if not viol:
            final_status='CAPACITY_FEASIBLE_NO_VIOLATION_FOUND'; final_solution=sol; history.append(entry); break
        nadd=0
        for v in viol:
            if add_cut(v['key'], f'lazy_iter_{it}'): nadd+=1
        entry['lazy_cuts_added']=nadd; print(f'  added {nadd:,}')
        history.append(entry)
        if nadd==0: final_status='STALLED_NO_NEW_CUTS'; final_solution=sol; break
    payload={'problem':'T-level Wang occupation capacity selected-dim CP-SAT lazy','field':'F2','rank_s':s,'init_dims':list(init_dims),'branch_rank':branch_rank,'final_status':final_status,'final_solution':None if final_solution is None else {str(k):v for k,v in sorted(final_solution.items())},'iterations':history,'cut_count':len(added),'cuts_by_dim':dict(Counter(c['dim'] for c in cuts)),'cuts_by_lb':dict(Counter(c['lb'] for c in cuts)),'cut_records_head':cuts[:100],'cut_records_tail':cuts[-100:]}
    out.parent.mkdir(parents=True,exist_ok=True); out.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    print('saved',out)


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')); ap.add_argument('--rank',type=int,default=20); ap.add_argument('--init-dims',default='1,2,3,8'); ap.add_argument('--branch-rank',type=int,choices=[0,1,2,3],default=0); ap.add_argument('--solver-time',type=float,default=300); ap.add_argument('--max-iters',type=int,default=20); ap.add_argument('--max-cuts-per-iter',type=int,default=0); ap.add_argument('--out',type=Path,required=True); args=ap.parse_args(); lut,meta=load_lut(args.lut); print(f'loaded {len(lut):,} coverage={meta.get("coverage_ok")} conflicts={meta.get("conflict_count")}'); solve(lut,args.rank,parse_dims(args.init_dims),args.branch_rank,args.solver_time,args.max_iters,args.max_cuts_per_iter,args.out)
if __name__=='__main__': main()
