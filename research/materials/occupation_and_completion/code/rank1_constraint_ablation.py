#!/usr/bin/env python3
"""Ablation and CP-SAT core extraction for pure rank-1 Wang constraints.

The pure rank-1 branch is small enough to ask which compressed intersection
families actually make exact size 20 impossible.  Constraints are grouped by
(size, cap), where size is the number of rank-1 grid points in the intersection
and cap is the Wang residual capacity.  This script can solve exact-size
feasibility for chosen groups and, optionally, attach an assumption literal to
each row to obtain a CP-SAT infeasibility core.  The core is not a formal proof,
but it is a useful seed for a much smaller DRAT CNF.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Set, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_capacity_profile import load_or_build  # noqa: E402


def parse_groups(spec: str) -> Set[Tuple[int,int]]:
    out=set()
    for part in spec.split(','):
        part=part.strip()
        if not part:
            continue
        a,b=part.split(':') if ':' in part else part.split('/')
        out.add((int(a),int(b)))
    return out


def selected(cons, mode: str, groups: Set[Tuple[int,int]], max_size: int | None, min_gap: int | None):
    rows=[]
    for idx,(mask,cap,key) in enumerate(cons):
        size=mask.bit_count(); gap=size-cap
        take=False
        if mode=='all': take=True
        elif mode=='groups': take=(size,cap) in groups
        elif mode=='max-size': take=max_size is not None and size<=max_size
        elif mode=='min-gap': take=min_gap is not None and gap>=min_gap
        elif mode=='small-and-dense': take=(size<=13 or gap>=6)
        else: raise ValueError(mode)
        if take:
            rows.append((idx,mask,cap,key))
    return rows


def solve(pts, rows, exact_size, fixed_point, time_limit, workers, assumptions):
    from ortools.sat.python import cp_model
    t0=time.time(); model=cp_model.CpModel(); x=[model.NewBoolVar(f'x_{p}') for p in pts]
    idx={p:i for i,p in enumerate(pts)}
    model.Add(sum(x)==exact_size)
    if fixed_point is not None:
        model.Add(x[idx[fixed_point]]==1)
    assump_vars=[]; assump_map=[]
    for rid,mask,cap,key in rows:
        inds=[i for i in range(len(pts)) if (mask>>i)&1]
        if len(inds)<=cap:
            continue
        ct=model.Add(sum(x[i] for i in inds)<=cap)
        if assumptions:
            a=model.NewBoolVar(f'a_{rid}')
            ct.OnlyEnforceIf(a)
            assump_vars.append(a); assump_map.append((rid,mask,cap,key))
    if assumptions:
        model.AddAssumptions(assump_vars)
    build=time.time()-t0
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=time_limit; solver.parameters.num_search_workers=workers
    t1=time.time(); st=solver.Solve(model); solve_t=time.time()-t1
    names={cp_model.OPTIMAL:'OPTIMAL',cp_model.FEASIBLE:'FEASIBLE',cp_model.INFEASIBLE:'INFEASIBLE',cp_model.UNKNOWN:'UNKNOWN',cp_model.MODEL_INVALID:'MODEL_INVALID'}
    sol=None
    if st in (cp_model.OPTIMAL,cp_model.FEASIBLE): sol=[pts[i] for i in range(len(pts)) if solver.Value(x[i])]
    core=[]
    if assumptions and st==cp_model.INFEASIBLE:
        # Returned literals are integer indices in current OR-Tools versions; compare to BoolVar.Index().
        core_lits=set(int(v) for v in solver.SufficientAssumptionsForInfeasibility())
        idx_to_row={a.Index():row for a,row in zip(assump_vars,assump_map)}
        for lit in sorted(core_lits):
            row=idx_to_row.get(lit)
            if row is not None:
                rid,mask,cap,key=row; core.append({'rid':rid,'mask':mask,'cap':cap,'size':mask.bit_count(),'key':key,'dim':key&0xF})
    return {'status':names.get(st,str(st)),'status_code':int(st),'build_elapsed_sec':build,'solve_elapsed_sec':solve_t,'wall_time':float(solver.WallTime()),'num_conflicts':int(solver.NumConflicts()),'num_branches':int(solver.NumBranches()),'solution':sol,'solution_size':None if sol is None else len(sol),'assumption_core_size':len(core),'assumption_core':core}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')); ap.add_argument('--cache',type=Path,default=Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl')); ap.add_argument('--rank',type=int,default=20); ap.add_argument('--fixed-point',type=int,default=1); ap.add_argument('--exact-size',type=int,default=20); ap.add_argument('--mode',choices=['all','groups','max-size','min-gap','small-and-dense'],default='all'); ap.add_argument('--groups',default=''); ap.add_argument('--max-size',type=int,default=None); ap.add_argument('--min-gap',type=int,default=None); ap.add_argument('--assumptions',action='store_true'); ap.add_argument('--time-limit',type=float,default=300); ap.add_argument('--workers',type=int,default=8); ap.add_argument('--out',type=Path,required=True); args=ap.parse_args()
    pts,cons,meta,lut_meta=load_or_build(args.cache,args.lut,args.rank,False)
    groups=parse_groups(args.groups)
    rows=selected(cons,args.mode,groups,args.max_size,args.min_gap)
    hist=Counter((m.bit_count(),cap) for _,m,cap,_ in rows)
    print('selected',len(rows),'hist',dict(sorted(hist.items())))
    res=solve(pts,rows,args.exact_size,args.fixed_point,args.time_limit,args.workers,args.assumptions)
    payload={'problem':'pure rank1 constraint ablation / CP-SAT core','field':'F2','rank_s':args.rank,'fixed_point':args.fixed_point,'exact_size':args.exact_size,'mode':args.mode,'groups':sorted(groups),'max_size':args.max_size,'min_gap':args.min_gap,'assumptions':args.assumptions,'selected_constraint_count':len(rows),'selected_hist':{f'{a},{b}':c for (a,b),c in sorted(hist.items())},'result':res,'compression':meta,'meaning':'INFEASIBLE identifies a sufficient row family for excluding 20 rank-1 A-points under Wang occupation. An assumption core is only a seed for later CNF/DRAT proof.'}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:res[k] for k in ['status','solution_size','assumption_core_size','build_elapsed_sec','solve_elapsed_sec','num_conflicts','num_branches']},indent=2,sort_keys=True)); print('saved',args.out)

if __name__=='__main__': main()
