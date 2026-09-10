#!/usr/bin/env python3
"""Find complete core Wang-capacity supports by greedy search and CP-SAT.

For core rank s=19, this script enumerates all 417,199 quotient subspace
constraints and tries to find a distinct 19-point A-support satisfying all of
them.  Finding such a support proves only that Wang occupation constraints alone
do not exclude a rank-19 core decomposition; it gives a fixed-A surface for B/C
search.  If the boolean-distinct model is infeasible, multiplicities on the few
cap=2 points would still need a separate integer model.
"""
from __future__ import annotations

import argparse, json, pickle, random, sys, time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Tuple

SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
from core_capacity_from_wang_lut import CoreQuotient, PIVOTS, occupancy_key8
from wang_capacity_lazy import unpack_basis, subspace_points_from_basis, pack_basis
from wang_capacity_orbit_closed import extension_keys


def load_lut(path:Path):
    with path.open('rb') as f: payload=pickle.load(f)
    return payload['lut'], payload.get('meta',{})

def enumerate_subspace_keys(n:int=8)->List[int]:
    levels={0:{pack_basis(tuple())}}; all_keys=set(levels[0])
    for d in range(n):
        nxt=set()
        for key in levels[d]:
            for ekey in extension_keys(unpack_basis(key), n=n):
                if (ekey&0xF)==d+1: nxt.add(ekey)
        levels[d+1]=nxt; all_keys.update(nxt)
    return sorted(all_keys)

def bitset_for_points(points):
    b=0
    for p in points: b |= 1<<int(p)
    return b

def build_constraints(core:CoreQuotient,lut:Dict[int,int],s:int):
    keys=enumerate_subspace_keys(8)
    cons=[]; by_dim=Counter(); by_L=Counter(); by_cap=Counter()
    for key8 in keys:
        pts=subspace_points_from_basis(unpack_basis(key8))
        point_count=len(pts)
        key9=core.key9_from_key8(key8); L=lut[key9]; cap=s-L
        # Keep constraints that can bind a distinct support.
        if cap < min(s, point_count):
            pbits=bitset_for_points(pts)
            cons.append({'key8':key8,'dim8':key8&0xF,'L':L,'cap':cap,'pbits':pbits,'pts':pts,'point_count':point_count})
            by_dim[key8&0xF]+=1; by_L[L]+=1; by_cap[cap]+=1
    meta={'constraint_count':len(cons),'by_dim8':dict(by_dim),'by_L':dict(by_L),'by_cap':dict(by_cap)}
    return cons,meta

def verify_support(support:List[int], cons, max_report=20):
    bits=bitset_for_points(support); viol=[]
    for c in cons:
        occ=(bits & c['pbits']).bit_count()
        if occ>c['cap']:
            vv={k:c[k] for k in ['key8','dim8','L','cap','point_count']}; vv.update({'occupancy':occ,'excess':occ-c['cap'],'basis8':list(unpack_basis(c['key8']))})
            viol.append(vv)
    viol.sort(key=lambda v:(v['excess'],v['L'],v['occupancy'],-v['dim8']), reverse=True)
    return {'violation_count':len(viol),'violations_by_dim8':dict(Counter(v['dim8'] for v in viol)),'violations_by_L':dict(Counter(v['L'] for v in viol)),'max_excess':max((v['excess'] for v in viol),default=0),'violations_head':viol[:max_report]}

def greedy_search(cons, s:int, trials:int, seed:int):
    rng=random.Random(seed)
    # For fast feasibility while adding: list constraints by point.  Use the
    # precomputed point lists; recomputing 255 bit tests for every constraint is
    # too slow for the 416k complete core system.
    point_cons=defaultdict(list)
    for ci,c in enumerate(cons):
        for p in c['pts']:
            point_cons[p].append(ci)
    caps=[c['cap'] for c in cons]
    best=[]; best_info=None
    # Prefer points that participate in fewer tight cap1 constraints.
    tight_degree={p:sum(1 for ci in point_cons[p] if caps[ci]<=1) for p in range(1,256)}
    all_points=list(range(1,256))
    for tr in range(1,trials+1):
        loads=[0]*len(cons); support=[]; available=set(all_points)
        while len(support)<s:
            feasible=[]
            for p in available:
                ok=True
                for ci in point_cons[p]:
                    if loads[ci]+1>caps[ci]: ok=False; break
                if ok:
                    feasible.append(p)
            if not feasible: break
            # stochastic greedy: sample feasible candidates, choose least tight degree plus random noise.
            sample=feasible if len(feasible)<=64 else rng.sample(feasible,64)
            p=min(sample, key=lambda q: (tight_degree[q] + rng.random()*5, rng.random()))
            support.append(p); available.remove(p)
            for ci in point_cons[p]: loads[ci]+=1
        if len(support)>len(best):
            best=support[:]
            best_info={'trial':tr,'size':len(best),'support':best}
            print(f'greedy trial {tr}: new best size {len(best)} support={best}', flush=True)
        if len(support)==s:
            chk=verify_support(support,cons)
            if chk['violation_count']==0:
                return support, {'trial':tr,'status':'found','check':chk}
        if tr%100==0:
            print(f'greedy trial {tr}/{trials}; best={len(best)}', flush=True)
    return None, {'status':'not_found','best':best_info}

def solve_cpsat(cons,s:int,time_limit:float,hint:List[int]|None,outpath:Path):
    from ortools.sat.python import cp_model
    model=cp_model.CpModel(); x={p:model.NewBoolVar(f'x_{p}') for p in range(1,256)}
    model.Add(sum(x.values())==s)
    for c in cons:
        model.Add(sum(x[p] for p in c['pts'])<=c['cap'])
    if hint:
        hset=set(hint)
        for p in range(1,256): model.AddHint(x[p], 1 if p in hset else 0)
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=time_limit; solver.parameters.num_search_workers=8; solver.parameters.random_seed=31415
    t0=time.time(); status=solver.Solve(model); elapsed=time.time()-t0
    status_name={cp_model.OPTIMAL:'OPTIMAL',cp_model.FEASIBLE:'FEASIBLE',cp_model.INFEASIBLE:'INFEASIBLE',cp_model.MODEL_INVALID:'MODEL_INVALID',cp_model.UNKNOWN:'UNKNOWN'}.get(status,str(status))
    sol=None; chk=None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol=[p for p in range(1,256) if solver.Value(x[p])]
        chk=verify_support(sol,cons)
    res={'status':status_name,'elapsed_sec':elapsed,'support':sol,'verification':chk}
    outpath.parent.mkdir(parents=True,exist_ok=True); outpath.write_text(json.dumps(res,indent=2,sort_keys=True)+'\n')
    print(json.dumps(res,indent=2,sort_keys=True)[:4000]); print('saved',outpath)
    return res

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')); ap.add_argument('--core',choices=list(PIVOTS),default='E11'); ap.add_argument('--rank',type=int,default=19); ap.add_argument('--greedy-trials',type=int,default=1000); ap.add_argument('--seed',type=int,default=1); ap.add_argument('--cpsat-time',type=float,default=0); ap.add_argument('--outdir',type=Path,default=Path('data/core_capacity_supports')); args=ap.parse_args()
    lut,meta=load_lut(args.lut); print(f'Loaded LUT {len(lut):,} coverage={meta.get("coverage_ok")}')
    core=CoreQuotient(PIVOTS[args.core]); t0=time.time(); cons,cm=build_constraints(core,lut,args.rank); print('constraints',json.dumps(cm,sort_keys=True),'build_sec',time.time()-t0)
    support=None; greedy_info=None
    if args.greedy_trials>0:
        support,greedy_info=greedy_search(cons,args.rank,args.greedy_trials,args.seed)
        args.outdir.mkdir(parents=True,exist_ok=True)
        (args.outdir/f'greedy_{args.core}_s{args.rank}_seed{args.seed}.json').write_text(json.dumps({'core':args.core,'rank':args.rank,'constraint_meta':cm,'greedy_info':greedy_info,'support':support},indent=2,sort_keys=True)+'\n')
        print('greedy_info',json.dumps(greedy_info,indent=2,sort_keys=True)[:4000])
    if args.cpsat_time>0:
        solve_cpsat(cons,args.rank,args.cpsat_time,support,args.outdir/f'cpsat_{args.core}_s{args.rank}_seed{args.seed}.json')
if __name__=='__main__': main()
