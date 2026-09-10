#!/usr/bin/env python3
"""Independent CP-SAT check of E11 Wang occupation feasibility with tight singleton domains.

This is a simpler cross-check of the rank-19 occupation model than the earlier
analysis full solver: variables are x_p with domains set directly to the exact
singleton capacities (249 points cap 1, six cap 2).  No neighborhood or absolute
distance variables are used.  Optional cap-threshold filters identify which
capacity layers already imply infeasibility.
"""
from __future__ import annotations

import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))
from e11_capacity_incremental_sat import build_or_load_constraint_cache, mask_to_points, scan_violations  # noqa: E402


def point_caps(cache):
    caps = {p: 0 for p in range(1,256)}
    for m, cap, d in zip(cache['masks'], cache['caps'], cache['dims']):
        if int(d) == 1 and int(m).bit_count() == 1:
            caps[int(m).bit_length()] = int(cap)
    if any(caps[p] <= 0 for p in range(1,256)):
        raise ValueError('bad singleton capacities')
    return caps


def sol_to_ms(sol):
    out=[]
    for p in range(1,256):
        out.extend([p]*int(sol.get(p,0)))
    return out


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--cache',type=Path,default=Path('data/e11_capacity_sat/e11_capacity_cache.pkl'))
    ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank',type=int,default=19)
    ap.add_argument('--max-cap',type=int,default=-1,help='include only cuts with cap <= this value; <0 includes all nonvacuous')
    ap.add_argument('--max-dim',type=int,default=8,help='include only cuts with dim <= this value')
    ap.add_argument('--time-limit',type=float,default=300)
    ap.add_argument('--workers',type=int,default=8)
    ap.add_argument('--out',type=Path,default=Path('data/e11_occupation_sat/domain_cpsat_all.json'))
    args=ap.parse_args()
    from ortools.sat.python import cp_model
    t_all=time.time()
    cache=build_or_load_constraint_cache(args.lut,args.cache,args.rank)
    caps=point_caps(cache)
    model=cp_model.CpModel()
    x={p:model.new_int_var(0,int(caps[p]),f'x_{p}') for p in range(1,256)}
    model.add(sum(x[p] for p in range(1,256)) == args.rank)
    added=0; bydim=Counter(); bycap=Counter(); byL=Counter(); examples=[]
    for i,(m,cap,d,L) in enumerate(zip(cache['masks'],cache['caps'],cache['dims'],cache['Ls'])):
        if not int(m) or int(cap) >= args.rank:
            continue
        if int(d) > args.max_dim:
            continue
        if args.max_cap >= 0 and int(cap) > args.max_cap:
            continue
        pts=mask_to_points(int(m))
        model.add(sum(x[p] for p in pts) <= int(cap))
        added += 1; bydim[int(d)] += 1; bycap[int(cap)] += 1; byL[int(L)] += 1
        if len(examples) < 20:
            examples.append({'index':i,'key8':int(cache['keys8'][i]),'dim8':int(d),'L':int(L),'cap':int(cap),'point_count':int(m).bit_count(),'points_head':pts[:64]})
    print(f'model rank={args.rank} cuts={added:,} max_cap={args.max_cap} max_dim={args.max_dim} bydim={dict(bydim)} bycap={dict(bycap)}')
    solver=cp_model.CpSolver()
    solver.parameters.max_time_in_seconds=args.time_limit
    solver.parameters.num_workers=args.workers
    solver.parameters.random_seed=2026090409 + max(0,args.max_cap)*100 + args.max_dim
    solver.parameters.log_search_progress=True
    t0=time.time(); status=solver.solve(model); elapsed=time.time()-t0
    name={cp_model.OPTIMAL:'OPTIMAL',cp_model.FEASIBLE:'FEASIBLE',cp_model.INFEASIBLE:'INFEASIBLE',cp_model.MODEL_INVALID:'MODEL_INVALID',cp_model.UNKNOWN:'UNKNOWN'}.get(status,str(status))
    sol=None; verification=None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol={p:int(solver.value(x[p])) for p in range(1,256) if int(solver.value(x[p]))}
        viol,stats=scan_violations(sol,cache,max_report=100)
        verification={'complete_violation_count':len(viol),'complete_scan_stats':stats,'violations_head':viol[:30],'multiset':sol_to_ms(sol)}
        print('solution complete scan',json.dumps(stats,sort_keys=True),'ms',sol_to_ms(sol))
    result={'problem':'independent tight-domain CP-SAT check of E11 Wang occupation feasibility','field':'F2','rank_s':args.rank,'max_cap':args.max_cap,'max_dim':args.max_dim,'cuts_added':added,'cuts_by_dim8':dict(bydim),'cuts_by_cap':dict(bycap),'cuts_by_L':dict(byL),'cut_examples_head':examples,'status':name,'elapsed_sec':elapsed,'solver_wall_time':solver.wall_time,'solution':sol,'verification':verification,'singleton_cap_counts':dict(Counter(caps.values())),'meaning':'INFEASIBLE proves the included Wang occupation inequalities have no rank-19 A-multiset solution; if included cuts are all derived from the verified Wang LUT this gives an E11 occupation obstruction, not by itself a characteristic-zero lower bound.'}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':name,'cuts_added':added,'elapsed_sec':elapsed,'wall_time':solver.wall_time,'solution':sol_to_ms(sol) if sol else None},indent=2,sort_keys=True))
    print(f'wrote {args.out}')

if __name__=='__main__': main()
