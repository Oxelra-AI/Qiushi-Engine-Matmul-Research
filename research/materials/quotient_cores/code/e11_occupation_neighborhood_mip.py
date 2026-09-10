#!/usr/bin/env python3
"""Exact bounded-neighborhood search for complete E11 Wang occupation supports.

Input: a rank-19 A-multiset.  The script asks whether there exists a complete
Wang-occupation-feasible rank-19 multiset within k replacements, equivalently
L1 distance <= 2k in point multiplicity vector.  This gives a finite exact check
around a near-feasible support; a found support should be passed immediately to
fixed-A XOR SAT.
"""
from __future__ import annotations

import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))
from e11_capacity_incremental_sat import build_or_load_constraint_cache, mask_to_points, scan_violations  # noqa: E402


def load_cache(path: Path):
    with path.open('rb') as f:
        return pickle.load(f)


def point_caps(cache):
    caps = {p: 0 for p in range(1,256)}
    for m, cap, d in zip(cache['masks'], cache['caps'], cache['dims']):
        if int(d) == 1 and int(m).bit_count() == 1:
            caps[int(m).bit_length()] = int(cap)
    if any(caps[p] <= 0 for p in range(1,256)):
        raise ValueError('bad singleton caps')
    return caps


def ms_to_counts(ms):
    c = {p: 0 for p in range(1,256)}
    for p in ms:
        c[int(p)] += 1
    return c


def counts_to_ms(sol):
    out=[]
    for p in range(1,256):
        out.extend([p]*int(sol.get(p,0)))
    return out


def sol_dict_to_counter(sol):
    return {int(k): int(v) for k, v in sol.items() if int(v)}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--cache',type=Path,default=Path('data/e11_capacity_sat/e11_capacity_cache.pkl'))
    ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank',type=int,default=19)
    ap.add_argument('--multiset',default='1,2,3,4,8,12,16,20,32,36,64,73,130,160,182,192,195,216,219')
    ap.add_argument('--radius',type=int,default=2,help='maximum replacements from input multiset')
    ap.add_argument('--time-limit',type=float,default=300)
    ap.add_argument('--workers',type=int,default=8)
    ap.add_argument('--max-cap-init',type=int,default=-1,help='if >=0, include only cuts with cap<=value; otherwise all complete Wang cuts')
    ap.add_argument('--out',type=Path,default=Path('data/e11_occupation_sat/neighborhood_radius2.json'))
    args=ap.parse_args()
    from ortools.sat.python import cp_model
    t_all=time.time()
    if not args.cache.exists():
        build_or_load_constraint_cache(args.lut,args.cache,args.rank)
    cache=load_cache(args.cache); caps=point_caps(cache)
    start_ms=[int(x) for x in args.multiset.split(',') if x.strip()]
    c0=ms_to_counts(start_ms)
    if sum(c0.values()) != args.rank:
        raise SystemExit('bad rank in input multiset')
    for p,v in c0.items():
        if v > caps[p]:
            raise SystemExit(f'input violates singleton cap at {p}: {v}>{caps[p]}')
    base_viol, base_stats = scan_violations(sol_dict_to_counter(c0), cache, max_report=50)
    print(f'base violations={base_stats}')

    model=cp_model.CpModel()
    x={p:model.new_int_var(0, int(caps[p]), f'x_{p}') for p in range(1,256)}
    model.add(sum(x[p] for p in range(1,256)) == args.rank)
    absdiff=[]
    for p in range(1,256):
        # Use an explicit finite table rather than AddAbsEquality on an affine
        # expression.  A previous version using add_abs_equality(d, x[p]-c0[p])
        # produced contradictory presolve UNSAT results for radius 19 even when
        # a known feasible point was within the radius.  The table encoding is
        # small because singleton capacities are 1 or 2.
        maxd = max(abs(v - int(c0[p])) for v in range(int(caps[p]) + 1))
        d=model.new_int_var(0, maxd, f'd_{p}')
        model.add_allowed_assignments([x[p], d], [(v, abs(v - int(c0[p]))) for v in range(int(caps[p]) + 1)])
        absdiff.append(d)
    model.add(sum(absdiff) <= 2*args.radius)

    added=0; bydim=Counter(); bycap=Counter()
    for i,(m,cap) in enumerate(zip(cache['masks'], cache['caps'])):
        if not int(m) or int(cap) >= args.rank:
            continue
        if args.max_cap_init >= 0 and int(cap) > args.max_cap_init:
            continue
        pts=mask_to_points(int(m))
        model.add(sum(x[p] for p in pts) <= int(cap))
        added += 1; bydim[int(cache['dims'][i])] += 1; bycap[int(cap)] += 1
    print(f'model cuts={added:,} bydim={dict(bydim)} bycap={dict(bycap)} radius={args.radius}')
    # Solution hint: start is generally infeasible but useful for CP-SAT phase.
    for p in range(1,256):
        model.add_hint(x[p], int(c0[p]))
    solver=cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.time_limit
    solver.parameters.num_workers = args.workers
    solver.parameters.random_seed = 20260904 + args.radius
    solver.parameters.log_search_progress = True
    t0=time.time(); status=solver.solve(model); elapsed=time.time()-t0
    status_name={cp_model.OPTIMAL:'OPTIMAL',cp_model.FEASIBLE:'FEASIBLE',cp_model.INFEASIBLE:'INFEASIBLE',cp_model.MODEL_INVALID:'MODEL_INVALID',cp_model.UNKNOWN:'UNKNOWN'}.get(status,str(status))
    sol=None; verification=None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol={p:int(solver.value(x[p])) for p in range(1,256) if int(solver.value(x[p]))}
        viol, stats = scan_violations(sol, cache, max_report=50)
        verification={'violation_count':len(viol),'stats':stats,'violations_head':viol[:20],'multiset':counts_to_ms(sol),'l1_distance':sum(abs(sol.get(p,0)-c0[p]) for p in range(1,256))}
        print('FOUND',json.dumps(verification['stats'],sort_keys=True),'ms',verification['multiset'],'l1',verification['l1_distance'])
    print(f'status={status_name} elapsed={elapsed:.2f}s wall={solver.wall_time}')
    result={'problem':'E11 complete Wang occupation bounded-neighborhood search','field':'F2','rank_s':args.rank,'input_multiset':start_ms,'input_complete_scan':base_stats,'input_violations_head':base_viol[:20],'radius_replacements':args.radius,'l1_bound':2*args.radius,'cuts_added':added,'cuts_by_dim8':dict(bydim),'cuts_by_cap':dict(bycap),'max_cap_filter':args.max_cap_init,'status':status_name,'elapsed_sec':elapsed,'solver_wall_time':solver.wall_time,'solution':sol,'verification':verification,'meaning':'FEASIBLE with zero verification violations gives a complete occupation-feasible A-multiset for fixed-A XOR SAT. INFEASIBLE excludes only this bounded replacement neighborhood, not global E11 rank 19.'}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('wrote',args.out)

if __name__=='__main__': main()
