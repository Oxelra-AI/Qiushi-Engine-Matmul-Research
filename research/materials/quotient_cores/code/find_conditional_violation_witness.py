#!/usr/bin/env python3
"""Find a full-A support satisfying low-dimensional Wang rows but violating a
conditional re-pivoted lift cut.

This tests whether the analysis conditional cuts are genuine additional
constraints in a branch, rather than already forced by the row family used to
start the full-A CEGAR.
"""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path
from ortools.sat.python import cp_model
from collections import Counter

ROOT=Path('research/research_record')
SCRIPTS=ROOT/'workspace/scripts'
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))
import fullA_global_cegar as base  # type: ignore

OUTDIR=ROOT/'workspace/data/quotient_lift/conditional_cuts'
PIVOTS=base.PIVOTS


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--pivot-name',choices=['rank2','rank3'],default=None)
    ap.add_argument('--force-quotient',default='')
    ap.add_argument('--forbid-quotient',default='')
    ap.add_argument('--initial-dim',type=int,default=2)
    ap.add_argument('--initial-cap',type=int,default=2)
    ap.add_argument('--time-limit',type=float,default=120)
    ap.add_argument('--seed',type=int,default=25025)
    ap.add_argument('--label',required=True)
    args=ap.parse_args(); t0=time.time()
    lut,meta=base.load_lut(base.LUT_PATH)
    rows,row_keys,init_stats=base.build_initial_rows(lut,20,args.initial_dim,args.initial_cap)
    cond,cond_meta=base.load_conditionals(base.COND_PATH)
    pivot=PIVOTS[args.pivot_name] if args.pivot_name else None
    force_q={int(x) for x in args.force_quotient.split(',') if x.strip()}
    forbid_q={int(x) for x in args.forbid_quotient.split(',') if x.strip()}
    model=cp_model.CpModel(); z={a:model.NewBoolVar(f'z_{a}') for a in range(1,512)}
    model.Add(sum(z.values())==20)
    model.Add(sum(base.RANKS[a]*z[a] for a in range(1,512))>=27)
    if pivot is not None:
        model.Add(z[pivot]==1)
        for p in force_q:
            s=base.section_lift(p,pivot); model.Add(z[s]+z[s^pivot]==1)
        for p in forbid_q:
            s=base.section_lift(p,pivot); model.Add(z[s]==0); model.Add(z[s^pivot]==0)
    for r in rows:
        pts=base.points_from_mask(r['mask'],512)
        model.Add(sum(z[a] for a in pts)<=int(r['cap']))
    # Violate at least one conditional: z_a=1 and sum_B >= 12, equivalently lhs>=21.
    sels=[]; eligible=0; potential_hist=Counter()
    forbidden_full=set()
    if pivot is not None:
        for p in forbid_q:
            s=base.section_lift(p,pivot); forbidden_full.add(s); forbidden_full.add(s^pivot)
    for i,c in enumerate(cond):
        B=[b for b in c['B'] if b not in forbidden_full]
        potential_hist[len(B)]+=1
        if len(B)<12: continue
        eligible+=1
        s=model.NewBoolVar(f'viol_{i}')
        model.Add(z[c['pivot_a']]==1).OnlyEnforceIf(s)
        model.Add(sum(z[b] for b in c['B'])>=12).OnlyEnforceIf(s)
        sels.append(s)
    model.Add(sum(sels)>=1)
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(args.time_limit); solver.parameters.num_search_workers=8; solver.parameters.random_seed=args.seed
    st=solver.Solve(model); status=solver.StatusName(st)
    out={'schema':'s0908_find_conditional_violation_witness_v1','meaning':'If SAT/OPTIMAL, low-dimensional full-Wang rows and branch constraints permit a support that violates at least one conditional re-pivoted lift cut; hence the conditional family is not redundant relative to this starting row system. This is not a full tensor candidate.','pivot_name':args.pivot_name,'pivot':pivot,'force_quotient':sorted(force_q),'forbid_quotient':sorted(forbid_q),'initial_stats':init_stats,'conditionals_meta':cond_meta,'eligible_conditionals':eligible,'eligible_B_after_forbid_hist':dict(sorted(potential_hist.items())),'status':status,'elapsed_sec':time.time()-t0,'solver_wall_time':solver.WallTime(),'conflicts':solver.NumConflicts(),'branches':solver.NumBranches()}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        support=[a for a in range(1,512) if solver.Value(z[a])]
        cev=base.eval_conditionals(support,cond)
        viol,stats=base.check_candidate(lut,support,20,max_report=100)
        out.update({'support':support,'rank_hist':dict(sorted((str(k),int(v)) for k,v in Counter(base.RANKS[a] for a in support).items())),'rank_sum':sum(base.RANKS[a] for a in support),'conditional_eval':cev,'full_check_stats':stats,'violation_head':viol[:20]})
    OUTDIR.mkdir(parents=True,exist_ok=True)
    p=OUTDIR/f'{args.label}.json'; p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(p),'status':status,'eligible':eligible,'support':out.get('support'), 'conditional_violations':out.get('conditional_eval',{}).get('violations'), 'max_lhs':out.get('conditional_eval',{}).get('max_lhs'), 'full_violations':out.get('full_check_stats',{}).get('violation_count'), 'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__': main()
