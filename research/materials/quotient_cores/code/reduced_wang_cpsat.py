#!/usr/bin/env python3
"""analysis: CP-SAT pilot on the primitive-reduced E11 Wang system.

This is not a proof-producing run. It tests whether the analysis inductive
row reduction materially changes support search. The model keeps point-level
variables, all retained Wang rows from `primitive_reduced_rows.pkl`, and optional
transported radius-3 overlap cuts (valid consequences of the checked d=3 local
Wang proof). If a solution is found, it is rescanned against the complete 417,199
Wang table.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

SCRIPTS=Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints, complete_core_wang_scan, ROOT
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis
from overlap_cut_separator import load_overlap_centers, support_bitset, overlap_summary

OUTDIR=ROOT/'workspace/data/reduced_wang'
DEFAULT_REDUCED=OUTDIR/'primitive_reduced_rows.pkl'
DEFAULT_OVERLAP=ROOT/'workspace/data/transported_overlap/transported_overlap_analysis.json'

def load_reduced(path:Path):
    with path.open('rb') as f: return pickle.load(f)

def add_wang_rows(model,x,records,kept_keys):
    kept=set(int(k) for k in kept_keys)
    count=0; by_dim=Counter(); by_L=Counter(); skipped=0
    for rec in records:
        key=int(rec['key8'])
        if key not in kept:
            skipped+=1; continue
        L=int(rec['L']); cap=19-L
        if cap>=19: continue
        pts=subspace_points_from_basis(unpack_basis(key))
        if pts:
            model.Add(sum(x[p] for p in pts) <= cap)
            count+=1; by_dim[int(rec['dim8'])]+=1; by_L[L]+=1
    return {'added':count,'skipped_not_kept':skipped,'by_dim':{str(k):int(v) for k,v in sorted(by_dim.items())},'by_L':{str(k):int(v) for k,v in sorted(by_L.items())}}

def main():
    from ortools.sat.python import cp_model
    ap=argparse.ArgumentParser()
    ap.add_argument('--solver-time',type=float,default=300.0)
    ap.add_argument('--workers',type=int,default=8)
    ap.add_argument('--seed',type=int,default=6161)
    ap.add_argument('--reduced',type=Path,default=DEFAULT_REDUCED)
    ap.add_argument('--use-overlap',action='store_true')
    ap.add_argument('--overlap-analysis',type=Path,default=DEFAULT_OVERLAP)
    ap.add_argument('--overlap-max',type=int,default=15)
    ap.add_argument('--out',type=Path,default=OUTDIR/'reduced_wang_cpsat_pilot.json')
    args=ap.parse_args(); args.out.parent.mkdir(parents=True,exist_ok=True)
    t0=time.time()
    lut,lut_meta=load_lut(ROOT/'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records,meta=build_core_constraints(CoreQuotient(1),lut)
    red=load_reduced(args.reduced)
    model=cp_model.CpModel(); points=list(range(1,256)); x={p:model.NewBoolVar(f'x_{p}') for p in points}
    model.Add(sum(x[p] for p in points)==19)
    wang_summary=add_wang_rows(model,x,records,red['kept_key8'])
    overlap_meta={}; overlap_cut_count=0; centers=[]; center_bits=[]
    if args.use_overlap:
        centers,overlap_meta=load_overlap_centers(args.overlap_analysis,None)
        center_bits=[support_bitset(c) for c in centers]
        for c in centers:
            model.Add(sum(x[p] for p in c) <= int(args.overlap_max)); overlap_cut_count+=1
    build_sec=time.time()-t0
    print(json.dumps({'build_sec':round(build_sec,3),'wang_summary':wang_summary,'overlap_cut_count':overlap_cut_count},indent=2)[:4000])
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(args.solver_time); solver.parameters.num_search_workers=int(args.workers); solver.parameters.random_seed=int(args.seed)
    ts=time.time(); status=solver.Solve(model); solve_sec=time.time()-ts; status_name=solver.StatusName(status)
    print('status',status_name,'solve_sec',solve_sec)
    result={
        'schema':'reduced_wang_cpsat_pilot_v1',
        'meaning':'CP-SAT feasibility pilot using the analysis primitive-reduced row set. FEASIBLE gives only an A-support and is rescanned against the complete Wang table; UNKNOWN/solver-only INFEASIBLE is not a proof.',
        'field':'F2','core':'E11 quotient core','rank_s':19,
        'parameters':{'solver_time':args.solver_time,'workers':args.workers,'seed':args.seed,'use_overlap':bool(args.use_overlap),'overlap_max':args.overlap_max,'reduced':str(args.reduced)},
        'lut_coverage_ok':lut_meta.get('coverage_ok'),
        'complete_meta':meta,
        'reduced_file_info':{k:red.get(k) for k in ['rank_s','description']},
        'reduced_counts':{'kept':len(red['kept_key8']),'dropped':len(red['dropped_key8'])},
        'wang_summary':wang_summary,
        'overlap_meta':overlap_meta|{'overlap_cuts_used':overlap_cut_count},
        'build_sec':round(build_sec,3),'status':status_name,'solve_sec':round(solve_sec,3),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A=[p for p in points if solver.Value(x[p])]
        scan=complete_core_wang_scan('reduced_cpsat_solution',A,19,records,max_head=40)
        ov=overlap_summary(A,center_bits) if center_bits else None
        result['solution']={'A_cols':A,'complete_wang_scan':scan,'overlap_summary':ov}
        print('A',A)
        print('scan',json.dumps({k:scan[k] for k in ['complete_violation_count','max_excess','violations_by_L','violations_by_dim8']},indent=2))
    result['elapsed_sec']=round(time.time()-t0,3)
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print('saved',args.out)
if __name__=='__main__': main()
