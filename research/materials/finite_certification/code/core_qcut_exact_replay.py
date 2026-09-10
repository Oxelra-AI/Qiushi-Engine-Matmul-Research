#!/usr/bin/env python3
r"""Replay a analysis quotient-separator run from stored learned rows/cuts.

The purpose is to separate a solver status from file-generation bugs: rebuild a
fresh CP-SAT model from the stored learned complete-Wang rows and guarded
quotient-rank cuts, then solve it.  This is still not an independently replayable
SAT/PB proof, but it checks that the reported INFEASIBLE follows from the stored
constraints rather than hidden state inside the original Python process.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path
import numpy as np
SCRIPTS=Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))
from core_capacity_from_wang_lut import CoreQuotient
from fixed_A_saturation import mat_rank_f2
from complete_core_and_transversal import ROOT, build_core_constraints
from core_e11_multiset_quotient_sep import QuotientCutAdder
from quotient_rank_cuts import build_contractions, point_mask_for_q
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis

OUTDIR=ROOT/'workspace/data/quotient_rank_cuts'

def load_lut(path: Path):
    with path.open('rb') as f: payload=pickle.load(f)
    return {int(k):int(v) for k,v in payload['lut'].items()}

def main():
    from ortools.sat.python import cp_model
    ap=argparse.ArgumentParser()
    ap.add_argument('--source',type=Path,default=OUTDIR/'core_e11_multiset_quotient_sep_24r_with_cuts.json')
    ap.add_argument('--time-limit',type=float,default=300.0)
    ap.add_argument('--out',type=Path,default=OUTDIR/'core_e11_multiset_quotient_sep_replay.json')
    args=ap.parse_args(); args.out.parent.mkdir(parents=True,exist_ok=True)
    t0=time.time(); s=19; core=CoreQuotient(1)
    src=json.loads(args.source.read_text())
    T=np.load(ROOT/'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8)%2
    lut=load_lut(ROOT/'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records, meta=build_core_constraints(core,lut)
    record_by_key={int(r['key8']):r for r in records}
    contractions=build_contractions(T); masks={q:point_mask_for_q(q) for q in contractions}
    points=list(range(1,256))
    point_cap={}
    for p in points:
        key8=core.key8_from_rows([p]); key9=core.key9_from_key8(key8); point_cap[p]=max(0,min(s,s-int(lut[key9])))
    model=cp_model.CpModel(); x={p:model.NewIntVar(0,point_cap[p],f'x_{p}') for p in points}
    model.Add(sum(x[p] for p in points)==s)
    # Force repeated direction as in the source run.
    ys=[]
    for p,c in point_cap.items():
        if c>=2:
            y=model.NewBoolVar(f'repeat_{p}'); model.Add(x[p]>=2).OnlyEnforceIf(y); model.Add(x[p]<=1).OnlyEnforceIf(y.Not()); ys.append(y)
    if ys: model.AddBoolOr(ys)
    # Initial dim1/dim2 rows.
    wang_keys=set(); qcuts=[]
    for r in records:
        if int(r['dim8']) in (1,2): wang_keys.add(int(r['key8']))
    for rnd in src.get('rounds',[]):
        for w in rnd.get('learned_wang_rows',[]): wang_keys.add(int(w['key8']))
        for c in rnd.get('learned_quotient_cuts',[]): qcuts.append(c)
    for key8 in sorted(wang_keys):
        rec=record_by_key[key8]; cap=s-int(rec['L']); pts=subspace_points_from_basis(unpack_basis(key8))
        if cap<0: model.Add(0==1)
        else: model.Add(sum(x[p] for p in pts)<=cap)
    # Contraction lower bounds.
    clb=0
    for q,c in contractions.items():
        rk=int(c['rank'])
        if rk>0:
            model.Add(sum(x[p] for p in points if ((q&p).bit_count()&1))>=rk); clb+=1
    qadder=QuotientCutAdder(model,x,points,contractions,masks)
    qadded=0
    for c in qcuts:
        if qadder.add_cut(c['side'], int(c['sources'][0]), int(c['sources'][1]), int(c['target'])): qadded+=1
    build_sec=time.time()-t0
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(args.time_limit); solver.parameters.num_search_workers=8; solver.parameters.random_seed=4599
    ts=time.time(); status=solver.Solve(model); solve_sec=time.time()-ts
    status_name={cp_model.OPTIMAL:'OPTIMAL',cp_model.FEASIBLE:'FEASIBLE',cp_model.INFEASIBLE:'INFEASIBLE',cp_model.UNKNOWN:'UNKNOWN',cp_model.MODEL_INVALID:'MODEL_INVALID'}.get(status,str(status))
    res={'schema':'core_qcut_exact_replay_v1','source':str(args.source),'source_final_status':src.get('final_status'),'field':'F2','core':'E11','rank_s':s,'stored_learned_wang_rows':sum(len(r.get('learned_wang_rows',[])) for r in src.get('rounds',[])),'unique_wang_rows_replayed':len(wang_keys),'initial_dim1_dim2_rows':11050,'contraction_lower_count':clb,'stored_quotient_cuts':len(qcuts),'unique_quotient_cuts_replayed':qadded,'saturation_bool_vars':len(qadder.sat_lits),'point_cap_distribution':{str(k):int(v) for k,v in sorted(Counter(point_cap.values()).items())},'solver_status':status_name,'build_sec':round(build_sec,3),'solve_sec':round(solve_sec,3),'total_elapsed_sec':round(time.time()-t0,3)}
    if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        counts={p:solver.Value(x[p]) for p in points if solver.Value(x[p])}; res['counts']={str(k):int(v) for k,v in sorted(counts.items())}
    args.out.write_text(json.dumps(res,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':status_name,'wang':len(wang_keys),'qcuts':qadded,'build_sec':round(build_sec,3),'solve_sec':round(solve_sec,3)},sort_keys=True))
    print(f'Saved {args.out}')
if __name__=='__main__': main()
