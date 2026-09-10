#!/usr/bin/env python3
"""Compressed full-Wang capacity problem for pure rank-1 A-supports.

This studies the T-level s=20 subbranch in which all 20 A-factors are rank-1
3x3 matrices over F2.  There are only 49 projective rank-1 points.  We compress
all 8,283,458 Wang subspace constraints by their intersection with these 49
points, keeping the tightest capacity for each intersection.  The resulting
small SAT/MIP instance can be solved and, if UNSAT, exported to DIMACS/DRAT.
"""
from __future__ import annotations
import argparse, itertools, json, pickle, sys, time
from collections import Counter
from pathlib import Path

SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
from wang_capacity_lazy import unpack_basis, in_rowspace, matrix_rank_of_mask


def load_lut(path):
    with open(path,'rb') as f: payload=pickle.load(f)
    return payload['lut'], payload.get('meta',{})


def compress(lut, s=20):
    t0=time.time(); pts=[p for p in range(1,512) if matrix_rank_of_mask(p)==1]
    assert len(pts)==49
    tight={}  # mask over 49 -> min cap
    witness={}
    by_dim=Counter(); by_L=Counter(); by_inter_size=Counter()
    for idx,(key,L) in enumerate(lut.items(),1):
        basis=unpack_basis(key); mask=0
        for i,p in enumerate(pts):
            if in_rowspace(p,basis,n=9): mask |= 1<<i
        cap=s-L
        old=tight.get(mask)
        if old is None or cap<old:
            tight[mask]=cap; witness[mask]=key
        by_dim[key&0xF]+=1; by_L[L]+=1; by_inter_size[mask.bit_count()]+=1
        if idx%1000000==0:
            print(f'scanned {idx:,}/{len(lut):,}; compressed={len(tight):,}; elapsed={time.time()-t0:.1f}s', flush=True)
    # Drop constraints whose subset size <= cap; they are vacuous for rank1-only variables.
    cons=[(mask,cap,witness[mask]) for mask,cap in tight.items() if mask.bit_count()>cap]
    cons.sort(key=lambda x:(x[0].bit_count(), x[1], x[0]))
    meta={'rank1_points':pts,'raw_subspaces':len(lut),'compressed_intersections':len(tight),'nonvacuous_constraints':len(cons),'raw_by_dim':dict(by_dim),'raw_by_L':dict(by_L),'intersection_size_hist_raw':dict(by_inter_size),'constraint_size_cap_hist':{f'{m.bit_count()},{cap}':0 for m,cap,_ in cons},'elapsed_sec':time.time()-t0}
    h=Counter((m.bit_count(),cap) for m,cap,_ in cons); meta['constraint_size_cap_hist']={f'{k[0]},{k[1]}':v for k,v in sorted(h.items())}
    return pts,cons,meta


def solve_cpsat(pts, cons, s=20, fixed_point=1, time_limit=300):
    from ortools.sat.python import cp_model
    idx={p:i for i,p in enumerate(pts)}; model=cp_model.CpModel(); x=[model.NewBoolVar(f'x_{p}') for p in pts]
    model.Add(sum(x)==s)
    if fixed_point in idx: model.Add(x[idx[fixed_point]]==1)
    for mask,cap,key in cons:
        inds=[i for i in range(len(pts)) if (mask>>i)&1]
        model.Add(sum(x[i] for i in inds)<=cap)
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=time_limit; solver.parameters.num_search_workers=8
    t0=time.time(); st=solver.Solve(model); elapsed=time.time()-t0
    names={cp_model.OPTIMAL:'OPTIMAL',cp_model.FEASIBLE:'FEASIBLE',cp_model.INFEASIBLE:'INFEASIBLE',cp_model.UNKNOWN:'UNKNOWN',cp_model.MODEL_INVALID:'MODEL_INVALID'}
    sol=None
    if st in (cp_model.OPTIMAL,cp_model.FEASIBLE): sol=[pts[i] for i in range(len(pts)) if solver.Value(x[i])]
    return {'status':names.get(st,str(st)),'elapsed_sec':elapsed,'solution':sol,'solution_size':None if sol is None else len(sol)}


def write_cnf(pts, cons, s, fixed_point, cnf_path, meta_path, meta):
    from pysat.card import CardEnc, EncType
    var={p:i+1 for i,p in enumerate(pts)}; clauses=[]; top=len(pts)
    enc=CardEnc.equals(lits=list(var.values()), bound=s, top_id=top, encoding=EncType.seqcounter)
    clauses.extend(enc.clauses); top=enc.nv
    if fixed_point in var: clauses.append([var[fixed_point]])
    direct=0
    for mask,cap,key in cons:
        lits=[i+1 for i in range(len(pts)) if (mask>>i)&1]
        if len(lits)<=cap: continue
        for comb in itertools.combinations(lits, cap+1): clauses.append([-v for v in comb]); direct+=1
    cnf_path.parent.mkdir(parents=True,exist_ok=True)
    with cnf_path.open('w') as f:
        f.write(f'p cnf {top} {len(clauses)}\n')
        for cl in clauses: f.write(' '.join(map(str,cl))+' 0\n')
    m=dict(meta); m.update({'cnf_path':str(cnf_path),'num_vars':top,'num_clauses':len(clauses),'cardinality_clauses':len(enc.clauses),'direct_capacity_clauses':direct,'fixed_point':fixed_point})
    meta_path.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
    return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')); ap.add_argument('--rank',type=int,default=20); ap.add_argument('--fixed-point',type=int,default=1); ap.add_argument('--time-limit',type=float,default=300); ap.add_argument('--out',type=Path,default=Path('data/wang_capacity_rank1_only/rank1_only_capacity.json')); ap.add_argument('--cnf',type=Path,default=None); ap.add_argument('--cnf-meta',type=Path,default=None); args=ap.parse_args()
    lut,meta0=load_lut(args.lut); print(f'loaded LUT {len(lut):,} coverage={meta0.get("coverage_ok")}')
    pts,cons,meta=compress(lut,args.rank); print('compressed brief',json.dumps({k:meta[k] for k in ['compressed_intersections','nonvacuous_constraints','elapsed_sec']},indent=2))
    res=solve_cpsat(pts,cons,args.rank,args.fixed_point,args.time_limit); print('cpsat',json.dumps(res,indent=2))
    payload={'problem':'pure rank-1 T-level s=20 full Wang capacity','field':'F2','rank_s':args.rank,'lut_meta_brief':{'coverage_ok':meta0.get('coverage_ok'),'subspace_count':meta0.get('subspace_count'),'conflict_count':meta0.get('conflict_count')},'compression':meta,'cpsat_result':res,'meaning':'UNSAT excludes the subbranch where all twenty A-factors have rank 1. SAT gives only an A-support necessary condition, not a tensor decomposition.'}
    if args.cnf:
        cm=write_cnf(pts,cons,args.rank,args.fixed_point,args.cnf,args.cnf_meta or args.cnf.with_suffix('.meta.json'),meta); payload['cnf_meta']=cm
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n'); print('saved',args.out)
if __name__=='__main__': main()
