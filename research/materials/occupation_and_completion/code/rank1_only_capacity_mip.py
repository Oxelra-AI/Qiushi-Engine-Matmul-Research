#!/usr/bin/env python3
"""Independent HiGHS MIP check for pure rank-1 T-level full Wang capacity.

Recomputes the rank1-intersection compression from the full Wang LUT and solves
a 49-binary infeasibility problem. This cross-checks the CP-SAT result in
rank1_only_capacity.py. It is still computational evidence, not a DRAT proof.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
from rank1_only_capacity import compress, load_lut


def solve(cons, s, fixed_point, pts, time_limit):
    t0=time.time(); n=len(pts); idx={p:i for i,p in enumerate(pts)}
    m=1+len(cons)+(1 if fixed_point in idx else 0)
    A=lil_matrix((m,n),dtype=float); lb=np.full(m,-np.inf); ub=np.empty(m,dtype=float)
    A[0,:]=1.0; lb[0]=s; ub[0]=s; row=1
    size_cap=Counter()
    for mask,cap,key in cons:
        for i in range(n):
            if (mask>>i)&1: A[row,i]=1.0
        lb[row]=-np.inf; ub[row]=cap; row+=1; size_cap[(mask.bit_count(),cap)]+=1
    if fixed_point in idx:
        A[row,idx[fixed_point]]=1.0; lb[row]=1; ub[row]=1; row+=1
    res=milp(c=np.zeros(n), integrality=np.ones(n), bounds=Bounds(np.zeros(n),np.ones(n)), constraints=[LinearConstraint(A.tocsr(),lb,ub)], options={'time_limit':time_limit,'mip_rel_gap':0.0,'disp':True})
    sol=None
    if getattr(res,'x',None) is not None:
        sol=[pts[i] for i,v in enumerate(res.x) if int(round(v))]
    return {'status':int(res.status),'success':bool(res.success),'message':str(res.message),'fun':None if res.fun is None else float(res.fun),'elapsed_sec':time.time()-t0,'constraint_count':len(cons),'size_cap_hist':{f'{a},{b}':c for (a,b),c in sorted(size_cap.items())},'solution':sol,'solution_size':None if sol is None else len(sol)}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')); ap.add_argument('--rank',type=int,default=20); ap.add_argument('--fixed-point',type=int,default=1); ap.add_argument('--time-limit',type=float,default=300); ap.add_argument('--out',type=Path,default=Path('data/wang_capacity_rank1_only/rank1_only_capacity_mip.json')); args=ap.parse_args()
    lut,meta0=load_lut(args.lut); print(f'loaded LUT {len(lut):,} coverage={meta0.get("coverage_ok")}')
    pts,cons,meta=compress(lut,args.rank); print('compressed',meta['compressed_intersections'],meta['nonvacuous_constraints'])
    res=solve(cons,args.rank,args.fixed_point,pts,args.time_limit); print(json.dumps({k:res[k] for k in ['status','success','message','elapsed_sec','constraint_count','solution_size']},indent=2))
    payload={'problem':'pure rank1 T-level s=20 full Wang capacity MIP cross-check','field':'F2','rank_s':args.rank,'compression':meta,'mip_result':res,'lut_meta_brief':{'coverage_ok':meta0.get('coverage_ok'),'subspace_count':meta0.get('subspace_count'),'conflict_count':meta0.get('conflict_count')}}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n'); print('saved',args.out)
if __name__=='__main__': main()
