#!/usr/bin/env python3
"""LP relaxation for the rank-1 projection of Wang occupation constraints.

This tests whether the pure rank-1 obstruction is already linear.  If the LP
maximum of selected rank-1 points is < 20, the rank-1-only branch has a much
simpler certificate target than a large DRAT search: a Farkas/dual certificate
using a small set of projected Wang inequalities.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import lil_matrix

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from rank1_capacity_profile import load_or_build  # noqa: E402


def build_matrix(cons, n):
    A = lil_matrix((len(cons), n), dtype=float)
    b = np.empty(len(cons), dtype=float)
    size_cap = Counter()
    for r,(mask,cap,key) in enumerate(cons):
        x = mask
        while x:
            lb = x & -x
            i = lb.bit_length()-1
            A[r,i] = 1.0
            x ^= lb
        b[r] = cap
        size_cap[(mask.bit_count(), cap)] += 1
    return A.tocsr(), b, size_cap


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')); ap.add_argument('--cache',type=Path,default=Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl')); ap.add_argument('--rank',type=int,default=20); ap.add_argument('--fixed-point',type=int,default=1); ap.add_argument('--no-fixed',action='store_true'); ap.add_argument('--integral',action='store_true'); ap.add_argument('--time-limit',type=float,default=300); ap.add_argument('--out',type=Path,required=True); args=ap.parse_args()
    pts,cons,meta,lut_meta=load_or_build(args.cache,args.lut,args.rank,False)
    t0=time.time(); A,b,size_cap=build_matrix(cons,len(pts)); build_elapsed=time.time()-t0
    c=-np.ones(len(pts))
    fixed = None if args.no_fixed else args.fixed_point
    extra_rows=[]; extra_lb=[]; extra_ub=[]
    if fixed is not None:
        try:
            j=pts.index(fixed)
        except ValueError:
            j=None
        if j is not None:
            row=lil_matrix((1,len(pts)),dtype=float); row[0,j]=1.0; extra_rows.append(row.tocsr()); extra_lb.append(1.0); extra_ub.append(1.0)
    # Add only bounds/inequality to linprog; equality for fixed as bounds by setting lb=ub for variable is simpler.
    bounds=[(0,1) for _ in pts]
    if fixed is not None and fixed in pts:
        bounds[pts.index(fixed)] = (1,1)
    t1=time.time()
    if args.integral:
        constraints=[LinearConstraint(A, -np.inf*np.ones(len(cons)), b)]
        res=milp(c=c, integrality=np.ones(len(pts)), bounds=Bounds(np.array([lo for lo,hi in bounds]),np.array([hi for lo,hi in bounds])), constraints=constraints, options={'time_limit':args.time_limit,'mip_rel_gap':0.0,'disp':True})
        status=int(res.status); message=str(res.message); x=None if getattr(res,'x',None) is None else res.x; fun=None if res.fun is None else float(res.fun)
        objective=None if fun is None else -fun
    else:
        res=linprog(c, A_ub=A, b_ub=b, bounds=bounds, method='highs', options={'time_limit':args.time_limit})
        status=int(res.status); message=str(res.message); x=None if res.x is None else res.x; objective=None if res.fun is None else -float(res.fun)
    solve_elapsed=time.time()-t1
    sol=None
    if x is not None:
        sol={str(pts[i]):float(v) for i,v in enumerate(x) if abs(v)>1e-8}
    payload={'problem':'LP/MILP rank-1 projected Wang capacity maximum','field':'F2','rank_s':args.rank,'fixed_point':fixed,'integral':args.integral,'build_elapsed_sec':build_elapsed,'solve_elapsed_sec':solve_elapsed,'status':status,'message':message,'objective_max_selected':objective,'solution':sol,'solution_support_size':None if sol is None else len(sol),'constraint_count':len(cons),'constraint_size_cap_hist':{f'{a},{b0}':c0 for (a,b0),c0 in sorted(size_cap.items())},'compression':meta,'lut_meta_brief':{'coverage_ok':lut_meta.get('coverage_ok'),'conflict_count':lut_meta.get('conflict_count'),'subspace_count':lut_meta.get('subspace_count')},'meaning':'If the LP objective is below 20, pure rank-1 infeasibility follows by linear programming; otherwise integrality or stronger structure is needed.'}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:payload[k] for k in ['integral','status','message','objective_max_selected','solution_support_size','build_elapsed_sec','solve_elapsed_sec']},indent=2,sort_keys=True)); print('saved',args.out)

if __name__=='__main__': main()
