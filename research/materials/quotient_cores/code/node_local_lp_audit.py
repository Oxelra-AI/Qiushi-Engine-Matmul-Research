#!/usr/bin/env python3
"""Independent LP/MILP audit for node-local occupation closure results."""
from __future__ import annotations
import argparse, json, time
from pathlib import Path
from typing import List, Tuple
import numpy as np
from scipy.optimize import linprog, milp, Bounds, LinearConstraint
from scipy.sparse import coo_matrix, vstack

import sys
SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from node_local_occupation_closure import load_data, node_constraints  # type: ignore


def build_matrix(k:int, support_size:int, constraints:List[Tuple[int,int]]):
    n=(1<<k)-1
    rows=[]; cols=[]; vals=[]; upper=[]; names=[]
    for ri,(mask,cap) in enumerate(constraints):
        if cap>=support_size: continue
        if cap<0:
            # zero row with upper -1
            upper.append(float(cap)); names.append((mask,cap)); continue
        r=len(upper)
        for i in range(n):
            if (mask>>i)&1:
                rows.append(r); cols.append(i); vals.append(1.0)
        upper.append(float(cap)); names.append((mask,cap))
    A=coo_matrix((vals,(rows,cols)),shape=(len(upper),n)).tocsr()
    return A, np.array(upper), names


def solve_one(rec, lut, lp_time:float, mip_time:float):
    k=int(rec['quotient_dim']); L=int(rec['old_lb']); support_size=int(rec['support_size_tested'])
    basis=tuple(int(x) for x in rec['basis'])
    constraints, meta = node_constraints(basis,lut,support_size)
    A, upper, names = build_matrix(k,support_size,constraints)
    n=(1<<k)-1
    c=np.zeros(n)
    Aeq=np.ones((1,n)); beq=np.array([float(support_size)])
    bounds=[(0.0,float(support_size))]*n
    t=time.time()
    lp=linprog(c,A_ub=A,b_ub=upper,A_eq=Aeq,b_eq=beq,bounds=bounds,method='highs',options={'time_limit':lp_time})
    lp_rec={'status':int(lp.status),'message':str(lp.message),'success':bool(lp.success),'elapsed_sec':time.time()-t}
    if lp.x is not None:
        sl=upper-A.dot(lp.x)
        lp_rec.update({'min_slack':float(sl.min()) if len(sl) else None,'near_binding':int(np.sum(sl<=1e-8)),'sum':float(lp.x.sum()),'max_x':float(lp.x.max())})
    t=time.time()
    lc=LinearConstraint(vstack([A,coo_matrix(Aeq).tocsr()]).tocsr(),
                        np.r_[-np.inf*np.ones(len(upper)), float(support_size)],
                        np.r_[upper, float(support_size)])
    mi=milp(c=c,integrality=np.ones(n,dtype=np.int8),bounds=Bounds(np.zeros(n),np.full(n,float(support_size))),constraints=lc,options={'time_limit':mip_time,'mip_rel_gap':0})
    mi_rec={'status':int(mi.status),'message':str(mi.message),'success':bool(mi.success),'elapsed_sec':time.time()-t,'has_x':mi.x is not None}
    if mi.x is not None:
        x=np.rint(mi.x).astype(int)
        mi_rec.update({'sum':int(x.sum()),'support_nonzero_count':int(np.count_nonzero(x)),'max_x':int(x.max())})
    return {'cert_index':rec['cert_index'],'position':rec['position'],'dim':rec['dim'],'old_lb':L,'support_size':support_size,'quotient_dim':k,'constraint_meta':meta,'matrix_rows':int(A.shape[0]),'matrix_nnz':int(A.nnz),'lp':lp_rec,'milp':mi_rec}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--closure-json',type=Path,required=True)
    ap.add_argument('--select',choices=['infeasible','all'],default='infeasible')
    ap.add_argument('--lp-time',type=float,default=20)
    ap.add_argument('--mip-time',type=float,default=20)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args()
    closure=json.loads(args.closure_json.read_text())
    lut,_=load_data()
    targets=[]
    for r in closure['results']:
        feas=r['solve'].get('feasible')
        if args.select=='all' or feas is False:
            targets.append(r)
    out=[]; t0=time.time()
    for rec in targets:
        res=solve_one(rec,lut,args.lp_time,args.mip_time)
        out.append(res)
        print(f"idx={res['cert_index']} dim={res['dim']} L={res['old_lb']} LP {res['lp']['status']} {res['lp']['message'][:30]} MIP {res['milp']['status']} {res['milp']['message'][:30]}",flush=True)
    summary={'schema':'node_local_lp_audit_v1','source':str(args.closure_json),'select':args.select,'count':len(out),'lp_status_hist':{},'milp_status_hist':{},'records':out,'elapsed_sec':time.time()-t0}
    from collections import Counter
    summary['lp_status_hist']=dict(Counter(str(r['lp']['status']) for r in out))
    summary['milp_status_hist']=dict(Counter(str(r['milp']['status']) for r in out))
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(args.out),'count':len(out),'lp_status_hist':summary['lp_status_hist'],'milp_status_hist':summary['milp_status_hist'],'elapsed_sec':summary['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__': main()
