#!/usr/bin/env python3
"""Independent HiGHS MIP check for rank-20 T-level capacity branches using dim<=3 Wang cuts."""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix
SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
from wang_capacity_lazy import unpack_basis, subspace_points_from_basis, matrix_rank_of_mask
CANON_BY_RANK={1:1,2:1|16,3:1|16|256}

def load_lut(path):
    with open(path,'rb') as f: payload=pickle.load(f)
    return payload['lut'], payload.get('meta',{})

def solve(lut,s,branch_rank,time_limit,out):
    t0=time.time()
    keys=[k for k in sorted(lut) if 1 <= (k&0xF) <= 3]
    extra=[]
    if branch_rank:
        canon=CANON_BY_RANK[branch_rank]
        extra.append(('fix',canon))
        if branch_rank>=2:
            for p in range(1,512):
                if matrix_rank_of_mask(p)<branch_rank:
                    extra.append(('zero',p))
    m=1+len(keys)+len(extra); n=511
    A=lil_matrix((m,n),dtype=float); lb=np.full(m,-np.inf); ub=np.empty(m)
    A[0,:]=1.0; lb[0]=s; ub[0]=s
    by_dim=Counter(); by_L=Counter()
    row=1
    for k in keys:
        pts=subspace_points_from_basis(unpack_basis(k))
        for p in pts: A[row,p-1]=1.0
        L=lut[k]; lb[row]=-np.inf; ub[row]=s-L; by_dim[k&0xF]+=1; by_L[L]+=1; row+=1
    for typ,p in extra:
        A[row,p-1]=1.0
        if typ=='fix': lb[row]=1; ub[row]=s
        else: lb[row]=0; ub[row]=0
        row+=1
    cons=LinearConstraint(A.tocsr(),lb,ub)
    res=milp(np.zeros(n),integrality=np.ones(n),bounds=Bounds(np.zeros(n),np.full(n,s)),constraints=cons,options={'time_limit':time_limit,'mip_rel_gap':0.0,'disp':True})
    sol=None
    if getattr(res,'x',None) is not None:
        sol={i+1:int(round(v)) for i,v in enumerate(res.x) if int(round(v))}
    payload={'problem':'T-level Wang capacity dim<=3 branch MIP','field':'F2','rank_s':s,'branch_rank':branch_rank,'branch_meaning':'rank1 contains a rank-1 point fixed to E11; rank2 contains no rank1 and a rank2 point fixed; rank3 all points rank3 with I fixed','cut_count_dim_le_3':len(keys),'extra_branch_rows':len(extra),'cuts_by_dim':dict(by_dim),'cuts_by_L':dict(by_L),'status':int(res.status),'success':bool(res.success),'message':str(res.message),'fun':None if res.fun is None else float(res.fun),'elapsed_sec':time.time()-t0,'solution':None if sol is None else {str(k):v for k,v in sorted(sol.items())},'solution_support':None if sol is None else len(sol),'solution_total':None if sol is None else sum(sol.values())}
    out.parent.mkdir(parents=True,exist_ok=True); out.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    print(json.dumps(payload,indent=2,sort_keys=True)[:4000]); print('saved',out)

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')); ap.add_argument('--rank',type=int,default=20); ap.add_argument('--branch-rank',type=int,choices=[1,2,3],required=True); ap.add_argument('--time-limit',type=float,default=300); ap.add_argument('--out',type=Path,required=True); args=ap.parse_args(); lut,meta=load_lut(args.lut); print('loaded',len(lut),'coverage',meta.get('coverage_ok')); solve(lut,args.rank,args.branch_rank,args.time_limit,args.out)
if __name__=='__main__': main()
