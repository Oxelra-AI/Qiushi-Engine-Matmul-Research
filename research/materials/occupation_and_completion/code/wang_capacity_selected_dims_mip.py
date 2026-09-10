#!/usr/bin/env python3
"""HiGHS MIP for T-level Wang capacity using selected subspace dimensions.

This complements the lazy CP-SAT solver.  It is useful for code-theoretic
experiments such as adding all hyperplane (dim 8) constraints, which are exactly
the matrix-rank split minimum-weight inequalities in the [20,9] code view.
The output is always followed by optional full-Wang-capacity verification of any
returned support, so feasible for the selected dimensions is not mistaken for
full feasibility.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path
from typing import Sequence
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
from wang_capacity_lazy import unpack_basis, subspace_points_from_basis, matrix_rank_of_mask, in_rowspace

CANON_BY_RANK={1:1,2:1|16,3:1|16|256}


def load_lut(path:Path):
    with path.open('rb') as f: payload=pickle.load(f)
    return payload['lut'], payload.get('meta',{})


def parse_dims(s:str):
    out=[]
    for part in s.split(','):
        part=part.strip()
        if not part: continue
        if '-' in part:
            a,b=map(int,part.split('-',1)); out.extend(range(a,b+1))
        else:
            out.append(int(part))
    return sorted(set(out))


def full_verify(lut, sol, s, max_report=50):
    support=list(sol.items())
    t0=time.time(); viol=[]; bydim=Counter(); bylb=Counter(); worst={}
    for key,lb in lut.items():
        occ=0; basis=unpack_basis(key)
        for p,m in support:
            if in_rowspace(p,basis,n=9): occ+=m
        cap=s-lb
        if occ>cap:
            d=key&0xF; v={'key':key,'dim':d,'basis':list(basis),'lb':lb,'cap':cap,'occupancy':occ,'excess':occ-cap}
            viol.append(v); bydim[d]+=1; bylb[lb]+=1
            if d not in worst or (v['excess'],v['lb'],v['occupancy'])>(worst[d]['excess'],worst[d]['lb'],worst[d]['occupancy']): worst[d]=v
    viol.sort(key=lambda v:(v['excess'],v['lb'],v['occupancy'],-v['dim']), reverse=True)
    return {'elapsed_sec':time.time()-t0,'violation_count':len(viol),'violations_by_dim':dict(bydim),'violations_by_lb':dict(bylb),'max_excess':max((v['excess'] for v in viol), default=0),'worst_by_dim':{str(k):v for k,v in sorted(worst.items())},'violations_head':viol[:max_report]}


def solve(lut, s:int, dims:Sequence[int], branch_rank:int, time_limit:float, out:Path, do_full_check:bool):
    t0=time.time(); points=list(range(1,512))
    keys=[k for k in sorted(lut) if (k&0xF) in dims]
    extra=[]
    if branch_rank:
        canon=CANON_BY_RANK[branch_rank]
        extra.append(('fix',canon))
        if branch_rank>=2:
            for p in points:
                if matrix_rank_of_mask(p)<branch_rank: extra.append(('zero',p))
    m=1+len(keys)+len(extra); n=511
    A=lil_matrix((m,n),dtype=np.float64); lb=np.full(m,-np.inf); ub=np.empty(m,dtype=np.float64)
    A[0,:]=1.0; lb[0]=s; ub[0]=s
    row=1; bydim=Counter(); byL=Counter(); nnz=0
    prep0=time.time()
    for key in keys:
        pts=subspace_points_from_basis(unpack_basis(key))
        for p in pts:
            A[row,p-1]=1.0
        nnz += len(pts)
        L=lut[key]; lb[row]=-np.inf; ub[row]=s-L; bydim[key&0xF]+=1; byL[L]+=1; row+=1
    for typ,p in extra:
        A[row,p-1]=1.0
        if typ=='fix': lb[row]=1; ub[row]=s
        else: lb[row]=0; ub[row]=0
        row+=1
    prep=time.time()-prep0
    cons=LinearConstraint(A.tocsr(),lb,ub)
    res=milp(c=np.zeros(n), integrality=np.ones(n), bounds=Bounds(np.zeros(n),np.ones(n)), constraints=cons, options={'time_limit':time_limit,'mip_rel_gap':0.0,'disp':True})
    sol=None
    if getattr(res,'x',None) is not None:
        rounded=[int(round(v)) for v in res.x]
        sol={i+1:v for i,v in enumerate(rounded) if v}
    payload={'problem':'T-level Wang capacity selected-dimension MIP','field':'F2','rank_s':s,'dims':list(dims),'branch_rank':branch_rank,'branch_meaning':'0 unbranched; 1 fixes E11; 2 fixes E11+E22 and excludes rank1; 3 fixes identity and excludes rank1/rank2','selected_cut_count':len(keys),'cuts_by_dim':dict(bydim),'cuts_by_L':dict(byL),'extra_branch_rows':len(extra),'matrix_nnz_subspace_rows':nnz,'prepare_elapsed_sec':prep,'elapsed_sec':time.time()-t0,'status':int(res.status),'success':bool(res.success),'message':str(res.message),'fun':None if res.fun is None else float(res.fun),'solution':None if sol is None else {str(k):v for k,v in sorted(sol.items())},'solution_support':None if sol is None else len(sol),'solution_total':None if sol is None else sum(sol.values()),'solution_rank_hist':None if sol is None else dict(Counter(matrix_rank_of_mask(p) for p in sol for _ in range(sol[p])))}
    if sol is not None and do_full_check:
        payload['full_capacity_check']=full_verify(lut, sol, s)
    out.parent.mkdir(parents=True,exist_ok=True); out.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    brief={k:payload[k] for k in ['rank_s','dims','branch_rank','selected_cut_count','cuts_by_dim','status','success','message','elapsed_sec','solution_support','solution_rank_hist'] if k in payload}
    if 'full_capacity_check' in payload:
        brief['full_capacity_brief']={k:payload['full_capacity_check'][k] for k in ['violation_count','violations_by_dim','max_excess','elapsed_sec']}
    print(json.dumps(brief,indent=2,sort_keys=True)); print('saved',out)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank',type=int,default=20)
    ap.add_argument('--dims',default='1,2,3,8')
    ap.add_argument('--branch-rank',type=int,choices=[0,1,2,3],default=0)
    ap.add_argument('--time-limit',type=float,default=600)
    ap.add_argument('--full-check',action='store_true')
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args()
    lut,meta=load_lut(args.lut); print(f'loaded LUT {len(lut):,} coverage={meta.get("coverage_ok")} conflicts={meta.get("conflict_count")}')
    solve(lut,args.rank,parse_dims(args.dims),args.branch_rank,args.time_limit,args.out,args.full_check)
if __name__=='__main__': main()
