#!/usr/bin/env python3
"""Solve pivot-fixed active Wang row cores with SciPy/HiGHS MILP.

This is an independent solver check for active row sets obtained by CEGAR.  It
uses the same Boolean length-20 model as pivot_fixed_active_cnf.py, but through
HiGHS rather than CP-SAT or CDCL.
"""
from __future__ import annotations
import argparse, json, time
from pathlib import Path
from collections import Counter
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_matrix, vstack


def bit_in(words, p:int)->bool:
    return bool((int(words[p>>6])>>(p&63))&1)


def points_in_words(words):
    pts=[]
    for wi,w0 in enumerate(words):
        w=int(w0)
        while w:
            lb=w & -w
            b=lb.bit_length()-1
            p=wi*64+b
            if 1<=p<=511: pts.append(p)
            w ^= lb
    return pts


def read_rows(path:Path):
    rows=[]
    with path.open() as f:
        for line in f:
            if line.strip(): rows.append(json.loads(line))
    return rows


def build(active:Path,pivot:int,length:int,include_pairs=True):
    pts=[p for p in range(1,512) if p!=pivot]
    col={p:i for i,p in enumerate(pts)}
    ub=max(1,length-19)
    r_index=[]; c_index=[]; vals=[]; lower=[]; upper=[]
    names=[]
    def add_row(points,rhs,name):
        if rhs < 0:
            # impossible row 0 <= -1 represented as 0 row upper -1
            ri=len(lower); lower.append(-np.inf); upper.append(-1.0); names.append(name); return
        # tautological rows are harmless but skip for size.
        if rhs >= sum(ub for p in points): return
        ri=len(lower)
        for p in points:
            if p==pivot: continue
            r_index.append(ri); c_index.append(col[p]); vals.append(1.0)
        lower.append(-np.inf); upper.append(float(rhs)); names.append(name)
    if include_pairs:
        seen=set()
        for a in range(1,512):
            if a==pivot: continue
            b=a^pivot
            if b==0 or b==pivot: continue
            pair=tuple(sorted((a,b)))
            if pair in seen: continue
            seen.add(pair); add_row(list(pair),ub,f'pair_{pair[0]}_{pair[1]}')
    cap_hist=Counter(); dim_hist=Counter(); rhs_hist=Counter(); row_len_hist=Counter()
    for r in read_rows(active):
        words=[int(w) for w in r['words']]
        cap=int(r['cap']); dim=int(r.get('dim',-1)); rhs=cap-(1 if bit_in(words,pivot) else 0)
        row_pts=[p for p in points_in_words(words) if p!=pivot]
        add_row(row_pts,rhs,f"row_{r.get('row_index')}")
        cap_hist[cap]+=1; dim_hist[dim]+=1; rhs_hist[rhs]+=1; row_len_hist[len(row_pts)]+=1
    # Cardinality equality.
    ri=len(lower)
    for p in pts:
        r_index.append(ri); c_index.append(col[p]); vals.append(1.0)
    lower.append(float(length-1)); upper.append(float(length-1)); names.append('cardinality')
    A=coo_matrix((vals,(r_index,c_index)),shape=(len(lower),len(pts))).tocsr()
    cons=LinearConstraint(A,np.array(lower),np.array(upper))
    bounds=Bounds(np.zeros(len(pts)),np.full(len(pts),ub))
    return pts, cons, bounds, {'active':str(active),'pivot':pivot,'length':length,'ub':ub,'constraints':len(lower),'nonzeros':A.nnz,'cap_hist':dict(sorted((int(k),int(v)) for k,v in cap_hist.items())),'dim_hist':dict(sorted((int(k),int(v)) for k,v in dim_hist.items())),'rhs_hist':dict(sorted((int(k),int(v)) for k,v in rhs_hist.items())),'row_len_hist':dict(sorted((int(k),int(v)) for k,v in row_len_hist.items()))}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--active',type=Path,required=True)
    ap.add_argument('--pivot',type=int,required=True)
    ap.add_argument('--length',type=int,default=20)
    ap.add_argument('--time-limit',type=float,default=300)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args()
    t0=time.time(); pts,cons,bounds,meta=build(args.active,args.pivot,args.length)
    c=np.zeros(len(pts))
    integrality=np.ones(len(pts),dtype=np.int8)
    res=milp(c=c,integrality=integrality,bounds=bounds,constraints=cons,options={'time_limit':args.time_limit,'mip_rel_gap':0})
    rec={'schema':'pivot_fixed_active_milp_v1','meta':meta,'solve_status':int(res.status),'solve_message':str(res.message),'success':bool(res.success),'fun':None if res.fun is None else float(res.fun),'elapsed_sec':time.time()-t0}
    if res.x is not None:
        x=np.rint(res.x).astype(int)
        selected=[]
        for p,v in zip(pts,x): selected += [int(p)]*int(v)
        rec['selected_full_A_multiset']=[int(args.pivot)]+selected
        rec['selected_after_pivot_count']=int(sum(x))
        rec['max_multiplicity']=int(max(x)) if len(x) else 0
        rec['distinct_after_pivot']=int(np.count_nonzero(x))
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(rec,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':rec['solve_status'],'message':rec['solve_message'],'success':rec['success'],'has_x':res.x is not None,'elapsed_sec':rec['elapsed_sec'],'out':str(args.out)},indent=2,sort_keys=True))

if __name__=='__main__': main()
