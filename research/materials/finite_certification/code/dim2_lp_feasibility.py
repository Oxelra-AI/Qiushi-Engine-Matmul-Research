#!/usr/bin/env python3
"""LP feasibility check for original-LUT dim-2 occupation raises.

If the nonnegative real relaxation of the occupation system is infeasible, the
raise has a potentially much simpler Farkas certificate.  If it is feasible,
certificate work must handle integrality.
"""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0,str(SCRIPT_DIR))
import dim2_replay_compat_graph as dg  # type: ignore
OUT=Path('data/dim2_raise_certs/dim2_lp_feasibility.json')

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--indices',default='479,484,485,486,487,488,489,490,491'); args=ap.parse_args()
    idxs=[int(x) for x in args.indices.split(',') if x.strip()]
    lut,cache=dg.load_lut_cache(); raw=dg.orbit_lbs_from_cache(cache,{})
    prof=json.loads(dg.PROFILE.read_text()); rec_by={int(r['index']):r for r in prof['dimension_2_orbits']}
    records=[]; t0=time.time()
    for idx in idxs:
        pr=rec_by[idx]; W=[int(x) for x in pr['constraint_values']]; L=int(pr['rank_lower_bound']); k=9-len(dg.rref_basis(W,9)); n=(1<<k)-1
        rows,meta=dg.node_rows(W,lut,cache,raw,L)
        A=[]; b=[]
        for mask,cap in rows:
            if cap>=L: continue
            row=np.zeros(n)
            for i in range(n):
                if (mask>>i)&1: row[i]=1.0
            if row.sum()==0:
                if cap<0:
                    # impossible 0 <= negative
                    pass
                continue
            A.append(row); b.append(float(cap))
        Aeq=np.ones((1,n)); beq=np.array([float(L)])
        res=linprog(c=np.zeros(n), A_ub=np.array(A), b_ub=np.array(b), A_eq=Aeq, b_eq=beq, bounds=[(0,None)]*n, method='highs')
        rec={'index':idx,'old_lb':L,'quotient_dim':k,'rows':len(rows),'lp_status':int(res.status),'lp_message':res.message,'lp_success':bool(res.success),'lp_fun':None if res.fun is None else float(res.fun)}
        if res.success:
            x=res.x; rec['nonzero_count']=int((x>1e-8).sum()); rec['max_x']=float(x.max()); rec['min_positive']=float(x[x>1e-8].min()) if (x>1e-8).any() else 0.0
            maxviol=max((float(np.dot(row,x)-cap) for row,cap in zip(A,b)), default=0.0); rec['max_violation']=maxviol; rec['sum']=float(x.sum())
        records.append(rec); print(idx,rec['lp_status'],rec['lp_success'],rec['lp_message'],flush=True)
    out={'schema':'s0908_dim2_lp_feasibility_v1','records':records,'summary':{'lp_feasible':[r['index'] for r in records if r['lp_success']], 'lp_infeasible':[r['index'] for r in records if not r['lp_success']]},'elapsed_sec':time.time()-t0}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(OUT),'summary':out['summary']},indent=2,sort_keys=True))
if __name__=='__main__': main()
