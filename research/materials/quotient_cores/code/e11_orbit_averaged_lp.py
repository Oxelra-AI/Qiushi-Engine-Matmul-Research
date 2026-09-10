#!/usr/bin/env python3
"""Orbit-averaged LP necessary condition for E11 rank-19 Wang occupation.

If an integral occupation vector x is feasible, its average over the verified
E11 quotient-action group is feasible and constant on the eight point orbits.
This script solves the resulting 8-variable LP using all subspace orbit
representatives.  Infeasibility would be a short symmetry-averaged obstruction;
feasibility is only a weak necessary-condition check.
"""
from __future__ import annotations

import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

SCRIPTS_A02 = Path('scripts')
if str(SCRIPTS_A02) not in sys.path: sys.path.insert(0, str(SCRIPTS_A02))
from e11_capacity_incremental_sat import build_or_load_constraint_cache, mask_to_points  # noqa: E402
from e11_quotient_action_verify import I3, P_row_stabilizer_generators, Q_col_stabilizer_generators, perm_for_pair  # noqa: E402


def point_orbits():
    I=I3()
    gens=[perm_for_pair(P,I) for P in P_row_stabilizer_generators()]+[perm_for_pair(I,Q) for Q in Q_col_stabilizer_generators()]
    unseen=set(range(1,256)); orbs=[]
    while unseen:
        seed=min(unseen); cur={seed}; changed=True
        while changed:
            changed=False
            for p in list(cur):
                for g in gens:
                    q=int(g[p])
                    if q not in cur:
                        cur.add(q); changed=True
        orbs.append(sorted(cur)); unseen-=cur
    return sorted(orbs, key=lambda o:(len(o),o[0]))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--cache',type=Path,default=Path('data/e11_capacity_sat/e11_capacity_cache.pkl'))
    ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank',type=int,default=19)
    ap.add_argument('--out',type=Path,default=Path('data/e11_subspace_orbits/orbit_averaged_lp.json'))
    args=ap.parse_args()
    t0=time.time()
    cache=build_or_load_constraint_cache(args.lut,args.cache,args.rank)
    orbs=point_orbits(); sizes=np.array([len(o) for o in orbs],dtype=float)
    p_to_o={p:i for i,o in enumerate(orbs) for p in o}
    # Variables n_i = total mass assigned to point orbit i in averaged vector. Each point gets n_i/size_i.
    A=[]; b=[]; used=0
    examples=[]
    for i,(m,cap) in enumerate(zip(cache['masks'], cache['caps'])):
        if not int(m) or int(cap)>=args.rank: continue
        coeff=np.zeros(len(orbs),dtype=float)
        for p in mask_to_points(int(m)):
            oi=p_to_o[p]; coeff[oi]+=1.0/sizes[oi]
        A.append(coeff); b.append(float(cap)); used+=1
        if len(examples)<10:
            examples.append({'index':i,'dim8':int(cache['dims'][i]),'L':int(cache['Ls'][i]),'cap':int(cap),'coeff':[float(x) for x in coeff]})
    A=np.vstack(A); b=np.array(b)
    Aeq=np.ones((1,len(orbs))); beq=np.array([args.rank],dtype=float)
    # Per-orbit total bounds from singleton caps. cap 2 for first two size-3 orbits, cap 1 otherwise in current data.
    point_caps={}
    for m,cap,d in zip(cache['masks'],cache['caps'],cache['dims']):
        if int(d)==1 and int(m).bit_count()==1:
            point_caps[int(m).bit_length()]=int(cap)
    bounds=[]
    for o in orbs:
        cset={point_caps[p] for p in o}
        bounds.append((0, len(o)*min(cset)))
    res=linprog(np.zeros(len(orbs)),A_ub=A,b_ub=b,A_eq=Aeq,b_eq=beq,bounds=bounds,method='highs')
    sol=None; max_slack_violation=None
    if res.success:
        sol=[float(x) for x in res.x]
        max_slack_violation=float(np.max(A@res.x-b))
    result={'problem':'orbit-averaged LP necessary condition for E11 complete Wang occupation','field':'F2','rank_s':args.rank,'point_orbits':[{'size':len(o),'points':o} for o in orbs],'bounds':bounds,'constraint_count':used,'status':int(res.status),'message':res.message,'success':bool(res.success),'solution_orbit_masses':sol,'max_ineq_lhs_minus_rhs':max_slack_violation,'examples_head':examples,'elapsed_sec':time.time()-t0,'meaning':'If infeasible, no integral occupation support exists. If feasible, this only says the group-averaged necessary condition does not obstruct E11 rank 19.'}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'success':result['success'],'message':result['message'],'solution':sol,'max_viol':max_slack_violation,'elapsed_sec':result['elapsed_sec']},indent=2,sort_keys=True))
    print(f'wrote {args.out}')

if __name__=='__main__': main()
