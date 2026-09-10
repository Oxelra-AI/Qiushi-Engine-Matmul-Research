#!/usr/bin/env python3
"""Independent MILP replay of a stored analysis E11 multiset quotient-cut model.

This uses scipy.optimize.milp/HiGHS rather than OR-Tools CP-SAT.  It is an
independent solver check of feasibility status, not a proof certificate.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix
SCRIPTS=Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))
from core_capacity_from_wang_lut import CoreQuotient
from fixed_A_saturation import mat_rank_f2
from complete_core_and_transversal import ROOT, build_core_constraints
from quotient_rank_cuts import build_contractions, point_mask_for_q
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis

OUTDIR=ROOT/'workspace/data/quotient_rank_cuts'

def load_lut(path: Path):
    with path.open('rb') as f: payload=pickle.load(f)
    return {int(k):int(v) for k,v in payload['lut'].items()}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--source', type=Path, default=OUTDIR/'core_e11_multiset_quotient_sep_24r_fullstored.json')
    ap.add_argument('--time-limit', type=float, default=300.0)
    ap.add_argument('--out', type=Path, default=OUTDIR/'core_e11_multiset_quotient_sep_milp_replay.json')
    args=ap.parse_args(); args.out.parent.mkdir(parents=True, exist_ok=True)
    t0=time.time(); s=19; core=CoreQuotient(1)
    src=json.loads(args.source.read_text())
    T=np.load(ROOT/'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8)%2
    lut=load_lut(ROOT/'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records, meta=build_core_constraints(core,lut); record_by_key={int(r['key8']):r for r in records}
    contractions=build_contractions(T); masks={q: point_mask_for_q(q) for q in contractions}
    points=list(range(1,256)); p_index={p:p-1 for p in points}
    point_cap={}
    for p in points:
        key8=core.key8_from_rows([p]); key9=core.key9_from_key8(key8); point_cap[p]=max(0,min(s,s-int(lut[key9])))
    qcuts=[]; wang_keys=set()
    for r in records:
        if int(r['dim8']) in (1,2): wang_keys.add(int(r['key8']))
    for rnd in src.get('rounds',[]):
        for w in rnd.get('learned_wang_rows',[]): wang_keys.add(int(w['key8']))
        for c in rnd.get('learned_quotient_cuts',[]): qcuts.append(c)
    # q saturation vars only for q's occurring as sources.
    sat_qs=sorted({int(c['sources'][0]) for c in qcuts} | {int(c['sources'][1]) for c in qcuts})
    repeat_pts=[p for p,c in point_cap.items() if c>=2]
    nx=255; ny=len(sat_qs); nr=len(repeat_pts); nvars=nx+ny+nr
    y_index={q:nx+i for i,q in enumerate(sat_qs)}; r_index={p:nx+ny+i for i,p in enumerate(repeat_pts)}
    rows=[]; lbs=[]; ubs=[]
    def add(coeff, lb=-np.inf, ub=np.inf):
        rows.append(coeff); lbs.append(lb); ubs.append(ub)
    # total rank equality
    add({p_index[p]:1 for p in points}, s, s)
    # repeat encoding: x_p <= 1+r_p, x_p >= 2 r_p, sum r>=1
    add({r_index[p]:1 for p in repeat_pts}, 1, np.inf)
    for p in repeat_pts:
        add({p_index[p]:1, r_index[p]:-1}, -np.inf, 1)  # x-r <=1
        add({p_index[p]:1, r_index[p]:-2}, 0, np.inf)    # x-2r >=0
    # Wang rows
    for key8 in sorted(wang_keys):
        rec=record_by_key[key8]; cap=s-int(rec['L']); pts=subspace_points_from_basis(unpack_basis(key8))
        add({p_index[p]:1 for p in pts}, -np.inf, cap)
    # contraction lower bounds
    clb=0
    for q,c in contractions.items():
        rk=int(c['rank'])
        if rk>0:
            add({p_index[p]:1 for p in points if ((q&p).bit_count()&1)}, rk, np.inf); clb+=1
    # saturation y equivalence for source q's, using contraction lower bound already included.
    for q in sat_qs:
        rk=int(contractions[q]['rank']); M=s-rk; wcoeff={p_index[p]:1 for p in points if ((q&p).bit_count()&1)}
        # w - rk <= M*(1-y) -> w + M*y <= rk+M
        c=dict(wcoeff); c[y_index[q]]=M; add(c, -np.inf, rk+M)
        # w - rk >= 1 - M*y -> w + M*y >= rk+1
        c=dict(wcoeff); c[y_index[q]]=M; add(c, rk+1, np.inf)
    # quotient cuts: lhs >= req - req*(2-y1-y2) -> lhs - req*y1 - req*y2 >= -req
    for c in qcuts:
        q1,q2=map(int,c['sources']); req=int(c['requirement'])
        # Reconstruct outside points from side/source/target rather than trusting only current-model summary.
        union=masks[q1]|masks[q2]; target=int(c['target']); outside=masks[target] & (~union) & ((1<<255)-1)
        coeff={p_index[p]:1 for p in points if (outside>>(p-1))&1}
        coeff[y_index[q1]]=coeff.get(y_index[q1],0)-req
        coeff[y_index[q2]]=coeff.get(y_index[q2],0)-req
        add(coeff, -req, np.inf)
    build_sec=time.time()-t0
    A=lil_matrix((len(rows), nvars), dtype=float)
    for i,coeff in enumerate(rows):
        for j,v in coeff.items(): A[i,j]=v
    lbounds=np.zeros(nvars); ubounds=np.zeros(nvars)
    integrality=np.ones(nvars, dtype=int)
    for p in points:
        lbounds[p_index[p]]=0; ubounds[p_index[p]]=point_cap[p]
    for q in sat_qs: lbounds[y_index[q]]=0; ubounds[y_index[q]]=1
    for p in repeat_pts: lbounds[r_index[p]]=0; ubounds[r_index[p]]=1
    c=np.zeros(nvars)
    constraints=LinearConstraint(A.tocsr(), np.array(lbs,dtype=float), np.array(ubs,dtype=float))
    ts=time.time(); res=milp(c=c, integrality=integrality, bounds=Bounds(lbounds,ubounds), constraints=constraints, options={'time_limit': float(args.time_limit), 'mip_rel_gap': 0.0, 'presolve': True})
    solve_sec=time.time()-ts
    out={'schema':'core_qcut_milp_replay_v1','source':str(args.source),'field':'F2','core':'E11','rank_s':s,'solver':'scipy.optimize.milp/HiGHS','source_final_status':src.get('final_status'),'variables':{'x':nx,'sat_y':ny,'repeat_r':nr,'total':nvars},'constraints':{'total_rows':len(rows),'unique_wang_rows':len(wang_keys),'contraction_lower':clb,'stored_quotient_cuts':len(qcuts),'repeat_encoding_rows':1+2*len(repeat_pts),'sat_equivalence_rows':2*len(sat_qs)},'point_cap_distribution':{str(k):int(v) for k,v in sorted(Counter(point_cap.values()).items())},'complete_core_table_meta':meta,'status':int(res.status),'message':res.message,'success':bool(res.success),'fun':None if res.fun is None else float(res.fun),'mip_node_count':getattr(res,'mip_node_count',None),'mip_dual_bound':None if getattr(res,'mip_dual_bound',None) is None else float(res.mip_dual_bound),'mip_gap':None if getattr(res,'mip_gap',None) is None else float(res.mip_gap),'build_sec':round(build_sec,3),'solve_sec':round(solve_sec,3),'total_elapsed_sec':round(time.time()-t0,3)}
    if res.x is not None:
        vals=np.rint(res.x[:nx]).astype(int); counts={p:int(vals[p-1]) for p in points if vals[p-1]}; out['counts']={str(k):v for k,v in sorted(counts.items())}
    args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':int(res.status),'message':res.message,'success':bool(res.success),'vars':nvars,'rows':len(rows),'solve_sec':round(solve_sec,3)},sort_keys=True))
    print(f'Saved {args.out}')
if __name__=='__main__': main()
