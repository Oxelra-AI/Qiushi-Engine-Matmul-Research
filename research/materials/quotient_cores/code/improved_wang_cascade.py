#!/usr/bin/env python3
"""Cascade tests after node-local occupation improvements.

This script uses node-local occupation closures (e.g. the 13 dim-3 orbit
raises found in analysis) as hypothetical/immediately-checkable strengthened
LUT values, then tests lower-dimensional orbit representatives with the
strengthened values.

It does not modify the canonical Wang LUT; it records the derived orbit-level
updates and every solver status so later proof work can replay or certify the
individual node closures.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from node_local_occupation_closure import (  # type: ignore
    CACHE_PATH, LUT_PATH, all_subspace_bases, strict_nonzero_proper_subspaces,
    rref_basis, pack_basis, in_span, free_bits_from_rref, lift_q, mask_from_qbasis,
    solve_local_cp, popcount,
)

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:
    cp_model = None

OUTDIR = Path("data/wang_analysis/cascade")


def load_all():
    with LUT_PATH.open('rb') as f:
        data = pickle.load(f)
    lut = data['lut'] if isinstance(data, dict) and 'lut' in data else data
    with CACHE_PATH.open('rb') as f:
        cache = pickle.load(f)
    return lut, cache


def make_orbit_lbs(cache, raises: Dict[int,int]) -> Dict[int,int]:
    d = {int(o['position']): int(o['raw_lb']) for o in cache['orbits']}
    for pos, val in raises.items():
        if int(val) > d[int(pos)]:
            d[int(pos)] = int(val)
    return d


def current_lb_for_key(key: int, lut: Dict[int,int], cache, orbit_lbs: Dict[int,int]) -> int:
    pos = cache['key_to_orbit'].get(int(key))
    if pos is None:
        return int(lut[int(key)])
    return int(orbit_lbs[int(pos)])


def current_node_constraints(W_basis: Sequence[int], lut, cache, orbit_lbs: Dict[int,int], support_size: int):
    W = rref_basis(W_basis, 9)
    d = len(W); k = 9-d
    free = free_bits_from_rref(W, 9)
    constraints: Dict[int,int] = {}
    cap_hist=Counter(); subdim_hist=Counter(); pop_hist=Counter(); source_lb_hist=Counter()
    neg=0; missing=0; taut=0
    for qbasis in strict_nonzero_proper_subspaces(k):
        U = rref_basis((*W, *[lift_q(q, free) for q in qbasis]), 9)
        key = pack_basis(U)
        if key not in lut:
            missing += 1; continue
        lb = current_lb_for_key(key,lut,cache,orbit_lbs)
        cap = int(support_size) - int(lb)
        mask = mask_from_qbasis(tuple(qbasis))
        if mask not in constraints or cap < constraints[mask]:
            constraints[mask] = cap
        cap_hist[cap]+=1; subdim_hist[len(qbasis)]+=1; pop_hist[popcount(mask)]+=1; source_lb_hist[lb]+=1
        if cap<0: neg+=1
        if cap>=support_size: taut+=1
    rows=sorted(constraints.items(), key=lambda mc:(mc[1], popcount(mc[0]), mc[0]))
    meta={'node_dim':d,'quotient_dim':k,'strict_subspace_rows':len(strict_nonzero_proper_subspaces(k)),'unique_masks':len(rows),'missing_lut_rows':missing,'cap_hist':dict(sorted((int(k),int(v)) for k,v in cap_hist.items())),'source_lb_hist':dict(sorted((int(k),int(v)) for k,v in source_lb_hist.items())),'subspace_dim_hist':dict(sorted((int(k),int(v)) for k,v in subdim_hist.items())),'mask_popcount_hist':dict(sorted((int(k),int(v)) for k,v in pop_hist.items())),'negative_cap_rows':neg,'tautological_rows':taut}
    return rows, meta


def load_initial_raises(path: Path, dim_filter: int|None=None) -> Dict[int,int]:
    data=json.loads(path.read_text())
    raises={}
    for r in data.get('results',[]):
        if dim_filter is not None and int(r['dim'])!=dim_filter: continue
        if r.get('solve',{}).get('feasible') is False:
            raises[int(r['position'])]=int(r['old_lb'])+1
    return raises


def test_dim(cache,lut,orbit_lbs,dim:int,time_limit:float,workers:int,limit:int=0):
    out=[]; summary=Counter(); checked=0
    for orb in cache['orbits']:
        if int(orb['dim'])!=dim: continue
        if limit and checked>=limit: break
        pos=int(orb['position']); L=int(orbit_lbs[pos]); support_size=L
        rows,meta=current_node_constraints(tuple(int(x) for x in orb['basis']), lut, cache, orbit_lbs, support_size)
        if meta['negative_cap_rows']:
            solve={'status':'NEGATIVE_CAP','feasible':False,'elapsed_sec':0.0}
        else:
            solve=solve_local_cp(9-dim,support_size,rows,time_limit,workers)
        feas=solve.get('feasible')
        status='unknown' if feas is None else ('feasible' if feas else 'infeasible')
        summary[status]+=1; summary[f'lb_{L}']+=1
        rec={'position':pos,'cert_index':int(orb.get('cert_index',pos)),'dim':dim,'old_or_current_lb':L,'attempted_new_lb':L+1,'support_size_tested':support_size,'proof_type':orb.get('proof_type'),'orbit_size':int(orb.get('orbit_size',-1)),'basis':[int(x) for x in orb['basis']],'constraint_meta':meta,'solve':solve}
        if solve.get('solution') is not None:
            sol=solve.pop('solution'); nz=[(i+1,int(v)) for i,v in enumerate(sol) if v]
            rec['solve']['solution_head']=nz[:40]; rec['solve']['solution_weight_check']=sum(v for _,v in nz)
        out.append(rec); checked+=1
        print(f"cascade dim={dim} idx={rec['cert_index']} L={L} rows={meta['unique_masks']} status={status} cp={solve.get('status')} elapsed={solve.get('elapsed_sec',0):.3f}",flush=True)
    return out, summary


def quotient_support_violations(pivot:int, support_q:List[int], lut, cache, orbit_lbs, length:int=19, max_report:int=20):
    """Scan all quotient rows U/<pivot> using current orbit LBs for a quotient support.

    support_q uses the highest-pivot-bit quotient coordinates from earlier scripts.
    """
    h = int(pivot).bit_length()-1
    def q_lift_old(q:int)->int:
        low=q & ((1<<h)-1); high=(q>>h)<<(h+1); return low|high
    full_lifts=[q_lift_old(int(q)) for q in support_q]
    W=rref_basis([pivot],9)
    k=8
    free=free_bits_from_rref(W,9)
    viol=0; cap_hist=Counter(); dim_hist=Counter(); lb_hist=Counter(); reports=[]; rows=0; tight=0
    for qbasis in strict_nonzero_proper_subspaces(k):
        U=rref_basis((*W,*[lift_q(q,free) for q in qbasis]),9)
        key=pack_basis(U)
        if key not in lut: continue
        lb=current_lb_for_key(key,lut,cache,orbit_lbs)
        cap=int(length)-int(lb)
        rows+=1; cap_hist[cap]+=1; dim_hist[len(U)]+=1; lb_hist[lb]+=1
        occ=sum(1 for a in full_lifts if in_span(a,U))
        if occ==cap: tight+=1
        if occ>cap:
            viol+=1
            if len(reports)<max_report:
                pos=cache['key_to_orbit'].get(int(key))
                reports.append({'cap':cap,'lb':lb,'occ':occ,'excess':occ-cap,'full_dim':len(U),'orbit_pos':None if pos is None else int(pos),'basis':[int(x) for x in U]})
    return {'pivot':pivot,'length':length,'support_q':support_q,'rows_scanned':rows,'violation_count':viol,'tight_count':tight,'cap_hist':dict(sorted((int(k),int(v)) for k,v in cap_hist.items())),'lb_hist':dict(sorted((int(k),int(v)) for k,v in lb_hist.items())),'dim_hist':dict(sorted((int(k),int(v)) for k,v in dim_hist.items())),'violation_head':reports}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--initial-closure',type=Path,required=True)
    ap.add_argument('--time-limit',type=float,default=30)
    ap.add_argument('--workers',type=int,default=8)
    ap.add_argument('--test-dims',default='2')
    ap.add_argument('--limit-per-dim',type=int,default=0)
    ap.add_argument('--scan-rank2-support',type=Path,default=Path('data/cegar/rank2_n19_cegar.json'))
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args()
    OUTDIR.mkdir(parents=True,exist_ok=True)
    t0=time.time()
    lut,cache=load_all()
    raises=load_initial_raises(args.initial_closure, dim_filter=3)
    orbit_lbs=make_orbit_lbs(cache,raises)
    all_results={}; summaries={}
    new_raises=dict(raises)
    for ds in args.test_dims.split(','):
        if not ds.strip(): continue
        dim=int(ds)
        res,summary=test_dim(cache,lut,orbit_lbs,dim,args.time_limit,args.workers,args.limit_per_dim)
        all_results[f'dim{dim}']=res; summaries[f'dim{dim}']=dict(summary)
        for r in res:
            if r['solve'].get('feasible') is False:
                pos=int(r['position']); val=int(r['old_or_current_lb'])+1
                if val>orbit_lbs[pos]:
                    orbit_lbs[pos]=val; new_raises[pos]=val
    support_scan=None
    if args.scan_rank2_support and args.scan_rank2_support.exists():
        d=json.loads(args.scan_rank2_support.read_text())
        # analysis support may be stored in slightly different fields.
        sup=d.get('support') or d.get('selected_support') or d.get('final_support')
        if sup is None:
            for r in reversed(d.get('rounds',[])):
                sup=r.get('support') or r.get('selected_support') or r.get('candidate_support')
                if sup is not None: break
        if sup is not None:
            support_scan=quotient_support_violations(17,[int(x) for x in sup],lut,cache,orbit_lbs,length=19)
    out={'schema':'improved_wang_cascade_v1','initial_closure':str(args.initial_closure),'initial_raises_from_dim3':{str(k):int(v) for k,v in sorted(raises.items())},'all_raises_after_tests':{str(k):int(v) for k,v in sorted(new_raises.items())},'test_summaries':summaries,'results':all_results,'rank2_support_scan_with_improved_lbs':support_scan,'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(args.out),'initial_raises':len(raises),'raises_after':len(new_raises),'summaries':summaries,'rank2_support_violations':None if support_scan is None else support_scan['violation_count'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__': main()
