#!/usr/bin/env python3
"""analysis independent replay of the peer dim-2 lower-bound reduction data.

This script reconstructs from definitions the row-to-node map for each
two-dimensional A-subspace orbit in Wang's certificate profile.  For a node W
with quotient Q=F2^9/W and support length L, every nonzero proper quotient
subspace H<Q gives a Wang occupation row

    sum_{q in H\setminus0} x_q <= L - LB(W+H),  sum_{q in Q\setminus0} x_q = L.

The script optionally uses a recorded overlay of already-raised supernodes,
then re-solves the dim-2 occupation systems and classifies which dim-2 orbits
can be spanned by two independent matrix-rank >=2 A-directions.

It is an independent replay/check of the mapping and finite integer systems,
not a formal proof certificate for UNSAT unless a separate certifying solver or
checked search trace is added.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from functools import lru_cache
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:
    cp_model = None

PROFILE = Path('data/wang_f2_lb20/cert_profile.json')
LUT_PATH = Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
CACHE_PATH = Path('data/wang_f2_lb20/wang_orbit_closed_cache.pkl')
OVERLAY_PATH = Path('data/wang_analysis/cascade/dim3_raises_to_dim2.json')
OUTDIR = Path('data/dim2_replay')


def popcnt(x:int)->int: return int(x).bit_count()


def rref_basis(rows: Iterable[int], nbits:int=9)->Tuple[int,...]:
    basis: List[int] = []
    for x0 in rows:
        x=int(x0)
        if x==0: continue
        for rb in basis:
            p=rb.bit_length()-1
            if (x>>p)&1: x ^= rb
        if x==0: continue
        p=x.bit_length()-1
        for i,rb in enumerate(basis):
            if (rb>>p)&1: basis[i]=rb^x
        basis.append(x); basis.sort(key=lambda z:z.bit_length(), reverse=True)
    return tuple(basis)


def pack_basis(basis: Sequence[int])->int:
    # Same profile/LUT convention: low 4 bits dimension, then 9-bit rows.
    x=0
    for i,b in enumerate(basis): x |= int(b) << (9*i)
    return (x<<4)|len(basis)


def in_span(v0:int, rref: Sequence[int])->bool:
    v=int(v0)
    for rb in rref:
        p=int(rb).bit_length()-1
        if p>=0 and ((v>>p)&1): v ^= int(rb)
    return v==0


def free_bits(W: Sequence[int], nbits:int=9)->List[int]:
    piv={int(rb).bit_length()-1 for rb in W if int(rb)}
    return [i for i in range(nbits) if i not in piv]


def lift_q(q:int, fb: Sequence[int])->int:
    v=0
    for i,bit in enumerate(fb):
        if (int(q)>>i)&1: v |= 1<<bit
    return v


@lru_cache(maxsize=None)
def all_subspace_bases(k:int)->Tuple[Tuple[int,...],...]:
    spaces={tuple()}
    for v in range(1,1<<k):
        add=[]
        for sp in spaces:
            if not in_span(v, sp): add.append(rref_basis((*sp,v), k))
        spaces.update(add)
    return tuple(sorted(spaces, key=lambda b:(len(b),b)))


@lru_cache(maxsize=None)
def strict_nonzero_proper_subspaces(k:int)->Tuple[Tuple[int,...],...]:
    return tuple(b for b in all_subspace_bases(k) if 0<len(b)<k)


@lru_cache(maxsize=None)
def mask_from_qbasis(qbasis: Tuple[int,...])->int:
    mask=0
    d=len(qbasis)
    for m in range(1,1<<d):
        q=0
        for i,b in enumerate(qbasis):
            if (m>>i)&1: q ^= int(b)
        mask |= 1 << (q-1)
    return mask


def rows3(x:int)->List[int]:
    return [sum(((int(x)>>(3*i+j))&1)<<j for j in range(3)) for i in range(3)]


def rank3(x:int)->int:
    piv: Dict[int,int]={}; r=0
    for row in rows3(x):
        y=row
        while y:
            p=y.bit_length()-1
            if p in piv: y ^= piv[p]
            else: piv[p]=y; r+=1; break
    return r


def nonzero_span(basis: Sequence[int])->List[int]:
    out=[]
    for m in range(1,1<<len(basis)):
        v=0
        for i,b in enumerate(basis):
            if (m>>i)&1: v ^= int(b)
        out.append(v)
    return sorted(out)


def load_lut()->Dict[int,int]:
    with LUT_PATH.open('rb') as f: d=pickle.load(f)
    return d['lut'] if isinstance(d,dict) and 'lut' in d else d


def load_overlay()->Dict[int,int]:
    out={}
    if not OVERLAY_PATH.exists(): return out
    d=json.loads(OVERLAY_PATH.read_text())
    for k,v in d.get('all_raises_after_tests',{}).items(): out[int(k)]=int(v)
    return out


def load_profile_orbits():
    prof=json.loads(PROFILE.read_text())
    return prof['dimension_2_orbits']


def node_rows(W_basis: Sequence[int], lut: Dict[int,int], overlay_key_to_lb: Dict[int,int], L:int):
    W=rref_basis(W_basis,9); k=9-len(W); fb=free_bits(W,9)
    constraints: Dict[int,int] = {}
    meta=Counter(); dimhist=Counter(); source_lbs=Counter(); caphist=Counter(); miss=0
    examples=[]
    for qbasis in strict_nonzero_proper_subspaces(k):
        U=rref_basis((*W,*[lift_q(q,fb) for q in qbasis]),9)
        key=pack_basis(U)
        lb=overlay_key_to_lb.get(key, lut.get(key))
        if lb is None:
            miss+=1; continue
        cap=int(L)-int(lb)
        mask=mask_from_qbasis(tuple(qbasis))
        if mask not in constraints or cap<constraints[mask]: constraints[mask]=cap
        dimhist[len(qbasis)]+=1; source_lbs[int(lb)]+=1; caphist[cap]+=1
        if len(examples)<20:
            examples.append({'qdim':len(qbasis),'U_dim':len(U),'U_key':int(key),'U_lb':int(lb),'cap':int(cap),'mask_popcount':popcnt(mask),'qbasis':[int(x) for x in qbasis],'U_basis':[int(x) for x in U]})
    return sorted(constraints.items(), key=lambda mc:(mc[1],popcnt(mc[0]),mc[0])), {
        'quotient_dim':k,'strict_subspace_rows':len(strict_nonzero_proper_subspaces(k)),'unique_masks':len(constraints),'missing_lut_or_overlay':miss,
        'quotient_subspace_dim_hist':{str(k):int(v) for k,v in sorted(dimhist.items())},
        'source_lb_hist':{str(k):int(v) for k,v in sorted(source_lbs.items())},
        'cap_hist':{str(k):int(v) for k,v in sorted(caphist.items())},
        'examples_head':examples,
    }


def solve_cp(rows: Sequence[Tuple[int,int]], k:int, L:int, time_limit:float, workers:int):
    if cp_model is None: return {'status':'NO_ORTOOLS','feasible':None}
    model=cp_model.CpModel(); npts=(1<<k)-1
    xs=[model.NewIntVar(0,L,f'x_{i+1}') for i in range(npts)]
    model.Add(sum(xs)==L)
    for mask,cap in rows:
        if cap<0: model.Add(0<=-1); continue
        pts=[i for i in range(npts) if (int(mask)>>i)&1]
        if pts and cap<L: model.Add(sum(xs[i] for i in pts)<=int(cap))
        elif not pts and cap<0: model.Add(0<=-1)
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(time_limit); solver.parameters.num_search_workers=int(workers); solver.parameters.random_seed=9031
    t0=time.time(); st=solver.Solve(model); elapsed=time.time()-t0; name=solver.StatusName(st)
    if st in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        sol=[int(solver.Value(x)) for x in xs]
        # replay all constraints exactly
        max_excess=max((sum(sol[i] for i in range(npts) if (int(mask)>>i)&1)-int(cap) for mask,cap in rows), default=0)
        nz=[(i+1,v) for i,v in enumerate(sol) if v]
        return {'status':name,'feasible':True,'elapsed_sec':elapsed,'conflicts':int(solver.NumConflicts()),'branches':int(solver.NumBranches()),'weight':sum(sol),'max_excess_replay':int(max_excess),'support_nonzero_count':len(nz),'max_multiplicity':max((v for _,v in nz), default=0),'solution_head':nz[:127]}
    if st==cp_model.INFEASIBLE:
        return {'status':name,'feasible':False,'elapsed_sec':elapsed,'conflicts':int(solver.NumConflicts()),'branches':int(solver.NumBranches())}
    return {'status':name,'feasible':None,'elapsed_sec':elapsed,'conflicts':int(solver.NumConflicts()),'branches':int(solver.NumBranches())}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--indices', default='478,479,480,481,482,483,484,485,486,487,488,489,490,491')
    ap.add_argument('--time-limit', type=float, default=60.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--out', type=Path, default=OUTDIR/'dim2_independent_replay.json')
    args=ap.parse_args()
    idxs={int(x) for x in args.indices.split(',') if x.strip()}
    lut=load_lut(); overlay_idx=load_overlay(); prof=load_profile_orbits()
    # Map every raised orbit index, including dim-3 supernodes, to its packed
    # representative basis via Wang's closed orbit cache.  The first version of
    # this replay used only dim-2 profile entries; that reproduced original
    # node-local rows but missed the dim-3 overlay rows that tighten dim-2 caps.
    with CACHE_PATH.open('rb') as f:
        cache=pickle.load(f)
    orbit_basis_by_idx={int(r.get('cert_index', r.get('index'))): [int(x) for x in r['basis']] for r in cache['orbits']}
    overlay_key_to_lb={}
    missing_overlay_indices=[]
    for idx,lb in overlay_idx.items():
        if idx in orbit_basis_by_idx:
            overlay_key_to_lb[pack_basis(rref_basis(orbit_basis_by_idx[idx],9))]=int(lb)
        else:
            missing_overlay_indices.append(int(idx))
    records=[]; t0=time.time()
    for rec in prof:
        idx=int(rec['index'])
        if idx not in idxs: continue
        W=[int(x) for x in rec['constraint_values']]
        ranks=[rank3(x) for x in nonzero_span(W)]
        high=sum(1 for r in ranks if r>=2)
        old=int(rec['rank_lower_bound'])
        current=int(overlay_idx.get(idx, old))
        L=current-1 if current>old else old  # support length used to test the recorded one-ARTIFACT raise when available; otherwise old.
        if idx in overlay_idx and overlay_idx[idx]>old:
            L=overlay_idx[idx]-1
        rows,meta=node_rows(W,lut,overlay_key_to_lb,L)
        sol=solve_cp(rows,9-len(rref_basis(W,9)),L,args.time_limit,args.workers)
        row_hash_input=';'.join(f'{m}:{c}' for m,c in rows)
        import hashlib
        records.append({'index':idx,'basis':W,'basis_rref':list(rref_basis(W,9)),'old_lb':old,'overlay_lb':current,'support_size_tested':L,'rank_pattern':ranks,'rank_ge2_count':high,'relevant_two_high_rank_generators':high>=2,'row_meta':meta,'row_sha256':hashlib.sha256(row_hash_input.encode()).hexdigest(),'solve':sol})
        print('idx',idx,'ranks',ranks,'old',old,'overlay',current,'L',L,'rows',len(rows),'status',sol['status'],'feasible',sol.get('feasible'),'elapsed',round(sol.get('elapsed_sec',0),3), flush=True)
    out={'schema':'s0908_dim2_independent_replay_v2','meaning':'Independent reconstruction of dim-2 quotient occupation row maps and CP-SAT replay, using Wang LUT values plus the recorded overlay mapped through the closed orbit cache. Infeasible statuses are solver evidence unless converted into checked proof traces.','overlay_source':str(OVERLAY_PATH),'missing_overlay_indices':missing_overlay_indices,'overlay_key_count':len(overlay_key_to_lb),'records':records,'summary':{'relevant':[r['index'] for r in records if r['relevant_two_high_rank_generators']],'relevant_still_below_19_after_overlay':[r['index'] for r in records if r['relevant_two_high_rank_generators'] and r['overlay_lb']<19],'infeasible_replay':[r['index'] for r in records if r['solve'].get('feasible') is False],'feasible_replay':[r['index'] for r in records if r['solve'].get('feasible') is True],'unknown_replay':[r['index'] for r in records if r['solve'].get('feasible') is None]},'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True, exist_ok=True); args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(args.out),'summary':out['summary'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__': main()
