#!/usr/bin/env python3
"""analysis pilot: count/enumerate local 16-color integer profiles for selected 4D dual flags.

This checks whether the local convex hull membership experiment can be done by full
profile enumeration for a few selected flags, rather than relying on an unverified
oracle loop. It uses the same E11 core Wang row lookup as earlier analysis.
"""
from __future__ import annotations
import json, sys, time
from pathlib import Path
from itertools import combinations
from collections import defaultdict

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints
from wang_capacity_lazy import rref_basis, pack_basis, subspace_points_from_basis, unpack_basis

ROOT = Path('research/research_record')
OUTDIR = ROOT/'workspace/data/local_hull'
LUT_PATH = ROOT/'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl'
BASE_SUPPORT = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]


def dot2(a,b): return (a & b).bit_count() & 1

def rref(rows, n=8): return list(rref_basis(list(rows), n=n))
def rank(rows,n=8): return len(rref(rows,n=n))
def intersection_basis(b1,b2,n=8):
    s1=set(subspace_points_from_basis(list(b1)))
    s2=set(subspace_points_from_basis(list(b2)))
    return rref(sorted(s1&s2), n=n) if s1&s2 else []

def annihilator_basis(primal_basis,n=8):
    vecs=[q for q in range(1,1<<n) if all(dot2(q,b)==0 for b in primal_basis)]
    return rref(vecs,n=n)

def eval_color(p, dual_basis):
    c=0
    for i,q in enumerate(dual_basis):
        if dot2(p,q): c |= 1<<i
    return c

def enumerate_subspaces(dim):
    pts=list(range(1,1<<dim))
    out=[]; seen=set()
    # enough to enumerate by all independent tuples up to dim; small dim=4
    for k in range(1,dim+1):
        for combo in combinations(pts,k):
            b=tuple(rref_basis(list(combo), n=dim))
            if len(b)==k and b not in seen:
                seen.add(b); out.append(b)
    return out

def build_local_constraints(ann_basis, rec_by_key):
    constraints=[]
    for e_basis in enumerate_subspaces(4):
        perp_colors=[]
        for v in range(16):
            if all(dot2(v,e)==0 for e in e_basis):
                perp_colors.append(v)
        lifted=[]
        for e in e_basis:
            q=0
            for k in range(4):
                if (e>>k)&1: q ^= ann_basis[k]
            lifted.append(q)
        primal_pts=[p for p in range(1,256) if all(dot2(p,q)==0 for q in lifted)]
        key=pack_basis(rref_basis(primal_pts,n=8))
        L=int(rec_by_key[key]['L'])
        constraints.append({'perp_colors':perp_colors,'cap':19-L,'L':L,'e_dim':len(e_basis),'primal_dim':len(rref_basis(primal_pts,n=8))})
    return constraints

def profile_of_support(support, ann_basis):
    prof=[0]*16
    for p in support:
        prof[eval_color(p,ann_basis)] += 1
    return prof

def enumerate_profiles(constraints, max_store=2000000):
    # Upper bounds from singleton-like constraints plus fiber sizes.
    ub=[15]+[16]*15
    for con in constraints:
        if len(con['perp_colors'])==1:
            v=con['perp_colors'][0]; ub[v]=min(ub[v], con['cap'])
    # Also c0+c_v constraints provide ub[v] <= cap if c0>=0.
    for con in constraints:
        if len(con['perp_colors'])==2 and 0 in con['perp_colors']:
            v=con['perp_colors'][0]^con['perp_colors'][1]
            ub[v]=min(ub[v], con['cap'])
    # Recursive variable ordering: colors with small ub first; keep zero first if small.
    order=sorted(range(16), key=lambda v:(ub[v], v))
    inv={v:i for i,v in enumerate(order)}
    con_idx_by_var=defaultdict(list)
    for ci,con in enumerate(constraints):
        for v in con['perp_colors']:
            con_idx_by_var[v].append(ci)
    caps=[c['cap'] for c in constraints]
    sums=[0]*len(constraints)
    assigned=[0]*16
    profiles=[]; count=0; truncated=False
    # Suffix max/min sums for remaining variables using ub.
    suffix_ub=[0]*(len(order)+1)
    for pos in range(len(order)-1,-1,-1):
        suffix_ub[pos]=suffix_ub[pos+1]+ub[order[pos]]
    t0=time.time()
    def dfs(pos, rem):
        nonlocal count, truncated
        if truncated: return
        if rem<0 or rem>suffix_ub[pos]: return
        if pos==len(order):
            if rem==0:
                count += 1
                if len(profiles)<max_store:
                    profiles.append(list(assigned))
                else:
                    truncated=True
            return
        v=order[pos]
        maxv=min(ub[v], rem)
        # Try values; small-to-large enough
        for val in range(maxv+1):
            ok=True
            # add
            for ci in con_idx_by_var[v]:
                sums[ci]+=val
                if sums[ci] > caps[ci]: ok=False
            if ok:
                assigned[v]=val
                dfs(pos+1, rem-val)
                assigned[v]=0
            for ci in con_idx_by_var[v]:
                sums[ci]-=val
            if truncated: return
    dfs(0,19)
    return {'ub':ub,'order':order,'count':count,'stored_count':len(profiles),'truncated':truncated,'elapsed_sec':time.time()-t0,'profiles':profiles if not truncated else profiles[:10]}

def main():
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0=time.time()
    lut,_=load_lut(LUT_PATH)
    core=CoreQuotient(1)
    records,_=build_core_constraints(core,lut)
    rec_by_key={int(r['key8']):r for r in records}
    # base violations
    bits=sum(1<<(p-1) for p in BASE_SUPPORT)
    violations=[]
    for r in records:
        occ=(int(r['point_bitset'])&bits).bit_count(); cap=19-int(r['L'])
        if occ>cap:
            violations.append({'key8':int(r['key8']),'dim8':int(r['dim8']),'L':int(r['L']),'basis8':list(unpack_basis(int(r['key8']))),'occ':occ,'cap':cap})
    d5=[v for v in violations if v['dim8']==5]
    pairs=[]
    for i,j in combinations(range(len(d5)),2):
        inter=intersection_basis(d5[i]['basis8'], d5[j]['basis8'])
        if len(inter)==4:
            pairs.append((i,j,inter))
    results=[]
    for idx,(i,j,inter) in enumerate(pairs[:2]):
        ann=annihilator_basis(inter)
        cons=build_local_constraints(ann,rec_by_key)
        prof=profile_of_support(BASE_SUPPORT,ann)
        local_viol=[c for c in cons if sum(prof[v] for v in c['perp_colors'])>c['cap']]
        enum=enumerate_profiles(cons,max_store=500000)
        results.append({'pair_index':idx,'viol_indices':[i,j],'intersection_basis':inter,'annihilator_basis':ann,'near_miss_profile':prof,'local_violation_count':len(local_viol),'constraint_L_cap_hist':dict(sorted({f"L{c['L']}_cap{c['cap']}":0 for c in cons}.items())),'enumeration_summary':{k:v for k,v in enum.items() if k!='profiles'},'profiles_head':enum['profiles'][:5]})
        print(idx, 'profiles', enum['count'], 'stored', enum['stored_count'], 'trunc', enum['truncated'], 'time', enum['elapsed_sec'])
    out=OUTDIR/'local_profile_count_pilot.json'
    out.write_text(json.dumps({'elapsed_sec':time.time()-t0,'violation_count':len(violations),'d5_count':len(d5),'good_pairs':len(pairs),'results':results},indent=2)+"\n")
    print('saved',out)
if __name__=='__main__': main()
