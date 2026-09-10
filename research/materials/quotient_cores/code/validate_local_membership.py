#!/usr/bin/env python3
"""Validate analysis local-hull membership certificates.

The membership files are used only if the displayed convex combinations really
reconstruct the projected global LP point from integer local profiles that obey
all local Wang color inequalities. This script recomputes the induced local rows
from the E11 core LUT and checks the stored certificates independently of the
column-generation control flow.
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
from wang_capacity_lazy import pack_basis, rref_basis

ROOT = Path('research/research_record')
OUTDIR = ROOT/'workspace/data/local_hull'
LUT_PATH = ROOT/'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl'
MEM_PATH = OUTDIR/'fractional_local_membership.json'
GLOBAL_PATH = OUTDIR/'global_fractional_solution.json'


def dot2(a,b): return (a & b).bit_count() & 1

def enumerate_subspaces(dim):
    pts=list(range(1,1<<dim)); out=[]; seen=set()
    for k in range(1, dim+1):
        for combo in combinations(pts,k):
            b=tuple(rref_basis(list(combo), n=dim))
            if len(b)==k and b not in seen:
                seen.add(b); out.append(b)
    return out

def eval_color(p, ann):
    c=0
    for i,q in enumerate(ann):
        if dot2(p,q): c |= 1<<i
    return c

def build_local_constraints(ann, rec_by_key):
    constraints=[]
    for e_basis in enumerate_subspaces(4):
        perp=[]
        for v in range(16):
            if all(dot2(v,e)==0 for e in e_basis): perp.append(v)
        lifted=[]
        for e in e_basis:
            q=0
            for k in range(4):
                if (e>>k)&1: q ^= ann[k]
            lifted.append(q)
        primal_pts=[p for p in range(1,256) if all(dot2(p,q)==0 for q in lifted)]
        key=pack_basis(rref_basis(primal_pts,n=8))
        rec=rec_by_key[int(key)]
        L=int(rec['L']); cap=19-L
        constraints.append({'perp_colors':perp,'L':L,'cap':cap,'key8':int(key)})
    return constraints

def profile_feasible(profile, constraints):
    reasons=[]
    if len(profile)!=16: reasons.append('length')
    if sum(profile)!=19: reasons.append(f'sum={sum(profile)}')
    for i,v in enumerate(profile):
        if v < 0: reasons.append(f'neg_{i}')
        if i==0 and v>15: reasons.append('zero_fiber_capacity')
        if i>0 and v>16: reasons.append(f'fiber_capacity_{i}')
    for ci,c in enumerate(constraints):
        lhs=sum(profile[v] for v in c['perp_colors'])
        if lhs > c['cap']:
            reasons.append(f'row_{ci}_lhs{lhs}_cap{c["cap"]}')
            if len(reasons)>5: break
    return (not reasons), reasons

def main():
    t0=time.time()
    mem=json.loads(MEM_PATH.read_text())
    glob=json.loads(GLOBAL_PATH.read_text())
    x=np.array(glob['global_lp']['x_full'], dtype=float)
    lut,_=load_lut(LUT_PATH)
    core=CoreQuotient(1)
    records,_=build_core_constraints(core,lut)
    rec_by_key={int(r['key8']):r for r in records}
    results=[]
    failures=[]
    for pr in mem['pair_results']:
        ann=list(map(int, pr['annihilator_basis']))
        constraints=build_local_constraints(ann, rec_by_key)
        recomputed_target=np.zeros(16)
        for p in range(1,256):
            recomputed_target[eval_color(p,ann)] += x[p-1]
        stored_target=np.array(pr['target_profile'], dtype=float)
        target_err=float(np.max(np.abs(recomputed_target-stored_target)))
        hc=pr['hull_test']
        mcert=hc.get('membership_certificate')
        pair_result={'pair_index':pr['pair_index'],'status':hc.get('status'),'target_recompute_max_abs_error':target_err}
        if not mcert:
            pair_result['validated']=False
            pair_result['reason']='no_membership_certificate'
            failures.append(pair_result)
            results.append(pair_result); continue
        combo=mcert.get('active_combination',[])
        weight_sum=sum(float(term[1]) for term in combo)
        recon=np.zeros(16)
        bad_profiles=[]
        for term in combo:
            idx,wt,prof=term
            prof=[int(v) for v in prof]
            ok,reasons=profile_feasible(prof,constraints)
            if not ok:
                bad_profiles.append({'profile_index':idx,'reasons':reasons,'profile':prof})
            recon += float(wt)*np.array(prof,dtype=float)
        recon_err=float(np.max(np.abs(recon-stored_target))) if combo else float('inf')
        pair_result.update({
            'validated': (target_err<1e-8 and abs(weight_sum-1.0)<1e-8 and recon_err<1e-8 and not bad_profiles),
            'active_combination_size':len(combo),
            'weight_sum':weight_sum,
            'reconstruction_max_abs_error':recon_err,
            'bad_profile_count':len(bad_profiles),
            'bad_profiles_head':bad_profiles[:3],
            'local_constraint_count':len(constraints),
        })
        if not pair_result['validated']:
            failures.append(pair_result)
        results.append(pair_result)
    out=OUTDIR/'membership_validation.json'
    out.write_text(json.dumps({'elapsed_sec':time.time()-t0,'input':str(MEM_PATH),'global_input':str(GLOBAL_PATH),'pair_count':len(results),'failure_count':len(failures),'results':results},indent=2)+"\n")
    print(json.dumps({'out':str(out),'pair_count':len(results),'failure_count':len(failures),'elapsed_sec':round(time.time()-t0,3)},indent=2))
if __name__=='__main__': main()
