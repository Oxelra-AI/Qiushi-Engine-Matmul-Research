#!/usr/bin/env python3
"""Validate active-row local-hull memberships from analysis."""
from __future__ import annotations
import json, sys, time
from pathlib import Path
from itertools import combinations
import numpy as np

SCRIPTS=Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))
from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints
from wang_capacity_lazy import pack_basis, rref_basis

ROOT=Path('research/research_record')
OUTDIR=ROOT/'workspace/data/local_hull'
MEM_PATH=OUTDIR/'active_fractional_local_membership.json'
GLOBAL_PATH=OUTDIR/'global_fractional_solution.json'
LUT_PATH=ROOT/'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl'

def dot2(a,b): return (a&b).bit_count()&1

def enumerate_subspaces(dim):
    pts=list(range(1,1<<dim)); out=[]; seen=set()
    for k in range(1,dim+1):
        for combo in combinations(pts,k):
            b=tuple(rref_basis(list(combo),n=dim))
            if len(b)==k and b not in seen:
                seen.add(b); out.append(b)
    return out

def eval_color(p,ann):
    c=0
    for i,q in enumerate(ann):
        if dot2(p,q): c|=1<<i
    return c

def build_constraints(ann, rec_by_key):
    out=[]
    for e_basis in enumerate_subspaces(4):
        perp=[v for v in range(16) if all(dot2(v,e)==0 for e in e_basis)]
        lifted=[]
        for e in e_basis:
            q=0
            for k in range(4):
                if (e>>k)&1: q^=ann[k]
            lifted.append(q)
        pts=[p for p in range(1,256) if all(dot2(p,q)==0 for q in lifted)]
        key=pack_basis(rref_basis(pts,n=8)); L=int(rec_by_key[int(key)]['L']); out.append({'perp_colors':perp,'cap':19-L,'L':L})
    return out

def profile_ok(prof,cons):
    reasons=[]
    if sum(prof)!=19: reasons.append(f'sum={sum(prof)}')
    for i,v in enumerate(prof):
        if v<0: reasons.append(f'neg{i}')
        if i==0 and v>15: reasons.append('c0>15')
        if i>0 and v>16: reasons.append(f'c{i}>16')
    for ci,c in enumerate(cons):
        lhs=sum(prof[v] for v in c['perp_colors'])
        if lhs>c['cap']:
            reasons.append(f'row{ci}_lhs{lhs}_cap{c["cap"]}')
            if len(reasons)>5: break
    return not reasons, reasons

def main():
    t0=time.time(); mem=json.loads(MEM_PATH.read_text()); glob=json.loads(GLOBAL_PATH.read_text()); x=np.array(glob['global_lp']['x_full'])
    lut,_=load_lut(LUT_PATH); records,_=build_core_constraints(CoreQuotient(1),lut); rec_by_key={int(r['key8']):r for r in records}
    results=[]; failures=[]
    for pr in mem['pair_results']:
        ann=[int(v) for v in pr['annihilator_basis']]
        cons=build_constraints(ann,rec_by_key)
        target=np.zeros(16)
        for p in range(1,256): target[eval_color(p,ann)] += x[p-1]
        target_err=float(np.max(np.abs(target-np.array(pr['target_profile']))))
        cert=pr['hull_test'].get('membership_certificate')
        if not cert:
            item={'pair_index':pr['pair_index'],'validated':False,'reason':'no_membership','status':pr['hull_test'].get('status')}; failures.append(item); results.append(item); continue
        recon=np.zeros(16); bad=[]; wsum=0.0
        for idx,wt,prof in cert['active_combination']:
            prof=[int(v) for v in prof]; wsum+=float(wt); recon += float(wt)*np.array(prof)
            ok,reasons=profile_ok(prof,cons)
            if not ok: bad.append({'profile_index':idx,'reasons':reasons,'profile':prof})
        recon_err=float(np.max(np.abs(recon-np.array(pr['target_profile']))))
        item={'pair_index':pr['pair_index'],'validated':target_err<1e-8 and abs(wsum-1.0)<1e-8 and recon_err<1e-8 and not bad,'target_recompute_max_abs_error':target_err,'active_combination_size':len(cert['active_combination']),'weight_sum':wsum,'reconstruction_max_abs_error':recon_err,'bad_profile_count':len(bad),'local_constraint_count':len(cons)}
        if not item['validated']: failures.append(item)
        results.append(item)
    out=OUTDIR/'active_membership_validation.json'
    out.write_text(json.dumps({'elapsed_sec':time.time()-t0,'input':str(MEM_PATH),'global_input':str(GLOBAL_PATH),'pair_count':len(results),'failure_count':len(failures),'results':results},indent=2)+"\n")
    print(json.dumps({'out':str(out),'pair_count':len(results),'failure_count':len(failures),'elapsed_sec':round(time.time()-t0,3)},indent=2))
if __name__=='__main__': main()
