#!/usr/bin/env python3
"""Independent spot checks for the analysis primitive Wang row reduction.

This script does not import the analysis local maximization helper. For sampled
kept/dropped dim5 and dim6 rows it recomputes the annihilator color system and
brute-force/DFS maximizes n0 under the proper-subflag Wang rows. It checks that
dropped rows satisfy max_n0 <= cap and retained rows satisfy max_n0 > cap.
"""
from __future__ import annotations
import json, pickle, sys, time
from pathlib import Path
from itertools import combinations
from collections import defaultdict

SCRIPTS=Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints
from wang_capacity_lazy import pack_basis, rref_basis, unpack_basis

ROOT=Path('research/research_record')
OUTDIR=ROOT/'workspace/data/reduced_wang'
LUT=ROOT/'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl'
RED=OUTDIR/'primitive_reduced_rows.pkl'

def dot(a,b): return (a&b).bit_count()&1

def ann_basis(primal_basis,n=8):
    return list(rref_basis([q for q in range(1,1<<n) if all(dot(q,b)==0 for b in primal_basis)],n=n))

def xor_combo(basis,mask):
    z=0
    for i,b in enumerate(basis):
        if (mask>>i)&1: z^=int(b)
    return z

def dual_perp_key(qs):
    qs=list(qs); rows=[]; target=8-len(rref_basis(qs,n=8))
    for p in range(1,256):
        if all(dot(p,q)==0 for q in qs):
            nr=list(rref_basis(rows+[p],n=8))
            if len(nr)>len(rows):
                rows=nr
                if len(rows)==target: break
    return pack_basis(rref_basis(rows,n=8))

def local_Ls(dual_basis, rec_by_key):
    d=len(dual_basis); m=(1<<d)-1
    point_L=[]
    for qmask in range(1,m+1):
        q=xor_combo(dual_basis,qmask)
        point_L.append(int(rec_by_key[dual_perp_key([q])]['L']))
    line_L=[]
    if d>=2:
        for r in range(1,m+1):
            qs=[xor_combo(dual_basis,qmask) for qmask in range(1,m+1) if dot(qmask,r)==0]
            line_L.append(int(rec_by_key[dual_perp_key(qs)]['L']))
    return point_L,line_L

def feasible_with_n0(d,n0,point_L,line_L):
    m=(1<<d)-1; rem=19-n0
    if rem<0: return False,None
    vals=[0]*(m+1); vals[0]=n0
    # total 19 makes fiber sizes nonbinding for d=2,3.
    ub=[rem]*(m+1)
    for r in range(1,m+1):
        cap=19-int(line_L[r-1])
        ub[r]=min(ub[r], cap-n0)
    if any(ub[r]<0 for r in range(1,m+1)): return False,None
    order=sorted(range(1,m+1), key=lambda r:(ub[r], r))
    suffix=[0]*(len(order)+1)
    for i in range(len(order)-1,-1,-1): suffix[i]=suffix[i+1]+ub[order[i]]
    def point_possible(idx,remaining):
        assigned=set(order[:idx]); rest=order[idx:]
        for qmask in range(1,m+1):
            cur=sum(vals[v] for v in assigned if dot(qmask,v))
            extra=sum(ub[v] for v in rest if dot(qmask,v))
            if cur+extra < int(point_L[qmask-1]): return False
        return True
    def rec(idx,remaining):
        if remaining<0 or remaining>suffix[idx]: return False
        if not point_possible(idx,remaining): return False
        if idx==len(order):
            if remaining!=0: return False
            for qmask in range(1,m+1):
                if sum(vals[v] for v in range(1,m+1) if dot(qmask,v)) < int(point_L[qmask-1]): return False
            return True
        r=order[idx]
        for z in range(min(ub[r],remaining),-1,-1):
            vals[r]=z
            if rec(idx+1,remaining-z): return True
        vals[r]=0; return False
    ok=rec(0,rem)
    return ok, tuple(vals) if ok else None

def max_n0_independent(d,point_L,line_L):
    for n0 in range(19,-1,-1):
        ok,wit=feasible_with_n0(d,n0,point_L,line_L)
        if ok: return n0,wit
    return -1,None

def select_samples(records, kept, n_each=6):
    samples=[]
    for dim in (6,5):
        dropped=[r for r in records if int(r['dim8'])==dim and int(r['key8']) not in kept]
        kept_rows=[r for r in records if int(r['dim8'])==dim and int(r['key8']) in kept]
        # deterministic spread: head, middle, tail
        for status,arr in [('dropped',dropped),('kept',kept_rows)]:
            idxs=sorted(set([0,1,2,len(arr)//2,max(0,len(arr)-3),max(0,len(arr)-1)]))[:n_each]
            for idx in idxs:
                if arr: samples.append((status,arr[idx]))
    return samples

def main():
    t0=time.time(); OUTDIR.mkdir(parents=True,exist_ok=True)
    lut,_=load_lut(LUT); records,_=build_core_constraints(CoreQuotient(1),lut); rec_by={int(r['key8']):r for r in records}
    with RED.open('rb') as f: red=pickle.load(f)
    kept=set(int(k) for k in red['kept_key8'])
    results=[]; failures=[]
    for status,rec in select_samples(records,kept):
        key=int(rec['key8']); dim=int(rec['dim8']); L=int(rec['L']); cap=19-L
        db=ann_basis(list(unpack_basis(key))); d=len(db)
        pL,lL=local_Ls(db,rec_by)
        mx,wit=max_n0_independent(d,pL,lL)
        relation_ok=(mx<=cap) if status=='dropped' else (mx>cap)
        item={'expected_status':status,'key8':key,'dim8':dim,'L':L,'cap':cap,'dual_basis':db,'point_L':pL,'line_L_by_annihilator_color':lL,'independent_max_n0':mx,'witness_at_max':list(wit) if wit else None,'relation_ok':relation_ok}
        if not relation_ok: failures.append(item)
        results.append(item)
        print(status,'dim',dim,'L',L,'cap',cap,'max',mx,'ok',relation_ok)
    out=OUTDIR/'primitive_reduction_spotcheck.json'
    out.write_text(json.dumps({'schema':'primitive_reduction_spotcheck_v1','meaning':'Independent finite spot checks of retained/dropped dim5/6 row decisions using a separate local DFS maximizer; this supports but does not replace a formal proof of all 96,833 deletions.','elapsed_sec':time.time()-t0,'sample_count':len(results),'failure_count':len(failures),'results':results},indent=2)+"\n")
    print(json.dumps({'out':str(out),'sample_count':len(results),'failure_count':len(failures),'elapsed_sec':round(time.time()-t0,3)},indent=2))
if __name__=='__main__': main()
