#!/usr/bin/env python3
"""Exhaustive Wang-capacity checks for cn122 restricted core A-factor multisets."""
from __future__ import annotations
import json, pickle, sys, time
from collections import Counter
from pathlib import Path
SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
from core_capacity_from_wang_lut import CoreQuotient, PIVOTS
from wang_capacity_lazy import load_qmm_a_factors, unpack_basis, subspace_points_from_basis, pack_basis
from wang_capacity_orbit_closed import extension_keys

def load_lut(path):
    with open(path,'rb') as f: payload=pickle.load(f)
    return payload['lut'], payload.get('meta',{})

def enumerate_subspace_keys(n=8):
    levels={0:{pack_basis(tuple())}}; all_keys=set(levels[0])
    for d in range(n):
        nxt=set()
        for key in levels[d]:
            for ekey in extension_keys(unpack_basis(key), n=n):
                if (ekey&0xF)==d+1: nxt.add(ekey)
        levels[d+1]=nxt; all_keys.update(nxt)
    return sorted(all_keys)

def bitset(points):
    b=0
    for p in points: b |= 1<<int(p)
    return b

def check_multiset(mult, core, lut, keys8, s):
    support_bits=bitset(mult.keys())
    extras=[(p,c-1) for p,c in mult.items() if c>1]
    viol=[]; by_dim=Counter(); by_L=Counter()
    for key8 in keys8:
        key9=core.key9_from_key8(key8); L=lut[key9]; cap=s-L
        pbits=bitset(subspace_points_from_basis(unpack_basis(key8)))
        occ=(pbits & support_bits).bit_count()
        for p,e in extras:
            if (pbits>>p)&1: occ+=e
        if occ>cap:
            vv={'key8':key8,'dim8':key8&0xF,'basis8':list(unpack_basis(key8)),'key9':key9,'basis9':list(unpack_basis(key9)),'L':L,'cap':cap,'occupancy':occ,'excess':occ-cap}
            viol.append(vv); by_dim[vv['dim8']]+=1; by_L[L]+=1
    viol.sort(key=lambda v:(v['excess'],v['L'],v['occupancy'],-v['dim8']), reverse=True)
    return {'subspaces_checked':len(keys8),'violation_count':len(viol),'violations_by_dim8':dict(by_dim),'violations_by_L':dict(by_L),'max_excess':max((v['excess'] for v in viol),default=0),'violations_head':viol[:20]}

def main():
    t0=time.time(); lut,meta=load_lut(Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    factors9=load_qmm_a_factors(Path('data/cn122_3x3_r23_repro/scheme.qmm'))
    keys8=enumerate_subspace_keys(8)
    out={'lut_meta_brief':{'coverage_ok':meta.get('coverage_ok'),'conflict_count':meta.get('conflict_count'),'subspace_count':meta.get('subspace_count')},'core_subspaces':len(keys8),'checks':{},'elapsed_sec':None}
    for name,pivot in PIVOTS.items():
        core=CoreQuotient(pivot); qs=[core.project9(a) for a in factors9]; surv=[q for q in qs if q]
        mult=Counter(surv); chk=check_multiset(mult,core,lut,keys8,len(surv))
        out['checks'][name]={'pivot_mask':pivot,'cn122_restricted_length':len(surv),'distinct_A_factors':len(mult),'max_multiplicity':max(mult.values()) if mult else 0,'A_multiset':{str(k):v for k,v in sorted(mult.items())},'exhaustive_capacity_check':chk}
        print(name,'len',len(surv),'violations',chk['violation_count'])
    out['elapsed_sec']=time.time()-t0
    path=Path('data/core_capacity/cn122_core_exhaustive_capacity_checks.json')
    path.parent.mkdir(parents=True,exist_ok=True); path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('saved',path,'elapsed',out['elapsed_sec'])
if __name__=='__main__': main()
