#!/usr/bin/env python3
"""
analysis: complete F5 scan of the corrected single-free-Z4 residual model modulo
right diagonal recombination redundancy.

This extends z4_finite_block_scan.py from one LU chart to all of SL_3(F5)/T,
where T={diag(a,b,(ab)^-1)} acts on the right and leaves the residual unchanged.
For each representative it applies the exact block decomposition solver for the two
rank-10 Z4-stable patterns 4+4+2 and 4+4+1+1.  This is an exact finite-field result
for this model only; it is not a characteristic-zero theorem.
"""
from __future__ import annotations
import itertools, json, time, sys
from pathlib import Path
import numpy as np

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'z4_block_scan'
OUT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0,str(WS/'scripts'))
import z4_finite_block_scan as scan  # noqa:E402

P=5

def det3(M,p=P):
    a=M
    return (int(a[0,0])*(int(a[1,1])*int(a[2,2])-int(a[1,2])*int(a[2,1]))
            -int(a[0,1])*(int(a[1,0])*int(a[2,2])-int(a[1,2])*int(a[2,0]))
            +int(a[0,2])*(int(a[1,0])*int(a[2,1])-int(a[1,1])*int(a[2,0])))%p

def right_diag_variants(M,p=P):
    out=[]
    for a in range(1,p):
        for b in range(1,p):
            c=pow((a*b)%p,-1,p)
            D=np.diag(np.array([a,b,c],dtype=object))
            out.append(scan.matmul_mod(M,D,p))
    return out

def canon_right_diag(M,p=P):
    return min(tuple(int(x)%p for x in V.reshape(-1)) for V in right_diag_variants(M,p))

def enumerate_sl3_mod_T(p=P):
    seen={}; count_sl3=0
    vals=range(p)
    t0=time.time()
    for flat in itertools.product(vals, repeat=9):
        M=np.array(flat,dtype=object).reshape(3,3)
        if det3(M,p)==1:
            count_sl3 += 1
            key=canon_right_diag(M,p)
            if key not in seen:
                seen[key]=M.copy()
        if len(seen) and len(seen)%5000==0 and count_sl3%1000==0:
            pass
    return list(seen.values()), count_sl3, time.time()-t0

def fixed_single_tail_dict(ctx):
    p=ctx['p']; tail_idx=ctx['tail_idx']
    d={}
    for coords in itertools.product(range(p), repeat=3):
        l=np.zeros(9,dtype=object); l[0:3]=coords
        C=scan.cube_coeff(l,p)
        key=tuple(int(C[i])%p for i in tail_idx)
        if key not in d: d[key]=coords
    return d

def len2_plus_fixed_tail_dict(ctx,len2,single_fixed):
    p=ctx['p']
    d={}
    for k2,c2 in len2.items():
        for kf,cf in single_fixed.items():
            key=tuple((k2[i]+kf[i])%p for i in range(len(k2)))
            if key not in d: d[key]=(c2,cf)
    return d

def bilr_tail_positive(ctx,len2_plus_fixed):
    p=ctx['p']
    # Build BILR residual in y coordinates and subtract known size-4 cube orbits 3 and 7.
    sch=json.loads((WS/'data'/'ballard_z4_cyclic'/'ballard_z4_cyclic_scheme.json').read_text())
    cubes=[np.array(c,dtype=object).reshape(9)%p for c in sch['cubes']]
    forms_y=[scan.matmul_mod(ctx['change'].T,c.reshape(9,1),p).reshape(9) for c in cubes]
    C=(ctx['target_y']-scan.free_contribution(ctx['T0_y'],ctx['Ddiag'],p))%p
    H=(C-scan.orbit_cube(forms_y[3],ctx['Ddiag'],p,4)-scan.orbit_cube(forms_y[7],ctx['Ddiag'],p,4))%p
    off_nz=sum(1 for i in ctx['off_idx'] if int(H[i])%p)
    tail=tuple(int(H[i])%p for i in ctx['tail_idx'])
    return {'off_after_known_size4_nonzero':int(off_nz),'tail_in_len2_plus_fixed':bool(tail in len2_plus_fixed),
            'witness': len2_plus_fixed.get(tail)}

def main():
    t0=time.time()
    ctx=scan.build_context(P)
    len2,fixed2=scan.precompute_tails(ctx)
    single=fixed_single_tail_dict(ctx)
    len2fixed=len2_plus_fixed_tail_dict(ctx,len2,single)
    pos=bilr_tail_positive(ctx,len2fixed)
    reps,count_sl3,enum_sec=enumerate_sl3_mod_T(P)
    stats={'tested_representatives':0,'rank10_hits':0,'off_qz_rank2':0,'conic_two':0}
    hits=[]; start=time.time()
    for idx,M in enumerate(reps):
        Tcols=scan.matmul_mod(ctx['T0_y'],M,P)
        C=(ctx['target_y']-scan.free_contribution(Tcols,ctx['Ddiag'],P))%P
        qz,qw,_=scan.extract_blocks(C)
        if scan.rank_mod(qz,P)==2 and scan.rank_mod(qw,P)==2:
            stats['off_qz_rank2']+=1
            if len(scan.conic_points_rowspace(qz,P))==2:
                stats['conic_two']+=1
        decs=scan.decompose_C(C,ctx,len2,fixed2,max_records=2)
        stats['tested_representatives']+=1
        if decs:
            for rec in decs:
                ver=scan.tensor_verify_candidate(ctx,M,rec)
                hits.append({'rep_index':idx,'M':[[int(M[i,j]) for j in range(3)] for i in range(3)],'decomposition':rec,'verification':ver})
                print('HIT',hits[-1],flush=True)
            stats['rank10_hits']+=len(decs)
        if (idx+1)%5000==0:
            print(f"scanned {idx+1}/{len(reps)}, hits={stats['rank10_hits']}, elapsed={time.time()-start:.1f}s",flush=True)
    summary={'prime':P,'scope':'complete SL3(F5)/right-diagonal quotient for corrected single-free-Z4 residual; finite-field evidence only',
             'sl3_count':count_sl3,'right_diagonal_torus_size':(P-1)**2,'representative_count':len(reps),'enumeration_seconds':enum_sec,
             'tail_dictionary_sizes':{'length2':len(len2),'two_fixed':len(fixed2),'single_fixed':len(single),'length2_plus_fixed':len(len2fixed)},
             'bilr_4_4_2_1_tail_positive':pos,'stats':stats,'scan_seconds':time.time()-start,'total_seconds':time.time()-t0,'hits_saved':hits[:20]}
    out=OUT/'f5_sl3_modT_complete_scan.json'
    out.write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'out':str(out),'sl3_count':count_sl3,'representatives':len(reps),'stats':stats,'bilr_tail_positive':pos,'seconds':summary['total_seconds']},indent=2),flush=True)

if __name__=='__main__': main()
