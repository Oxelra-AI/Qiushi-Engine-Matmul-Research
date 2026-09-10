#!/usr/bin/env python3
"""analysis: positive controls for the corrected Z4 block solver over F5.

The robust F5 scan produced zero rank-10 hits.  This script checks that the same
qz/qw -> pzw -> tail pipeline actually recovers known decomposable cubics:
  * synthetic 4+4+2 instance;
  * synthetic 4+4+1+1 instance;
  * the actual BILR rank-23 residual 4+4+2+1 over F5, using an added tail dictionary.
It also records SHA-256 hashes of the active analysis scripts and data files.
"""
from __future__ import annotations
import hashlib, itertools, json, sys, time
from pathlib import Path
import numpy as np

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'z4_block_scan'
OUT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0,str(WS/'scripts'))
import z4_finite_block_scan as scan  # noqa:E402
import z4_f5_robust_rank10_scan as robust  # noqa:E402

P=5

def sha256(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for b in iter(lambda:f.read(1<<20), b''):
            h.update(b)
    return h.hexdigest()

def coeff_from_record(record,ctx):
    p=ctx['p']; D=ctx['Ddiag']
    C=(scan.orbit_cube(np.array(record['l1'],dtype=object),D,p,4)+scan.orbit_cube(np.array(record['l2'],dtype=object),D,p,4))%p
    if record['pattern']=='4+4+2':
        coords=record['tail_witness']
        l=np.zeros(9,dtype=object); l[0:3]=coords[0:3]; l[3:5]=coords[3:5]
        C=(C+scan.orbit_cube(l,D,p,2))%p
    elif record['pattern']=='4+4+1+1':
        f1,f2=record['tail_witness']
        for coords in (f1,f2):
            l=np.zeros(9,dtype=object); l[0:3]=coords
            C=(C+scan.cube_coeff(l,p))%p
    elif record['pattern']=='4+4+2+1':
        c2,cf=record['tail_witness']
        l=np.zeros(9,dtype=object); l[0:3]=c2[0:3]; l[3:5]=c2[3:5]
        C=(C+scan.orbit_cube(l,D,p,2))%p
        lf=np.zeros(9,dtype=object); lf[0:3]=cf
        C=(C+scan.cube_coeff(lf,p))%p
    else:
        raise ValueError(record['pattern'])
    return C%p

def diff_nz(A,B,p=P):
    return int(sum(1 for x in ((np.array(A,dtype=object)-np.array(B,dtype=object))%p) if int(x)%p))

def fixed_single_tail_dict(ctx):
    p=ctx['p']; tail_idx=ctx['tail_idx']; d={}
    for coords in itertools.product(range(p), repeat=3):
        l=np.zeros(9,dtype=object); l[0:3]=coords
        C=scan.cube_coeff(l,p)
        key=tuple(int(C[i])%p for i in tail_idx)
        d.setdefault(key,coords)
    return d

def len2_plus_fixed_tail_dict(ctx,len2,single):
    p=ctx['p']; d={}
    for k2,c2 in len2.items():
        for kf,cf in single.items():
            key=tuple((k2[i]+kf[i])%p for i in range(len(k2)))
            d.setdefault(key,(c2,cf))
    return d

def decompose_with_taildict(C,ctx,qzd,qwd,taildict,pattern,max_hits=1):
    p=ctx['p']; D=ctx['Ddiag']; tail_idx=ctx['tail_idx']; off_idx=ctx['off_idx']
    qz,qw,pzw=scan.extract_blocks(C)
    keyqz=tuple(int(qz[i//3,i%3])%p for i in range(6))
    keyqw=tuple(int(qw[i//3,i%3])%p for i in range(6))
    target_pzw=robust.pzw_from_block(pzw)
    hits=[]; qz_seen=0; qw_seen=0; p_seen=0
    for z1,z2,q1,q2 in qzd.get(keyqz,[]):
        qz_seen+=1
        for w1,w2 in qwd.get((q1,q2,keyqw),[]):
            qw_seen+=1
            psols=robust.solve_p_for_pzw(target_pzw,z1,z2,w1,w2,p)
            for ps in psols:
                p_seen+=1
                l1=np.zeros(9,dtype=object); l2=np.zeros(9,dtype=object)
                l1[0:3]=ps[:3]; l1[3:5]=q1; l1[5:7]=z1; l1[7:9]=w1
                l2[0:3]=ps[3:6]; l2[3:5]=q2; l2[5:7]=z2; l2[7:9]=w2
                H=(C-scan.orbit_cube(l1,D,p,4)-scan.orbit_cube(l2,D,p,4))%p
                if any(int(H[i])%p for i in off_idx):
                    continue
                tail=tuple(int(H[i])%p for i in tail_idx)
                if tail in taildict:
                    rec={'pattern':pattern,'l1':[int(x)%p for x in l1],'l2':[int(x)%p for x in l2],
                         'tail_witness':taildict[tail],
                         'solver_stats':{'qz_witnesses_seen':qz_seen,'qw_witnesses_seen':qw_seen,'p_solutions_seen':p_seen}}
                    hits.append(rec)
                    if len(hits)>=max_hits:
                        return hits
    return hits

def run_synthetic_controls(ctx,qzd,qwd,len2,fixed2):
    p=ctx['p']; D=ctx['Ddiag']
    tests=[]
    l1=np.array([1,2,0,1,3,1,4,2,1],dtype=object)%p
    l2=np.array([0,1,2,4,1,2,1,3,2],dtype=object)%p
    tail=np.zeros(9,dtype=object); tail[0:5]=[2,1,4,1,3]
    C=(scan.orbit_cube(l1,D,p,4)+scan.orbit_cube(l2,D,p,4)+scan.orbit_cube(tail,D,p,2))%p
    hits=robust.decompose_robust(C,ctx,qzd,qwd,len2,fixed2,max_hits=1)
    tests.append({'name':'synthetic_4+4+2','hit_count':len(hits),
                  'first_hit_pattern':hits[0]['pattern'] if hits else None,
                  'reconstruction_nonzero':diff_nz(coeff_from_record(hits[0],ctx),C,p) if hits else None})
    f1=np.zeros(9,dtype=object); f2=np.zeros(9,dtype=object); f1[0:3]=[1,2,3]; f2[0:3]=[4,0,1]
    C=(scan.orbit_cube(l1,D,p,4)+scan.orbit_cube(l2,D,p,4)+scan.cube_coeff(f1,p)+scan.cube_coeff(f2,p))%p
    hits=robust.decompose_robust(C,ctx,qzd,qwd,len2,fixed2,max_hits=1)
    tests.append({'name':'synthetic_4+4+1+1','hit_count':len(hits),
                  'first_hit_pattern':hits[0]['pattern'] if hits else None,
                  'reconstruction_nonzero':diff_nz(coeff_from_record(hits[0],ctx),C,p) if hits else None})
    return tests

def bilr_control(ctx,qzd,qwd,len2fixed):
    p=ctx['p']
    C=(ctx['target_y']-scan.free_contribution(ctx['T0_y'],ctx['Ddiag'],p))%p
    hits=decompose_with_taildict(C,ctx,qzd,qwd,len2fixed,'4+4+2+1',max_hits=1)
    return {'hit_count':len(hits), 'first_hit':hits[0] if hits else None,
            'reconstruction_nonzero':diff_nz(coeff_from_record(hits[0],ctx),C,p) if hits else None}

def main():
    t0=time.time(); ctx=scan.build_context(P)
    len2,fixed2=scan.precompute_tails(ctx)
    single=fixed_single_tail_dict(ctx); len2fixed=len2_plus_fixed_tail_dict(ctx,len2,single)
    qzd,maxqz=robust.build_qz_dict(P); qwd,maxqw=robust.build_qw_dict(P)
    synthetic=run_synthetic_controls(ctx,qzd,qwd,len2,fixed2)
    bilr=bilr_control(ctx,qzd,qwd,len2fixed)
    paths=[
        WS/'scripts'/'z4_pairing_pencil.py',
        WS/'scripts'/'z4_finite_block_scan.py',
        WS/'scripts'/'z4_f5_sl3_quotient_scan.py',
        WS/'scripts'/'z4_f5_robust_rank10_scan.py',
        WS/'scripts'/'z4_f5_conciseness_scan.py',
        WS/'scripts'/'z4_block_solver_controls.py',
        WS/'data'/'z4_pairing_pencil'/'pairing_pencil_positive_control.json',
        WS/'data'/'z4_block_scan'/'f5_sl3_modT_robust_rank10_scan.json',
        WS/'data'/'z4_block_scan'/'f5_sl3_modT_conciseness_scan.json',
    ]
    hashes={str(p.relative_to(WS)):sha256(p) for p in paths if p.exists()}
    summary={'prime':P,'scope':'positive controls for corrected Z4 block solver over F5; validates solver pipeline but is not a lower-bound theorem',
             'dictionary_sizes':{'qz':len(qzd),'qw':len(qwd),'max_qz_bucket':maxqz,'max_qw_bucket':maxqw,'length2_tail':len(len2),'two_fixed_tail':len(fixed2),'length2_plus_fixed_tail':len(len2fixed)},
             'synthetic_rank10_controls':synthetic,
             'bilr_4_4_2_1_control':bilr,
             'all_controls_pass': all(t['hit_count']>0 and t['reconstruction_nonzero']==0 for t in synthetic) and bilr['hit_count']>0 and bilr['reconstruction_nonzero']==0,
             'artifact_hashes_sha256':hashes,'seconds':time.time()-t0}
    out=OUT/'f5_block_solver_positive_controls.json'; out.write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'out':str(out),'all_controls_pass':summary['all_controls_pass'],'synthetic':synthetic,'bilr':{'hit_count':bilr['hit_count'],'reconstruction_nonzero':bilr['reconstruction_nonzero']},'seconds':summary['seconds']},indent=2),flush=True)
if __name__=='__main__': main()
