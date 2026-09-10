#!/usr/bin/env python3
"""analysis: robust F5 scan including degenerate qz/qw branches.

The first F5 scan used the generic pencil-conic extraction requiring qz and qw rank 2.
This script removes that generic assumption for the complete SL3(F5)/right-diagonal
quotient.  It precomputes exact finite dictionaries for the two size-4 orbit blocks:
  qz2(q,z) and qw2(q,w)
for all exact q,z,w in F5^2, then matches every residual C_M.  Thus rank-deficient
qz/qw branches are also tested for the Z4-stable patterns 4+4+2 and 4+4+1+1.

Still finite-field/model-local evidence only; it is not a characteristic-zero proof.
"""
from __future__ import annotations
import itertools, json, time, sys
from pathlib import Path
import numpy as np
WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'z4_block_scan'
OUT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0,str(WS/'scripts'))
import z4_finite_block_scan as scan
import z4_f5_sl3_quotient_scan as qscan
P=5

def q_block_vec(q,z,p=P):
    q0,q1=int(q[0])%p,int(q[1])%p; z0,z1=int(z[0])%p,int(z[1])%p
    sq=[(12*z0*z0)%p,(24*z0*z1)%p,(12*z1*z1)%p]
    return ((q0*sq[0])%p,(q0*sq[1])%p,(q0*sq[2])%p,(q1*sq[0])%p,(q1*sq[1])%p,(q1*sq[2])%p)

def pzw_vec(pv,z,w,p=P):
    out=[]
    for pi in range(3):
        for zi in range(2):
            for wi in range(2):
                out.append((24*int(pv[pi])*int(z[zi])*int(w[wi]))%p)
    return tuple(out)

def pzw_from_block(pzw):
    return tuple(int(pzw[pi,zi,wi])%P for pi in range(3) for zi in range(2) for wi in range(2))

def build_qz_dict(p=P):
    vec2=list(itertools.product(range(p), repeat=2))
    d={}; max_bucket=0
    for z1 in vec2:
        for z2 in vec2:
            for q1 in vec2:
                v1=q_block_vec(q1,z1,p)
                for q2 in vec2:
                    v2=q_block_vec(q2,z2,p)
                    key=tuple((v1[i]+v2[i])%p for i in range(6))
                    # F5 is small enough to store all witnesses; completeness matters more than bucket size.
                    bucket=d.setdefault(key,[])
                    bucket.append((z1,z2,q1,q2))
                    if len(bucket)>max_bucket: max_bucket=len(bucket)
    return d, max_bucket

def build_qw_dict(p=P):
    vec2=list(itertools.product(range(p), repeat=2))
    d={}; max_bucket=0
    for q1 in vec2:
        for q2 in vec2:
            for w1 in vec2:
                v1=q_block_vec(q1,w1,p)
                for w2 in vec2:
                    v2=q_block_vec(q2,w2,p)
                    key=(q1,q2,tuple((v1[i]+v2[i])%p for i in range(6)))
                    bucket=d.setdefault(key,[])
                    bucket.append((w1,w2))
                    if len(bucket)>max_bucket: max_bucket=len(bucket)
    return d,max_bucket

def solve_p_for_pzw(target,z1,z2,w1,w2,p=P):
    Ap=np.zeros((12,6),dtype=object); b=np.array(target,dtype=object)
    row=0
    for pi in range(3):
        for zi in range(2):
            for wi in range(2):
                Ap[row,pi]=(24*int(z1[zi])*int(w1[wi]))%p
                Ap[row,3+pi]=(24*int(z2[zi])*int(w2[wi]))%p
                row+=1
    sols=scan.affine_solutions(Ap,b,p,max_solutions=20000)
    return [] if sols is None else sols

def fixed_single_tail_dict(ctx):
    p=ctx['p']; tail_idx=ctx['tail_idx']; d={}
    for coords in itertools.product(range(p), repeat=3):
        l=np.zeros(9,dtype=object); l[0:3]=coords
        C=scan.cube_coeff(l,p); key=tuple(int(C[i])%p for i in tail_idx)
        d.setdefault(key,coords)
    return d

def decompose_robust(C,ctx,qzdict,qwdict,len2,fixed2,max_hits=1):
    p=ctx['p']; Ddiag=ctx['Ddiag']; tail_idx=ctx['tail_idx']; off_idx=ctx['off_idx']
    qz,qw,pzw=scan.extract_blocks(C)
    keyqz=tuple(int(qz[i//3,i%3])%p for i in range(6))
    keyqw=tuple(int(qw[i//3,i%3])%p for i in range(6))
    target_pzw=pzw_from_block(pzw)
    hits=[]; candidates=0; qw_candidates=0; p_solved=0
    for z1,z2,q1,q2 in qzdict.get(keyqz,[]):
        candidates+=1
        wlist=qwdict.get((q1,q2,keyqw),[])
        if not wlist: continue
        for w1,w2 in wlist:
            qw_candidates+=1
            psols=solve_p_for_pzw(target_pzw,z1,z2,w1,w2,p)
            if not psols: continue
            for ps in psols:
                p_solved+=1
                l1=np.zeros(9,dtype=object); l2=np.zeros(9,dtype=object)
                l1[0:3]=ps[:3]; l1[3:5]=q1; l1[5:7]=z1; l1[7:9]=w1
                l2[0:3]=ps[3:6]; l2[3:5]=q2; l2[5:7]=z2; l2[7:9]=w2
                H=(C-scan.orbit_cube(l1,Ddiag,p,4)-scan.orbit_cube(l2,Ddiag,p,4))%p
                if any(int(H[i])%p for i in off_idx):
                    continue
                tail=tuple(int(H[i])%p for i in tail_idx)
                if tail in len2:
                    hits.append({'pattern':'4+4+2','l1':[int(x) for x in l1],'l2':[int(x) for x in l2],'tail_witness':len2[tail], 'stats':{'qz_candidates_seen':candidates,'qw_candidates_seen':qw_candidates,'p_solutions_seen':p_solved}})
                if tail in fixed2:
                    hits.append({'pattern':'4+4+1+1','l1':[int(x) for x in l1],'l2':[int(x) for x in l2],'tail_witness':fixed2[tail], 'stats':{'qz_candidates_seen':candidates,'qw_candidates_seen':qw_candidates,'p_solutions_seen':p_solved}})
                if len(hits)>=max_hits: return hits
    return hits

def main():
    t0=time.time(); print('building context/tails',flush=True)
    ctx=scan.build_context(P); len2,fixed2=scan.precompute_tails(ctx)
    print('building qz/qw dictionaries',flush=True)
    qzd,maxqz=build_qz_dict(P); qwd,maxqw=build_qw_dict(P)
    print(f'qz keys={len(qzd)}, qw keys={len(qwd)}, max buckets {maxqz}/{maxqw}',flush=True)
    reps,count_sl3,enum_sec=qscan.enumerate_sl3_mod_T(P)
    stats={'tested':0,'hits':0,'generic_rank2_both':0,'degenerate_qz_or_qw':0,'qz_key_missing':0,'no_qw_for_any_qz':0}
    hits=[]; start=time.time(); candidate_sum=0
    for idx,M in enumerate(reps):
        Tcols=scan.matmul_mod(ctx['T0_y'],M,P)
        C=(ctx['target_y']-scan.free_contribution(Tcols,ctx['Ddiag'],P))%P
        qz,qw,_=scan.extract_blocks(C)
        if scan.rank_mod(qz,P)==2 and scan.rank_mod(qw,P)==2: stats['generic_rank2_both']+=1
        else: stats['degenerate_qz_or_qw']+=1
        keyqz=tuple(int(qz[i//3,i%3])%P for i in range(6))
        if keyqz not in qzd: stats['qz_key_missing']+=1
        decs=decompose_robust(C,ctx,qzd,qwd,len2,fixed2,max_hits=2)
        stats['tested']+=1
        if decs:
            for rec in decs:
                ver=scan.tensor_verify_candidate(ctx,M,rec)
                hits.append({'rep_index':idx,'M':[[int(M[i,j]) for j in range(3)] for i in range(3)],'decomposition':rec,'verification':ver})
                print('HIT',hits[-1],flush=True)
            stats['hits']+=len(decs)
        if (idx+1)%2000==0:
            print(f"robust scanned {idx+1}/{len(reps)}, hits={stats['hits']}, elapsed={time.time()-start:.1f}s",flush=True)
    summary={'prime':P,'scope':'complete SL3(F5)/right-diagonal quotient; robust exact block scan including rank-deficient qz/qw branches; finite-field/model-local only',
             'sl3_count':count_sl3,'representative_count':len(reps),'dictionary_sizes':{'qz':len(qzd),'qw':len(qwd),'max_qz_bucket':maxqz,'max_qw_bucket':maxqw,'length2_tail':len(len2),'two_fixed_tail':len(fixed2)},
             'stats':stats,'enum_seconds':enum_sec,'scan_seconds':time.time()-start,'total_seconds':time.time()-t0,'hits_saved':hits[:20]}
    out=OUT/'f5_sl3_modT_robust_rank10_scan.json'; out.write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'out':str(out),'stats':stats,'dicts':summary['dictionary_sizes'],'seconds':summary['total_seconds']},indent=2),flush=True)
if __name__=='__main__': main()
