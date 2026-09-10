#!/usr/bin/env python3
"""Validate mathematical prerequisites for analysis conditional re-pivot cuts.

Checks two finite statements directly:
1. The A-slot map used in conditional normalizers extends to an exact
   automorphism of tau(A,B,C)=tr(A B C^T), with B,C slot maps exhibited.
2. For every rank-2 direction a and every b not in <a>, the plane <a,b>
   has full-Wang cap20 <= 2. Thus if a is selected in a length-20 support
   satisfying Wang occupation, the two nonzero directions in each quotient
   fiber relative to a cannot both be selected.
Also records dim-1 cap20 values for duplicate-direction semantics.
"""
from __future__ import annotations
import json, pickle, sys, time, hashlib
from collections import Counter
from pathlib import Path
ROOT=Path('research/research_record')
S04=Path('scripts')
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import rref_basis, pack_basis, unpack_basis  # type: ignore
SCRIPTS=ROOT/'workspace/scripts'
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))
import conditional_repivot_cuts as gen  # type: ignore

LUT=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
COND=ROOT/'workspace/data/quotient_lift/conditional_cuts/conditional_rank2_cut_masks_from_two_orbits.json'
OUT=ROOT/'workspace/data/quotient_lift/conditional_cuts/conditional_prereq_validation.json'


def sha(path:Path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()


def load_lut():
    with LUT.open('rb') as f: payload=pickle.load(f)
    return payload['lut'], payload.get('meta',{})


def mat_inv_from_mask(mask:int):
    return gen.gf2_inv(gen.bits_to_mat(mask))


def mat_identity(): return [[1 if i==j else 0 for j in range(3)] for i in range(3)]


def slot_action_A(P,QinvT,a:int):
    return gen.full_action(P,QinvT,a)


def slot_action_B(Q,B:int):
    # R=I in derivation: B -> Q^T B
    return gen.mat_to_bits(gen.matmul(gen.transpose(Q), gen.bits_to_mat(B)))


def slot_action_C(Pinv,C:int):
    # R=I in derivation: C -> P^{-1} C
    return gen.mat_to_bits(gen.matmul(Pinv, gen.bits_to_mat(C)))


def tau(a:int,b:int,c:int)->int:
    A=gen.bits_to_mat(a); B=gen.bits_to_mat(b); C=gen.bits_to_mat(c)
    s=0
    for i in range(3):
        for j in range(3):
            if not A[i][j]: continue
            for k in range(3):
                s ^= (A[i][j] & B[j][k] & C[i][k])
    return s & 1


def validate_automorphisms():
    data=json.loads(COND.read_text())
    normals={}
    for r in data['conditional_cuts']:
        a=int(r['pivot_a']); n=r['normalizer']; normals[a]=(int(n['Pmask']),int(n['Qmask']),int(n['QinvTmask']))
    errors=[]; checked=0
    basis=[1<<i for i in range(9)]
    for a,(Pmask,Qmask,QinvTmask) in sorted(normals.items()):
        P=gen.bits_to_mat(Pmask); Q=gen.bits_to_mat(Qmask); QinvT=gen.bits_to_mat(QinvTmask); Pinv=gen.gf2_inv(P)
        if slot_action_A(P,QinvT,a)!=17:
            errors.append({'pivot_a':a,'error':'A_normalization'}); continue
        for A in basis:
            Ap=slot_action_A(P,QinvT,A)
            for B in basis:
                Bp=slot_action_B(Q,B)
                for C in basis:
                    Cp=slot_action_C(Pinv,C)
                    if tau(Ap,Bp,Cp)!=tau(A,B,C):
                        errors.append({'pivot_a':a,'error':'tau_mismatch','A':A,'B':B,'C':C,'Ap':Ap,'Bp':Bp,'Cp':Cp,'Pmask':Pmask,'Qmask':Qmask,'QinvTmask':QinvTmask})
                        break
                if errors and errors[-1].get('pivot_a')==a and errors[-1].get('error')=='tau_mismatch': break
            if errors and errors[-1].get('pivot_a')==a and errors[-1].get('error')=='tau_mismatch': break
        checked+=1
    return {'normalizer_count':len(normals),'automorphism_checks':checked,'error_count':len(errors),'errors':errors[:20]}


def validate_plane_caps(lut):
    rank_hist=Counter(gen.rank_of_mask(a) for a in range(1,512))
    dim1=Counter(); dim1_bad=[]
    for a in range(1,512):
        key=pack_basis(rref_basis([a],n=9)); lb=int(lut[key]); cap=20-lb; dim1[cap]+=1
        if cap>1 and len(dim1_bad)<20: dim1_bad.append({'a':a,'rank':gen.rank_of_mask(a),'lb':lb,'cap20':cap})
    rank2=[a for a in range(1,512) if gen.rank_of_mask(a)==2]
    cap_hist=Counter(); lb_hist=Counter(); bad=[]; checked=0; unique_planes={}
    for a in rank2:
        for b in range(1,512):
            if b==a: continue
            # b is in <a> iff b==a over F2; zero omitted already.
            key=pack_basis(rref_basis([a,b],n=9))
            if (key,a) in unique_planes: continue
            lb=int(lut[key]); cap=20-lb; cap_hist[cap]+=1; lb_hist[lb]+=1; checked+=1
            if cap>2 and len(bad)<50:
                bad.append({'a':a,'b':b,'basis':list(unpack_basis(key)),'lb':lb,'cap20':cap})
    # unique planes containing some rank2 direction (ignoring a) for context.
    plane_keys=set()
    for a in rank2:
        for b in range(1,512):
            if b==a: continue
            plane_keys.add(pack_basis(rref_basis([a,b],n=9)))
    unique_cap=Counter(); unique_bad=[]
    for key in plane_keys:
        lb=int(lut[key]); cap=20-lb; unique_cap[cap]+=1
        if cap>2 and len(unique_bad)<50: unique_bad.append({'basis':list(unpack_basis(key)),'lb':lb,'cap20':cap})
    return {'rank_hist_nonzero_matrices':dict(sorted(rank_hist.items())),'dim1_cap20_hist':dict(sorted(dim1.items())),'dim1_cap_gt1_examples':dim1_bad,'rank2_direction_count':len(rank2),'rank2_ordered_plane_checks':checked,'rank2_ordered_plane_cap20_hist':dict(sorted(cap_hist.items())),'rank2_ordered_plane_lb_hist':dict(sorted(lb_hist.items())),'rank2_plane_cap_gt2_examples':bad,'rank2_unique_plane_count':len(plane_keys),'rank2_unique_plane_cap20_hist':dict(sorted(unique_cap.items())),'rank2_unique_plane_cap_gt2_examples':unique_bad}


def main():
    t0=time.time(); lut,meta=load_lut()
    aut=validate_automorphisms(); planes=validate_plane_caps(lut)
    out={'schema':'s0908_conditional_prereq_validation_v1','source_lut':str(LUT),'source_lut_sha256':sha(LUT),'lut_coverage_ok':meta.get('coverage_ok'),'conditional_file':str(COND),'conditional_file_sha256':sha(COND),'automorphism_validation':aut,'plane_cap_validation':planes,'elapsed_sec':time.time()-t0}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
