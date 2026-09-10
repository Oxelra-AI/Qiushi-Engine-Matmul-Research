#!/usr/bin/env python3
"""analysis: explicit assignment certificate for the 12-point lift-bit cut.

For the minimized pivot-17 set A, enumerate all 2^12 lift-bit assignments.  For
each assignment, record one full-tensor Wang subspace (basis, L value, cap) whose
occupation is violated.  This turns the exact DFS UNSAT result into a small
replayable certificate independent of CP-SAT.
"""
from __future__ import annotations
import hashlib, json, sys, time
from collections import Counter
from pathlib import Path
ROOT=Path('research/research_record')
OUT=ROOT/'workspace/data/quotient_lift/lift_cut_assignment_certificate.json'
SCRIPT_DIR=ROOT/'workspace/scripts'
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
from lift_bit_feasibility_allrows import (  # type: ignore
    LUT_PATH, PIVOTS, build_constraints_all, load_lut, sha_file, section_lift
)
A=[9,33,99,160,184,189,192,209,215,224,249,254]
PIVOT=PIVOTS['rank2']

def sha_text_obj(obj)->str:
    return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def occupation_for_assignment(zmask:int,omask:int,assignment:int,n:int)->int:
    occ=0
    for i in range(n):
        b=(assignment>>i)&1
        if ((zmask>>i)&1) and b==0: occ+=1
        if ((omask>>i)&1) and b==1: occ+=1
    return occ

def main():
    t0=time.time(); print('Loading LUT...',flush=True); lut,meta=load_lut(LUT_PATH)
    print('Rebuilding canonical constraints for A...',flush=True)
    bundle=build_constraints_all(lut,PIVOT,A,max_dim=9,progress=0)
    constraints=bundle['constraints']; sources=bundle['source']; n=len(A)
    cert=[]; constraint_use=Counter(); cap_hist=Counter(); dim_hist=Counter(); active_hist=Counter(); max_excess=0
    for assn in range(1<<n):
        found=None
        for cid,(z,o,cap) in enumerate(constraints):
            occ=occupation_for_assignment(z,o,assn,n)
            if occ>cap:
                src=sources[(z,o)]
                found={
                    'assignment_int':assn,
                    'bits_in_A_order':[(assn>>i)&1 for i in range(n)],
                    'violating_constraint_id':cid,
                    'cap':int(cap),
                    'occ':int(occ),
                    'excess':int(occ-cap),
                    'active':int((z|o).bit_count()),
                    'eps0_points':[A[i] for i in range(n) if (z>>i)&1],
                    'eps1_points':[A[i] for i in range(n) if (o>>i)&1],
                    'source_basis9':[int(x) for x in src['basis']],
                    'source_dim':int(src['dim']),
                    'source_lb':int(src['lb']),
                    'source_cap20':int(src['cap20']),
                    'source_lut_index_in_iteration':int(src['idx']),
                }
                constraint_use[cid]+=1; cap_hist[cap]+=1; dim_hist[int(src['dim'])]+=1; active_hist[(z|o).bit_count()]+=1; max_excess=max(max_excess,occ-cap)
                break
        if found is None:
            raise AssertionError(f'assignment {assn} has no violation')
        cert.append(found)
    out={'schema':'s0908_lift_cut_assignment_certificate_v1','source_lut':str(LUT_PATH),'source_lut_sha256':sha_file(LUT_PATH),'lut_coverage_ok':meta.get('coverage_ok'),'pivot_name':'rank2','pivot':PIVOT,'cut_points':A,'cut_rhs':len(A)-1,'constraint_count':len(constraints),'builder_stats':bundle['stats'],'q_violations_head':bundle['q_violations'],'assignment_count':len(cert),'all_assignments_certified':len(cert)==(1<<n),'max_excess_in_chosen_violations':max_excess,'chosen_violation_cap_hist':{str(k):int(v) for k,v in sorted(cap_hist.items())},'chosen_violation_dim_hist':{str(k):int(v) for k,v in sorted(dim_hist.items())},'chosen_violation_active_hist':{str(k):int(v) for k,v in sorted(active_hist.items())},'distinct_constraints_used':len(constraint_use),'top_constraints_used':[{'constraint_id':int(k),'count':int(v)} for k,v in constraint_use.most_common(20)],'certificate':cert,'elapsed_sec':time.time()-t0}
    out['certificate_sha256']=sha_text_obj(cert)
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:out[k] for k in ['assignment_count','all_assignments_certified','constraint_count','distinct_constraints_used','chosen_violation_cap_hist','chosen_violation_dim_hist','certificate_sha256','elapsed_sec']},indent=2,sort_keys=True),flush=True)
    print('saved',OUT,flush=True)
if __name__=='__main__': main()
