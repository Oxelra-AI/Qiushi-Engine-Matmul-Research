#!/usr/bin/env python3
"""Positive control for analysis residual-space repair algebra.

Retain 22 columns of a verified rank-23 scheme, add one new slot with the
original deleted A-factor, and check that the residual-space intersection finds
the original B-direction and reconstructs a verified rank-23 decomposition after
linear C solve.
"""
from __future__ import annotations
import json, sys, time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
import residual_repair_geometry as rg  # type: ignore
from ab_residual_block_search import nonzero_tag_options_for_A, build_final_and_verify  # type: ignore
from linear_completion import parse_qmm_scheme_f2, verify_decomposition_f2  # type: ignore

OUT=Path('data/residual_repair/residual_positive_control.json')

def main():
    t0=time.time()
    A,B,C=parse_qmm_scheme_f2(Path('data/cn122_3x3_r23_repro/scheme.qmm'))
    D_cols=rg.D_columns_as_ints()
    records=[]
    ok_count=0
    for del_idx in range(23):
        retained=[(A[i],B[i],C[i]) for i in range(23) if i!=del_idx]
        retained_cols=[rg.vec_mask9_to_outer81(a,b) for a,b,_c in retained]
        tagged,E,rank_L,d=rg.build_quotient_basis(retained_cols,D_cols)
        opts=nonzero_tag_options_for_A(tagged,A[del_idx])
        orig_col=rg.vec_mask9_to_outer81(A[del_idx],B[del_idx])
        rem,orig_tag=rg.reduce_by_basis(tagged,orig_col)
        has_orig=(rem==0 and orig_tag in opts and opts[orig_tag]==B[del_idx])
        # Verify by appending original term as a new slot.
        seed_terms=retained+[(0,1,0)]  # dummy changed slot at index 22
        final_A=[a for a,_b,_c in seed_terms]
        final_A[22]=A[del_idx]
        vr=build_final_and_verify(seed_terms,[22],[A[del_idx]],[B[del_idx]])
        rec={'delete_index':del_idx,'rank_L':rank_L,'d':d,'option_count':len(opts),'orig_tag':int(orig_tag),'orig_rem_zero':rem==0,'has_original_B':has_orig,'verify_status':vr['status'],'brent_diff':vr.get('brent_diff')}
        if d==1 and has_orig and vr.get('brent_diff')==0:
            ok_count+=1
        records.append(rec)
    out={'schema':'s0908_residual_positive_control_v1','ok_count':ok_count,'total':23,'all_ok':ok_count==23,'records':records,'elapsed_sec':time.time()-t0}
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok' if out['all_ok'] else 'bad','out':str(OUT),'ok_count':ok_count,'total':23,'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))
    if not out['all_ok']:
        raise SystemExit(1)

if __name__=='__main__':
    main()
