#!/usr/bin/env python3
r"""analysis: independent audit of repaired pencil artifacts."""
from __future__ import annotations

import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2, gf2_rank_rows
from dual_basis_instrument import gf2_mat_inv, gf2_mat_mul

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/pencil_repair"
ALLRANK9 = OUTDIR / "allrank9_subspace_boundary.json"
CONSTRUCTIVE = OUTDIR / "pencil_constructive_repair.json"
analysis = ROOT / "workspace/data/pencil_pilot/analytical_pencil_results.json"
NEAR_MISS = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]


def dot(a:int,b:int)->int: return (a&b).bit_count()&1

def mat_vec(M: np.ndarray, v: int) -> int:
    out=0
    for i in range(M.shape[0]):
        s=0
        for j in range(M.shape[1]):
            if int(M[i,j]) and ((v>>j)&1): s ^= 1
        if s: out |= 1<<i
    return out

def rows_to_mat(rows: Sequence[int], n: int=9) -> np.ndarray:
    M=np.zeros((len(rows),n),dtype=np.uint8)
    for i,r in enumerate(rows):
        for j in range(n): M[i,j]=(r>>j)&1
    return M

def square_from_row_masks(rows: Sequence[int]) -> np.ndarray:
    return rows_to_mat(rows,9)

def color_counts(line: Sequence[int], support: Sequence[int]) -> List[int]:
    q1,q2,_=line; c=[0,0,0,0]
    for p in support:
        e1,e2=dot(q1,p),dot(q2,p)
        if e1==0 and e2==0: c[0]+=1
        elif e1==1 and e2==0: c[1]+=1
        elif e1==0 and e2==1: c[2]+=1
        else: c[3]+=1
    return c

def span_contains(v:int,basis:Sequence[int],n:int=9)->bool:
    return gf2_rank_rows(list(basis)+[v],n)==gf2_rank_rows(basis,n)

def main()->None:
    t0=time.time(); failures=[]; warnings=[]
    T=build_matmul_tensor_f2()[1:,:,:].astype(np.uint8)%2
    cdata={}
    for q in range(1,256):
        M=contraction_matrix(T,q); cdata[q]={"M":M,"rank":int(mat_rank_f2(M))}

    # Audit all-rank-9 K and W witnesses.
    allr=json.loads(ALLRANK9.read_text())
    records=allr.get('records',[])
    for idx,rec in enumerate(records):
        line=rec['line']; q1,q2,q3=line
        if [cdata[q]['rank'] for q in line] != [9,9,9]:
            failures.append({"where":"allrank9","idx":idx,"line":line,"problem":"line not rank 9"}); continue
        M1,M2=cdata[q1]['M'],cdata[q2]['M']
        M1inv=gf2_mat_inv(M1)
        if M1inv is None:
            failures.append({"where":"allrank9","idx":idx,"line":line,"problem":"M1 not invertible"}); continue
        A=gf2_mat_mul(M1inv,M2)%2
        K=list(rec['K_basis']); AK_saved=list(rec['AK_basis_images']); e=int(rec['extra_vector_e'])
        AK=[mat_vec(A,k) for k in K]
        if AK != AK_saved:
            failures.append({"where":"allrank9","idx":idx,"line":line,"problem":"AK mismatch","AK":AK,"saved":AK_saved})
        if gf2_rank_rows(K,9)!=4:
            failures.append({"where":"allrank9","idx":idx,"line":line,"problem":"rank K != 4"})
        if gf2_rank_rows(K+AK,9)!=8:
            failures.append({"where":"allrank9","idx":idx,"line":line,"problem":"rank K+AK != 8"})
        if span_contains(e,K+AK,9):
            failures.append({"where":"allrank9","idx":idx,"line":line,"problem":"e in K+AK"})
        I=np.eye(9,dtype=np.uint8)
        for key,chk in rec['witness_checks'].items():
            W=square_from_row_masks(chk['W_row_masks'])
            got=[int(mat_rank_f2((I+W)%2)), int(mat_rank_f2((A+W)%2)), int(mat_rank_f2(W))]
            if got != chk['target']:
                failures.append({"where":"allrank9","idx":idx,"line":line,"witness":key,"problem":"rank target mismatch","got":got,"target":chk['target']})

    # Audit flagship Z witnesses from constructive repair.
    con=json.loads(CONSTRUCTIVE.read_text())
    for line_key,rec in con['detailed_line_analyses'].items():
        if line_key not in ['(42, 149, 191)','(55, 141, 186)']:
            continue
        line=rec['line']; q1,q2,_=line
        M1,M2=cdata[q1]['M'],cdata[q2]['M']
        chk=rec.get('simple_strategist_9x9_witness_check') or rec.get('explicit_9x9_witness_check')
        Z=square_from_row_masks(chk['Z_row_masks'])
        got=[int(mat_rank_f2((M1+Z)%2)), int(mat_rank_f2((M2+Z)%2)), int(mat_rank_f2(Z))]
        if got != chk['ranks_order_c10_c01_c11'] or not all(got[i] <= chk['budget_order_c10_c01_c11'][i] for i in range(3)):
            failures.append({"where":"flagship","line":line,"problem":"Z witness rank mismatch","got":got,"saved":chk})

    # Audit analysis stored colors against near-miss support.
    st56=json.loads(analysis.read_text())
    mismatch=[]
    method_counts=Counter()
    for rec in st56.get('tests',[]):
        method_counts[rec.get('pencil_detail',{}).get('method','unknown')]+=1
        cc=color_counts(rec['line'],NEAR_MISS)
        if cc != rec['colors']:
            mismatch.append({"line":rec['line'],"old_colors":rec['colors'],"recomputed":cc})
    if mismatch:
        warnings.append({"problem":"analysis colors mismatch recomputed near-miss support","count":len(mismatch),"head":mismatch[:10]})

    # Check reclassification counts align with old records, not total reported infeasible count.
    reclass=con['stored_test_reclassification']
    if len(reclass['records']) != len(st56.get('tests',[])):
        failures.append({"where":"reclass","problem":"record count mismatch","reclass":len(reclass['records']),"analysis":len(st56.get('tests',[]))})

    out={
        "schema":"pencil_repair_audit_v1",
        "elapsed_sec":time.time()-t0,
        "failure_count":len(failures),
        "failures":failures[:50],
        "warning_count":len(warnings),
        "warnings":warnings,
        "allrank9_records_checked":len(records),
        "flagship_Z_witnesses_checked":2,
        "test_records_checked":len(st56.get('tests',[])),
        "test_method_counts":dict(method_counts),
        "reported_total_pencil_infeasible":st56.get('pencil_infeasible'),
        "reclassification_counts_apply_only_to_stored_tests":reclass['counts'],
        "conclusion":"audit passed" if not failures else "audit found failures",
    }
    path=OUTDIR/'pencil_repair_audit.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({"out":str(path),"failures":len(failures),"warnings":len(warnings),"allrank9_records":len(records),"tests":len(st56.get('tests',[])),"elapsed_sec":time.time()-t0},indent=2,sort_keys=True))

if __name__=='__main__': main()
