#!/usr/bin/env python3
r"""analysis: constructive boundary for all-rank-9 E11 dual-line pencils.

For an all-rank-9 dual line, after normalizing M1 to I the pencil is

  rank(W) <= c11, rank(I+W) <= c10, rank(A+W) <= c01,

where A=M1^{-1}M2 and I+A are invertible.  The analysis block-diagonal envelope
already covers all individual-rank budgets except the three central minimal
triples (4,5,5), (5,4,5), (5,5,4) in rank order
(rank(I+W), rank(A+W), rank(W)).

This script gives a direct subspace construction of these central triples for
every all-rank-9 E11 line.  It searches for a 4D subspace K with K cap A K = 0.
Let E be a vector outside K + A K.  On the basis K, A K, E define W by

  W(k)=A k,  W(A k)=A k,

and put W(E)=E, A E, or 0.  Then respectively

  W(E)=E   -> ranks (4,5,5),
  W(E)=A E -> ranks (5,4,5),
  W(E)=0   -> ranks (5,5,4).

For k in K, (I+W)(Ak)=Ak+Ak=0 and (A+W)(k)=Ak+Ak=0, so AK is a kernel component for I+W and K is a kernel component for A+W.  This proves the central all-rank-9 budgets are feasible once K exists; the script finds and checks K for all 192 lines.
"""
from __future__ import annotations

import json
import random
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2, gf2_rank_rows
from wang_capacity_lazy import rref_basis
from dual_basis_instrument import gf2_mat_inv, gf2_mat_mul

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/pencil_repair"


def enumerate_dual_lines(n: int = 8) -> List[Tuple[int,int,int]]:
    seen=set(); out=[]
    for q1 in range(1,1<<n):
        for q2 in range(q1+1,1<<n):
            q3=q1^q2
            line=tuple(sorted((q1,q2,q3)))
            if line not in seen:
                seen.add(line); out.append(line)
    return out


def mat_vec(M: np.ndarray, v: int) -> int:
    out=0
    for i in range(M.shape[0]):
        s=0
        for j in range(M.shape[1]):
            if int(M[i,j]) & ((v>>j)&1):
                s ^= 1
        if s: out |= 1<<i
    return out


def int_cols_to_matrix(cols: Sequence[int], n: int=9) -> np.ndarray:
    M=np.zeros((n,len(cols)),dtype=np.uint8)
    for j,c in enumerate(cols):
        for i in range(n):
            M[i,j]=(c>>i)&1
    return M


def row_masks(M: np.ndarray) -> List[int]:
    rows=[]
    for i in range(M.shape[0]):
        x=0
        for j in range(M.shape[1]):
            if int(M[i,j])&1: x|=1<<j
        rows.append(x)
    return rows


def span_contains(v: int, basis: Sequence[int], n: int=9) -> bool:
    return gf2_rank_rows(list(basis) + [v], n) == gf2_rank_rows(basis, n)


def random_independent_basis(dim: int, n: int=9) -> List[int]:
    basis=[]
    while len(basis)<dim:
        v=random.randrange(1,1<<n)
        if gf2_rank_rows(basis+[v], n)>len(basis):
            basis.append(v)
    return list(rref_basis(basis,n=n))


def find_K(A: np.ndarray, max_trials: int=5000) -> Optional[Dict[str,object]]:
    for trial in range(max_trials):
        K=random_independent_basis(4,9)
        AK=[mat_vec(A,v) for v in K]
        if gf2_rank_rows(K+AK,9)!=8:
            continue
        basis8=list(rref_basis(K+AK,n=9))
        e=None
        for cand in range(1,1<<9):
            if not span_contains(cand,basis8,9):
                e=cand; break
        if e is None:
            continue
        return {"K":K,"AK":AK,"basis8":basis8,"e":e,"trial":trial}
    return None


def build_W_from_K(A: np.ndarray, Krec: Dict[str,object], extra_value: str) -> np.ndarray:
    K=list(Krec['K']); AK=list(Krec['AK']); e=int(Krec['e'])
    Dcols=K+AK+[e]
    Ycols=[]
    for ak in AK:       # W(k)=A k
        Ycols.append(ak)
    for ak in AK:       # W(Ak)=Ak
        Ycols.append(ak)
    if extra_value == 'I':
        Ycols.append(e)
    elif extra_value == 'A':
        Ycols.append(mat_vec(A,e))
    elif extra_value == '0':
        Ycols.append(0)
    else:
        raise ValueError(extra_value)
    D=int_cols_to_matrix(Dcols,9)
    Y=int_cols_to_matrix(Ycols,9)
    Dinv=gf2_mat_inv(D)
    if Dinv is None:
        raise RuntimeError('domain basis not invertible')
    return gf2_mat_mul(Y,Dinv)%2


def check_W(A: np.ndarray, W: np.ndarray) -> Dict[str,object]:
    I=np.eye(9,dtype=np.uint8)
    return {
        "rank_I_plus_W": int(mat_rank_f2((I+W)%2)),
        "rank_A_plus_W": int(mat_rank_f2((A+W)%2)),
        "rank_W": int(mat_rank_f2(W)),
        "W_row_masks": row_masks(W),
    }


def main() -> None:
    t0=time.time(); random.seed(5701)
    OUTDIR.mkdir(parents=True,exist_ok=True)
    T=build_matmul_tensor_f2()[1:,:,:].astype(np.uint8)%2
    cdata={}
    for q in range(1,256):
        M=contraction_matrix(T,q); cdata[q]={"M":M,"rank":int(mat_rank_f2(M))}
    lines=[ln for ln in enumerate_dual_lines(8) if all(cdata[q]['rank']==9 for q in ln)]
    records=[]; failures=[]; trial_hist=Counter()
    for line in lines:
        q1,q2,q3=line
        M1=cdata[q1]['M']; M2=cdata[q2]['M']
        M1inv=gf2_mat_inv(M1); assert M1inv is not None
        A=gf2_mat_mul(M1inv,M2)%2
        I=np.eye(9,dtype=np.uint8)
        if mat_rank_f2(A)!=9 or mat_rank_f2((A+I)%2)!=9:
            failures.append({"line":list(line),"reason":"A_or_A_plus_I_not_invertible"}); continue
        Krec=find_K(A)
        if Krec is None:
            failures.append({"line":list(line),"reason":"no_K_found"}); continue
        trial_hist[int(Krec['trial'])]+=1
        checks={}
        target_by_extra={"I":(4,5,5),"A":(5,4,5),"0":(5,5,4)}
        for extra,target in target_by_extra.items():
            W=build_W_from_K(A,Krec,extra)
            chk=check_W(A,W)
            got=(chk['rank_I_plus_W'],chk['rank_A_plus_W'],chk['rank_W'])
            chk['target']=list(target)
            chk['passes_target']=bool(all(got[i]<=target[i] for i in range(3)))
            checks[extra]=chk
            if not chk['passes_target']:
                failures.append({"line":list(line),"reason":"target_check_failed","extra":extra,"got":list(got),"target":list(target)})
        records.append({
            "line":list(line),
            "K_basis":list(Krec['K']),
            "AK_basis_images":list(Krec['AK']),
            "extra_vector_e":int(Krec['e']),
            "search_trial":int(Krec['trial']),
            "rank_K_plus_AK":int(gf2_rank_rows(list(Krec['K'])+list(Krec['AK']),9)),
            "witness_checks":checks,
        })
    out={
        "schema":"allrank9_subspace_boundary_v1",
        "elapsed_sec":time.time()-t0,
        "all_rank9_line_count":len(lines),
        "record_count":len(records),
        "failure_count":len(failures),
        "failures":failures[:20],
        "K_search_trial_histogram_head":dict(sorted(trial_hist.items())[:20]),
        "max_search_trial":max(trial_hist) if trial_hist else None,
        "records":records,
        "records_head":records[:10],
        "records_tail":records[-5:],
        "conclusion":{
            "central_minimal_budgets_constructed_for_all_rank9_lines": bool(len(failures)==0 and len(records)==len(lines)),
            "rank_order":"(rank(I+W), rank(A+W), rank(W)) = (c10,c01,c11)",
            "covered_central_triples":[[4,5,5],[5,4,5],[5,5,4]],
            "scientific_meaning":"Together with the exact block-diagonal envelope, this shows the all-rank-9 dual-line pencil color-budget condition has no support-level consequence beyond individual contraction rank inequalities for length-19 budgets. It does not address mixed/low-rank lines or full B/C completion."
        }
    }
    path=OUTDIR/'allrank9_subspace_boundary.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({"out":str(path),"lines":len(lines),"records":len(records),"failures":len(failures),"max_trial":out['max_search_trial'],"elapsed_sec":time.time()-t0},indent=2,sort_keys=True))

if __name__=='__main__': main()
