#!/usr/bin/env python3
"""analysis: conciseness check for the corrected single-free-Z4 residual over F5.

For the complete SL3(F5)/right-diagonal quotient used in z4_f5_sl3_quotient_scan.py,
compute the rank of the first catalecticant (span of first partial derivatives) of
C_M.  Rank 9 means the cubic is concise in all 9 variables.  This tests the premise
used to dismiss one-size-4-orbit plus W* rank-10 patterns in the finite-field model.
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
QUADS=list(itertools.combinations_with_replacement(range(9),2)); QIDX={q:i for i,q in enumerate(QUADS)}

def derivative_matrix(C,p=P):
    M=np.zeros((9,len(QUADS)),dtype=object)
    for coeff,mono in zip(C,scan.MONOS):
        c=int(coeff)%p
        if c==0: continue
        counts=[0]*9
        for v in mono: counts[v]+=1
        for var in range(9):
            if counts[var]:
                rem=[]
                used=False
                for v in mono:
                    if v==var and not used:
                        used=True
                    else:
                        rem.append(v)
                q=tuple(rem)
                M[var,QIDX[q]]=(int(M[var,QIDX[q]])+counts[var]*c)%p
    return M

def main():
    t0=time.time(); ctx=scan.build_context(P)
    reps,count_sl3,enum_sec=qscan.enumerate_sl3_mod_T(P)
    rank_counts={}; examples={}
    start=time.time()
    for idx,M in enumerate(reps):
        Tcols=scan.matmul_mod(ctx['T0_y'],M,P)
        C=(ctx['target_y']-scan.free_contribution(Tcols,ctx['Ddiag'],P))%P
        rk=scan.rank_mod(derivative_matrix(C,P),P)
        rank_counts[rk]=rank_counts.get(rk,0)+1
        if rk not in examples:
            examples[rk]=[[int(M[i,j]) for j in range(3)] for i in range(3)]
        if (idx+1)%5000==0:
            print(f'checked {idx+1}/{len(reps)}, ranks={rank_counts}, elapsed={time.time()-start:.1f}s',flush=True)
    summary={'prime':P,'scope':'complete SL3(F5)/right-diagonal quotient; finite-field conciseness evidence only',
             'sl3_count':count_sl3,'representative_count':len(reps),'enum_seconds':enum_sec,'scan_seconds':time.time()-start,
             'catalecticant_rank_counts':{str(k):v for k,v in sorted(rank_counts.items())},'examples_by_rank':{str(k):v for k,v in examples.items()},
             'all_concise_rank9':rank_counts=={9:len(reps)}}
    out=OUT/'f5_sl3_modT_conciseness_scan.json'; out.write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'out':str(out),'rank_counts':summary['catalecticant_rank_counts'],'all_rank9':summary['all_concise_rank9'],'seconds':time.time()-t0},indent=2),flush=True)
if __name__=='__main__': main()
