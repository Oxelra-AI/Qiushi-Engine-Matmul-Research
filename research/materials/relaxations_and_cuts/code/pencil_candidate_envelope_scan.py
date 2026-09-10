#!/usr/bin/env python3
r"""analysis: scan candidate supports against the explicit pencil envelope.

For each stored distinct E11 support candidate, this script compares each dual
line's color budget with the explicit block-diagonal pencil envelope computed
from the 3x3 contraction blocks.  A line marked `outside_block_envelope` is not
an infeasibility result; it only means the simple block construction does not
supply a witness for that line/budget.  Such lines are candidates for exact
(non-block-diagonal) pencil analysis.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/pencil_repair"

SUPPORTS = {
    "54_base_9violation": [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219],
    "12violation_no36_with192": [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219],
    "far_L15_28viol": [2,3,16,20,24,28,31,65,72,96,97,108,114,130,146,159,162,216,252],
    "far_L14_44viol": [8,18,20,22,24,27,31,64,65,72,73,128,144,160,162,216,219,224,252],
}


def dot(a:int,b:int)->int: return (a&b).bit_count()&1

def enumerate_dual_lines(n:int=8)->List[Tuple[int,int,int]]:
    seen=set(); out=[]
    for q1 in range(1,1<<n):
        for q2 in range(q1+1,1<<n):
            line=tuple(sorted((q1,q2,q1^q2)))
            if line not in seen:
                seen.add(line); out.append(line)
    return out

def mat3_from_int(x:int)->np.ndarray:
    M=np.zeros((3,3),dtype=np.uint8)
    for i in range(9):
        if (x>>i)&1: M[i//3,i%3]=1
    return M

def int_from_mat3(M:np.ndarray)->int:
    x=0
    for i in range(3):
        for j in range(3):
            if int(M[i,j])&1: x|=1<<(3*i+j)
    return x

def row_masks(M:np.ndarray)->List[int]:
    rows=[]
    for i in range(M.shape[0]):
        x=0
        for j in range(M.shape[1]):
            if int(M[i,j]): x|=1<<j
        rows.append(x)
    return rows

def gf2mul(A:np.ndarray,B:np.ndarray)->np.ndarray:
    return ((A.astype(np.uint8)@B.astype(np.uint8))&1).astype(np.uint8)

def Pmat()->np.ndarray:
    P=np.zeros((9,9),dtype=np.uint8)
    for j in range(3):
        for k in range(3): P[3*k+j,3*j+k]=1
    return P

def grouped_H(M:np.ndarray,P:np.ndarray)->int:
    Mg=gf2mul(gf2mul(P,M),P.T)
    H=Mg[:3,:3].copy()
    return int_from_mat3(H)

def minimal(triples:Iterable[Tuple[int,int,int]])->List[Tuple[int,int,int]]:
    ts=sorted(set(triples)); out=[]
    for t in ts:
        if not any(all(u[i]<=t[i] for i in range(3)) and any(u[i]<t[i] for i in range(3)) for u in ts if u!=t): out.append(t)
    return out

def covers(b:Tuple[int,int,int], mins:Sequence[Tuple[int,int,int]])->bool:
    return any(t[0]<=b[0] and t[1]<=b[1] and t[2]<=b[2] for t in mins)

def colors(line:Tuple[int,int,int], support:Sequence[int])->Tuple[int,int,int,int]:
    q1,q2,_=line; c=[0,0,0,0]
    for p in support:
        c[dot(q1,p)*2 + dot(q2,p)] += 1  # index 0=00,1=01? fix below
    # convert internal index e1*2+e2 into c00,c10,c01,c11
    return (c[0],c[2],c[1],c[3])

def main()->None:
    t0=time.time(); OUTDIR.mkdir(parents=True,exist_ok=True)
    rank3=[0]*512
    for x in range(512): rank3[x]=int(mat_rank_f2(mat3_from_int(x)))
    T=build_matmul_tensor_f2()[1:,:,:].astype(np.uint8)%2
    P=Pmat(); qH={}; qrank={}
    for q in range(1,256):
        M=contraction_matrix(T,q); h=grouped_H(M,P); qH[q]=h; qrank[q]=3*rank3[h]
    env_cache={}
    def env(h1:int,h2:int)->List[Tuple[int,int,int]]:
        key=(h1,h2)
        if key in env_cache: return env_cache[key]
        single={(rank3[h1^z],rank3[h2^z],rank3[z]) for z in range(512)}
        sums={(0,0,0)}
        for _ in range(3):
            sums={(a[0]+b[0],a[1]+b[1],a[2]+b[2]) for a in sums for b in single}
        env_cache[key]=minimal(sums); return env_cache[key]
    lines=enumerate_dual_lines(8)
    results={}
    for name,supp in SUPPORTS.items():
        outside=[]; ib_fail=[]; all_lines_by_type=Counter(); outside_by_type=Counter(); outside_by_budget=Counter()
        for line in lines:
            q1,q2,q3=line; ranks=(qrank[q1],qrank[q2],qrank[q3])
            all_lines_by_type[ranks]+=1
            c00,c10,c01,c11=colors(line,supp); b=(c10,c01,c11)
            ib=(c10+c11>=ranks[0] and c01+c11>=ranks[1] and c10+c01>=ranks[2])
            if not ib:
                ib_fail.append({"line":list(line),"ranks":list(ranks),"colors":[c00,c10,c01,c11],"budget":list(b)})
                continue
            if not covers(b,env(qH[q1],qH[q2])):
                outside_by_type[ranks]+=1; outside_by_budget[b]+=1
                outside.append({"line":list(line),"ranks":list(ranks),"colors":[c00,c10,c01,c11],"budget":list(b),"env_minimal":[list(x) for x in env(qH[q1],qH[q2])]})
        results[name]={
            "support":supp,
            "individual_bound_fail_count":len(ib_fail),
            "outside_block_envelope_count":len(outside),
            "outside_block_envelope_by_rank_type":{str(k):v for k,v in sorted(outside_by_type.items())},
            "outside_block_envelope_by_budget_head":{str(k):v for k,v in outside_by_budget.most_common(30)},
            "outside_examples_head":outside[:50],
            "individual_bound_fail_examples_head":ib_fail[:20],
        }
    out={
        "schema":"pencil_candidate_envelope_scan_v1",
        "elapsed_sec":time.time()-t0,
        "dual_line_count":len(lines),
        "unique_ordered_H_pair_count":len(env_cache),
        "interpretation":"outside_block_envelope is not infeasible; it only marks line/budget pairs needing a stronger exact pencil witness or proof before any support cut is sound.",
        "results":results,
    }
    p=OUTDIR/'candidate_block_envelope_scan.json'
    p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({"out":str(p),"supports":list(results),"outside_counts":{k:v['outside_block_envelope_count'] for k,v in results.items()},"ib_fail_counts":{k:v['individual_bound_fail_count'] for k,v in results.items()},"elapsed_sec":time.time()-t0},indent=2,sort_keys=True))
if __name__=='__main__': main()
