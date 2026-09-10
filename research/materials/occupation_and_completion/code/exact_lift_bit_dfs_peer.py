#!/usr/bin/env python3
"""Exact backtracking verifier for the analysis canonical lift-bit PB system.

This is an independent check of CP-SAT for the peer rank-2 Wang-admissible
support.  It imports the canonical all-row constraint builder, then performs an
exact DFS over the 19 lift bits.  A branch is pruned only when a Wang upper-bound
row already has too many agreeing selected lifts; future bits cannot repair this.
"""
from __future__ import annotations
import json, sys, time, hashlib
from collections import Counter
from pathlib import Path
ROOT=Path('research/research_record')
OUT=ROOT/'workspace/data/quotient_lift/exact_lift_bit_dfs_peer.json'
SCRIPT_DIR=ROOT/'workspace/scripts'
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
from lift_bit_feasibility_allrows import (  # type: ignore
    LUT_PATH, PEER_RANK2_SUPPORT, PIVOTS, build_constraints_all, load_lut, sha_file
)

def exact_dfs(constraints, nvars:int, order:list[int]):
    # constraints: list[(zmask,omask,cap)] over original variable indices.
    inc=[ [[],[]] for _ in range(nvars) ]  # inc[var][value] -> constraint ids incremented by setting var=value
    active_hist=Counter(); cap_hist=Counter()
    for ci,(z,o,cap) in enumerate(constraints):
        active=(z|o).bit_count(); active_hist[active]+=1; cap_hist[cap]+=1
        for v in range(nvars):
            if (z>>v)&1: inc[v][0].append(ci)
            if (o>>v)&1: inc[v][1].append(ci)
    occ=[0]*len(constraints)
    assigned=[None]*nvars
    stats={'nodes':0,'leaves':0,'prunes':0,'solutions':0,'max_depth':0}
    prune_depth=Counter(); branch_depth=Counter(); first_solution=None; first_conflicts=[]
    t0=time.time()
    def rec(depth:int):
        nonlocal first_solution
        stats['nodes']+=1; branch_depth[depth]+=1; stats['max_depth']=max(stats['max_depth'],depth)
        if depth==nvars:
            stats['leaves']+=1; stats['solutions']+=1
            if first_solution is None: first_solution=[int(x) for x in assigned]
            return
        v=order[depth]
        for val in (0,1):
            touched=[]; bad=None
            for ci in inc[v][val]:
                occ[ci]+=1; touched.append(ci)
                if occ[ci] > constraints[ci][2]:
                    bad=ci; break
            if bad is None:
                assigned[v]=val
                rec(depth+1)
                assigned[v]=None
            else:
                stats['prunes']+=1; prune_depth[depth+1]+=1
                if len(first_conflicts)<30:
                    z,o,cap=constraints[bad]
                    first_conflicts.append({'depth':depth+1,'var':v,'value':val,'constraint_id':bad,'cap':cap,'active':(z|o).bit_count(),'zmask':z,'omask':o,'current_occ':occ[bad]})
            for ci in reversed(touched):
                occ[ci]-=1
    rec(0)
    stats['elapsed_sec']=time.time()-t0
    return {
        'stats':stats,
        'first_solution':first_solution,
        'active_hist':{str(k):int(v) for k,v in sorted(active_hist.items())},
        'cap_hist':{str(k):int(v) for k,v in sorted(cap_hist.items())},
        'branch_depth':{str(k):int(v) for k,v in sorted(branch_depth.items())},
        'prune_depth':{str(k):int(v) for k,v in sorted(prune_depth.items())},
        'first_conflicts':first_conflicts,
        'order':order,
        'incident_lengths':[{ 'var':i, 'point':PEER_RANK2_SUPPORT[i], 'inc0':len(inc[i][0]), 'inc1':len(inc[i][1])} for i in range(nvars)],
    }

def main():
    t0=time.time(); print('Loading LUT...',flush=True); lut,meta=load_lut(LUT_PATH)
    print('Building all-row canonical constraints...',flush=True)
    bundle=build_constraints_all(lut,PIVOTS['rank2'],PEER_RANK2_SUPPORT,max_dim=9,progress=0)
    constraints=bundle['constraints']
    # Use support order sorted by total incident constraints descending for stronger early pruning.
    n=len(PEER_RANK2_SUPPORT)
    inc_count=[]
    for i in range(n):
        c=0
        for z,o,cap in constraints:
            if ((z|o)>>i)&1: c+=1
        inc_count.append((c,i))
    order=[i for c,i in sorted(inc_count,reverse=True)]
    print(f"constraints={len(constraints)}, order={order}",flush=True)
    result=exact_dfs(constraints,n,order)
    out={'schema':'s0908_exact_lift_bit_dfs_peer_v1','source_lut':str(LUT_PATH),'source_lut_sha256':sha_file(LUT_PATH),'lut_coverage_ok':meta.get('coverage_ok'),'pivot_name':'rank2','pivot':PIVOTS['rank2'],'support':PEER_RANK2_SUPPORT,'constraint_count':len(constraints),'q_violations_head':bundle['q_violations'],'builder_stats':bundle['stats'],'dfs':result,'total_elapsed_sec':time.time()-t0}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'constraint_count':len(constraints),'q_violations':len(bundle['q_violations']),'dfs_stats':result['stats'],'order_points':[PEER_RANK2_SUPPORT[i] for i in order]},indent=2,sort_keys=True),flush=True)
    print('saved',OUT,flush=True)
if __name__=='__main__': main()
