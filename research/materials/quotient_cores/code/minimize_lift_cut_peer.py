#!/usr/bin/env python3
"""analysis: derive a small canonical lift-incompatible support cut.

Starting from the peer's rank-2 Wang-admissible quotient support, rebuild the
all-Wang-row lift-bit PB constraints in the corrected representation, then greedily
minimize the selected quotient points whose lift-bit system is still UNSAT.

If a subset A is lift-bit UNSAT, no full rank-20 A-support whose quotient support
contains A (with pivot 17) can satisfy Wang occupation, because adding more terms
only adds nonnegative occupation to every full row.  Thus sum_{p in A} x_p <=
|A|-1 is a valid A-side cut for the rank-2 pivot search.
"""
from __future__ import annotations
import json, sys, time
from collections import Counter
from pathlib import Path
ROOT=Path('research/research_record')
OUT=ROOT/'workspace/data/quotient_lift/minimized_lift_cut_peer.json'
SCRIPT_DIR=ROOT/'workspace/scripts'
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
from lift_bit_feasibility_allrows import (  # type: ignore
    LUT_PATH, PIVOTS, PEER_RANK2_SUPPORT, build_constraints_all, load_lut, sha_file
)

def restrict_constraints(constraints, keep_orig_indices):
    # keep_orig_indices are original support positions 0..18.  Return constraints
    # over compact positions 0..m-1, retaining only active>cap rows.
    pos={old:i for i,old in enumerate(keep_orig_indices)}
    out=[]; best={}
    for z,o,cap in constraints:
        zz=0; oo=0; active=0
        for old,new in pos.items():
            if (z>>old)&1:
                zz|=1<<new; active+=1
            elif (o>>old)&1:
                oo|=1<<new; active+=1
        if active>cap:
            key=(zz,oo)
            if key not in best or cap<best[key]: best[key]=cap
    out=[(z,o,c) for (z,o),c in best.items()]
    out.sort(key=lambda t:(t[2],(t[0]|t[1]).bit_count(),t[0],t[1]))
    return out

def feasible_dfs(constraints,m,find_all=False):
    # Choose order by incident count descending.
    inc_count=[]
    for v in range(m):
        c=sum(1 for z,o,cap in constraints if ((z|o)>>v)&1)
        inc_count.append((c,v))
    order=[v for c,v in sorted(inc_count,reverse=True)]
    inc=[ [[],[]] for _ in range(m) ]
    for ci,(z,o,cap) in enumerate(constraints):
        for v in range(m):
            if (z>>v)&1: inc[v][0].append(ci)
            if (o>>v)&1: inc[v][1].append(ci)
    occ=[0]*len(constraints); assign=[None]*m
    stats={'nodes':0,'leaves':0,'prunes':0,'solutions':0,'max_depth':0}; prune_depth=Counter(); first_solution=None; first_conflicts=[]
    t0=time.time()
    def rec(depth):
        nonlocal first_solution
        stats['nodes']+=1; stats['max_depth']=max(stats['max_depth'],depth)
        if depth==m:
            stats['leaves']+=1; stats['solutions']+=1
            if first_solution is None: first_solution=[int(x) for x in assign]
            return not find_all  # stop if just need feasibility
        v=order[depth]
        for val in (0,1):
            touched=[]; bad=None
            for ci in inc[v][val]:
                occ[ci]+=1; touched.append(ci)
                if occ[ci]>constraints[ci][2]: bad=ci; break
            stop=False
            if bad is None:
                assign[v]=val
                stop=rec(depth+1)
                assign[v]=None
            else:
                stats['prunes']+=1; prune_depth[depth+1]+=1
                if len(first_conflicts)<20:
                    z,o,cap=constraints[bad]
                    first_conflicts.append({'depth':depth+1,'var_compact':v,'value':val,'constraint_id':bad,'cap':cap,'active':(z|o).bit_count(),'eps0_compact':[i for i in range(m) if (z>>i)&1],'eps1_compact':[i for i in range(m) if (o>>i)&1]})
            for ci in reversed(touched): occ[ci]-=1
            if stop: return True
        return False
    rec(0)
    stats['elapsed_sec']=time.time()-t0
    return {'feasible':stats['solutions']>0,'stats':stats,'order':order,'first_solution':first_solution,'first_conflicts':first_conflicts,'prune_depth':{str(k):int(v) for k,v in sorted(prune_depth.items())}}

def main():
    t0=time.time(); print('Loading LUT...',flush=True); lut,meta=load_lut(LUT_PATH)
    print('Building corrected all-row constraints for peer support...',flush=True)
    bundle=build_constraints_all(lut,PIVOTS['rank2'],PEER_RANK2_SUPPORT,max_dim=9,progress=0)
    full_constraints=bundle['constraints']
    current=list(range(len(PEER_RANK2_SUPPORT)))
    history=[]
    print(f'Initial constraints {len(full_constraints)} on {len(current)} points',flush=True)
    base=feasible_dfs(restrict_constraints(full_constraints,current),len(current),find_all=False)
    print('Initial feasible?',base['feasible'],base['stats'],flush=True)
    changed=True
    while changed:
        changed=False
        for old in list(current):
            trial=[x for x in current if x!=old]
            rc=restrict_constraints(full_constraints,trial)
            res=feasible_dfs(rc,len(trial),find_all=False)
            history.append({'try_remove_index':old,'try_remove_point':PEER_RANK2_SUPPORT[old],'remaining_points':[PEER_RANK2_SUPPORT[i] for i in trial],'constraint_count':len(rc),'feasible_after_removal':res['feasible'],'stats':res['stats']})
            print(f"try remove {PEER_RANK2_SUPPORT[old]} -> feasible={res['feasible']} constraints={len(rc)} nodes={res['stats']['nodes']}",flush=True)
            if not res['feasible']:
                current=trial; changed=True
                print('  removed; current', [PEER_RANK2_SUPPORT[i] for i in current], flush=True)
                break
    final_constraints=restrict_constraints(full_constraints,current)
    final=feasible_dfs(final_constraints,len(current),find_all=True)
    # Verify every one-point deletion is feasible.
    deletion_checks=[]
    for old in current:
        trial=[x for x in current if x!=old]
        rc=restrict_constraints(full_constraints,trial)
        res=feasible_dfs(rc,len(trial),find_all=False)
        deletion_checks.append({'remove_point':PEER_RANK2_SUPPORT[old],'feasible':res['feasible'],'constraint_count':len(rc),'stats':res['stats'],'first_solution_bits_compact':res['first_solution']})
    # Decode final conflicts into point labels.
    final_conflicts=[]
    for c in final['first_conflicts']:
        final_conflicts.append({**c,'eps0_points':[PEER_RANK2_SUPPORT[current[i]] for i in c['eps0_compact']],'eps1_points':[PEER_RANK2_SUPPORT[current[i]] for i in c['eps1_compact']]})
    out={'schema':'s0908_minimized_lift_cut_peer_v1','source_lut':str(LUT_PATH),'source_lut_sha256':sha_file(LUT_PATH),'lut_coverage_ok':meta.get('coverage_ok'),'pivot_name':'rank2','pivot':PIVOTS['rank2'],'original_support':PEER_RANK2_SUPPORT,'builder_stats':bundle['stats'],'q_violations_head':bundle['q_violations'],'full_constraint_count':len(full_constraints),'initial_check':base,'greedy_history':history,'minimized_indices':current,'minimized_points':[PEER_RANK2_SUPPORT[i] for i in current],'cut':{'points':[PEER_RANK2_SUPPORT[i] for i in current],'rhs':len(current)-1,'meaning':'sum_{p in points} x_p <= rhs for rank2 pivot 17, because these points have no full-Wang-compatible lift-bit assignment'},'final_constraint_count':len(final_constraints),'final_exact_check':{**final,'first_conflicts':final_conflicts},'one_point_deletion_checks':deletion_checks,'total_elapsed_sec':time.time()-t0}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'minimized_points':out['minimized_points'],'rhs':out['cut']['rhs'],'final_feasible':final['feasible'],'final_stats':final['stats'],'all_deletions_feasible':all(d['feasible'] for d in deletion_checks)},indent=2,sort_keys=True),flush=True)
    print('saved',OUT,flush=True)
if __name__=='__main__': main()
