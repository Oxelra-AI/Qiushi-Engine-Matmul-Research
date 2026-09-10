#!/usr/bin/env python3
"""analysis: add full E11-stabilizer orbits of near-miss dual violations to L>=14 hybrid model."""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter, deque
from pathlib import Path
from typing import Sequence

import numpy as np

SCRIPTS=Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient  # noqa:E402
from complete_core_and_transversal import ROOT, build_core_constraints, complete_core_wang_scan, saturation_domains, transversal_failures  # noqa:E402
from quotient_rank_cuts import build_contractions, point_mask_for_q  # noqa:E402
from candidate_source_qcut_scan import eval_candidate_sources  # noqa:E402
from core_repeat_symmetry_and_cnf import build_action_images_with_flag, induced_core_permutation  # noqa:E402
from dual_violation_orbits import primal_perm_to_dual_perm, transform_D_key  # noqa:E402
from wang_capacity_lazy import pack_basis, rref_basis, subspace_points_from_basis, unpack_basis  # noqa:E402

S=19; POINTS=list(range(1,256)); OUTDIR=ROOT/'workspace/data/hybrid_orbit_augmented'


def load_lut(path:Path):
    with path.open('rb') as f: payload=pickle.load(f)
    return {int(k):int(v) for k,v in payload['lut'].items()}, payload.get('meta',{})

def dot(q:int,p:int)->int: return (int(q)&int(p)).bit_count()&1

def annihilator_points(basis:Sequence[int], n:int=8):
    return [q for q in range(1,1<<n) if all(dot(q,b)==0 for b in basis)]

def D_key(D:Sequence[int])->int: return pack_basis(rref_basis(D,n=8))

def U_key_from_D_key(dkey:int)->int:
    D=subspace_points_from_basis(unpack_basis(dkey))
    U=[p for p in range(1,256) if all(dot(q,p)==0 for q in D)]
    return pack_basis(rref_basis(U,n=8))

def orbit(seed:int, perms:Sequence[Sequence[int]]):
    seen={int(seed)}; dq=deque([int(seed)])
    while dq:
        k=dq.popleft()
        for dp in perms:
            im=transform_D_key(k,dp)
            if im not in seen:
                seen.add(im); dq.append(im)
    return sorted(seen)

def bitset_points(bs:int): return [i+1 for i in range(255) if (int(bs)>>i)&1]

def load_best_hint(records):
    p=ROOT/'workspace/data/distinct_line_cover/threshold_L15_300s.json'
    if p.exists():
        d=json.loads(p.read_text())
        if d.get('solutions'): return [int(x) for x in d['solutions'][0]['A_cols']]
    return None

def main():
    from ortools.sat.python import cp_model
    ap=argparse.ArgumentParser()
    ap.add_argument('--seeds', type=str, default='75122,8429827,37896739', help='comma-separated representative D_keys')
    ap.add_argument('--initial-threshold-L', type=int, default=14)
    ap.add_argument('--solver-time', type=float, default=300.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--seed', type=int, default=4960)
    ap.add_argument('--out', type=Path, default=OUTDIR/'orbit_augmented_L14.json')
    args=ap.parse_args(); args.out.parent.mkdir(parents=True,exist_ok=True)
    t0=time.time()
    lut,_=load_lut(ROOT/'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records,meta=build_core_constraints(CoreQuotient(1),lut)
    key_to_index={int(r['key8']):i for i,r in enumerate(records)}
    core=CoreQuotient(1)
    actions=build_action_images_with_flag()
    import wang_capacity_lazy as wcl
    primal=[]; seen=set()
    for img,tr in actions:
        if wcl.transform_mask(core.pivot,img)!=core.pivot: continue
        g=induced_core_permutation(core,img)
        if g not in seen: seen.add(g); primal.append(g)
    dual=[primal_perm_to_dual_perm(g) for g in primal]
    dual=list(dict.fromkeys(dual))
    seed_keys=[int(x) for x in args.seeds.replace(',', ' ').split()]
    orbit_info=[]; orbit_indices=[]
    for sk in seed_keys:
        orb=orbit(sk, dual)
        idxs=[]; Lhist=Counter(); dimhist=Counter()
        for dk in orb:
            uk=U_key_from_D_key(dk)
            idx=key_to_index[uk]
            idxs.append(idx); Lhist[int(records[idx]['L'])]+=1; dimhist[int(records[idx]['dim8'])]+=1
        orbit_info.append({'seed_D_key':sk,'orbit_size':len(orb),'row_indices':idxs,'L_hist':{str(k):int(v) for k,v in sorted(Lhist.items())},'dim8_hist':{str(k):int(v) for k,v in sorted(dimhist.items())}})
        orbit_indices.extend(idxs)
    orbit_indices=sorted(set(orbit_indices))

    T=np.load(ROOT/'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8)%2
    contractions=build_contractions(T); masks={q:point_mask_for_q(q) for q in contractions}
    model=cp_model.CpModel(); x={p:model.NewBoolVar(f'x_{p}') for p in POINTS}; model.Add(sum(x[p] for p in POINTS)==S)
    w={q:model.NewIntVar(0,S,f'w_{q}') for q in POINTS}
    for q in POINTS: model.Add(w[q]==sum(x[p] for p in POINTS if dot(q,p)))
    added=set(); repr_count=Counter(); by_L=Counter(); by_dim=Counter(); direct_terms=0; ann_terms=0
    def add_idx(idx:int, reason:str):
        nonlocal direct_terms, ann_terms
        if idx in added: return False
        rec=records[idx]; L=int(rec['L']); cap=S-L; d=int(rec['dim8'])
        if cap>=S: return False
        pts=bitset_points(int(rec['point_bitset']))
        if not pts and cap>=0: return False
        direct_n=len(pts); ann_n=(1 << (8-d))-1 if d<8 else 10**9
        if d>=5 and ann_n<direct_n:
            D=annihilator_points(unpack_basis(int(rec['key8'])),8); k=8-d
            model.Add(sum(w[q] for q in D) >= (1 << (k-1))*L)
            repr_count['annihilator']+=1; ann_terms+=len(D)
        else:
            model.Add(sum(x[p] for p in pts)<=cap)
            repr_count['direct']+=1; direct_terms+=len(pts)
        added.add(idx); by_L[L]+=1; by_dim[d]+=1
        return True
    for idx,rec in enumerate(records):
        if int(rec['L']) >= args.initial_threshold_L: add_idx(idx,'initial')
    new_orbit=0
    for idx in orbit_indices:
        if add_idx(idx,'orbit'): new_orbit+=1
    for q,c in contractions.items():
        rk=int(c['rank'])
        if rk>0: model.Add(w[q]>=rk)
    hint=load_best_hint(records)
    if hint:
        hs=set(hint)
        for p in POINTS: model.AddHint(x[p],1 if p in hs else 0)
    build_sec=time.time()-t0
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(args.solver_time); solver.parameters.num_search_workers=int(args.workers); solver.parameters.random_seed=int(args.seed)
    ts=time.time(); st=solver.Solve(model); solve_sec=time.time()-ts; status=solver.StatusName(st)
    result={'schema':'hybrid_orbit_augmented_v1','field':'F2','core':'E11','rank_s':S,'initial_threshold_L':args.initial_threshold_L,'seed_D_keys':seed_keys,'dual_permutations':len(dual),'orbit_info':orbit_info,'orbit_rows_total_unique':len(orbit_indices),'orbit_rows_new_beyond_threshold':new_orbit,'constraint_summary':{'active_wang_rows':len(added),'repr_count':{str(k):int(v) for k,v in sorted(repr_count.items())},'rows_by_L':{str(k):int(v) for k,v in sorted(by_L.items())},'rows_by_dim8':{str(k):int(v) for k,v in sorted(by_dim.items())},'direct_point_terms_total':direct_terms,'annihilator_weight_terms_total':ann_terms,'weight_variables':255,'weight_equalities':255,'contraction_lower_bounds':255},'complete_core_table_meta':meta,'model_stats':model.ModelStats(),'hint_added':bool(hint),'build_sec':round(build_sec,3),'solver_time_limit':args.solver_time,'status':status,'solve_sec':round(solve_sec,3),'response_stats':solver.ResponseStats(),'interpretation':'Adds the full E11-stabilizer dual orbits of the L15-support missing L=12 annihilator rows to the L>=14 hybrid model. FEASIBLE is only an A-support candidate; UNKNOWN is not a proof.'}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A=[p for p in POINTS if solver.Value(x[p])]
        scan=complete_core_wang_scan('orbit_augmented_solution',A,S,records,max_head=40)
        sat=saturation_domains(T,A); trans=transversal_failures(sat['sat_records'],sat['B_domains'],sat['C_domains'],9,9,max_report=10); qscan=eval_candidate_sources('orbit_augmented_solution',A,contractions,masks,max_source_size=2,max_store=20)
        result['solution']={'A_cols':A,'complete_wang_violations':scan['complete_violation_count'],'max_excess':scan['max_excess'],'violations_by_dim8':scan['violations_by_dim8'],'violations_by_L':scan['violations_by_full_lut_L'],'violations_head':scan['violations_head'],'zero_domain_terms':len(sat['summary']['zero_domain_terms']),'linear_pass':sat['summary']['linear_membership']['necessary_linear_test_passed'],'affine_dim':sat['summary']['linear_membership']['affine_solution_dimension_if_consistent'],'transversal_failures':trans['failure_count_reported'],'quotient_rank_violations_size2':qscan['violated_guarded_instances']}
        print('A',A,'viol',result['solution']['complete_wang_violations'],result['solution']['violations_by_L'])
    result['elapsed_sec']=round(time.time()-t0,3)
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(args.out),'status':status,'orbit_new':new_orbit,'active_rows':len(added),'elapsed_sec':result['elapsed_sec']},sort_keys=True))

if __name__=='__main__': main()
