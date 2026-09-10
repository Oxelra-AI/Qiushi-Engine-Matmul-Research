#!/usr/bin/env python3
"""Prefix/orbit CP-SAT brancher for T-level Wang occupation supports.

This is a support-feasibility instrument for the remaining fixed-E11 rank-20
branch.  It generalizes the analysis second-orbit split: after fixing a base
prefix (for example 1,2 or 1,16), compute the pointwise stabilizer inside the
A-side GL(3,2)xGL(3,2)⋊C2 action, split remaining candidate points of chosen
matrix ranks into orbits, and optionally fix one branch representative while
omitting earlier candidate orbits.

The model can include:
  * all Wang LUT rows of selected dimensions, normally 1,2,3;
  * all high-dimensional rows containing a specified `through` prefix, normally
    the fixed rank-1 pair such as 1,2 or 1,16;
  * all compressed rank-1-projection inequalities (sound for mixed supports);
  * optional seed rows from previous complete-LUT scans.

SAT supports must still be checked against the full LUT.  INFEASIBLE is useful
branch evidence but requires a proof-producing CNF/DRAT replay if used as a
mathematical proof component.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence, Set

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_capacity_profile import load_or_build as load_or_build_rank1_projection  # noqa: E402
from wang_capacity_lazy import (  # noqa: E402
    in_rowspace,
    make_actions,
    matrix_rank_of_mask,
    transform_mask,
    unpack_basis,
    subspace_points_from_basis,
)
from wang_capacity_cnf_e11_fixed import E11, collect_violation_keys, parse_dims, stab_e11_orbits  # noqa: E402


def parse_ints(spec: str) -> List[int]:
    return [int(x) for x in spec.replace(';', ',').split(',') if x.strip()]


def parse_ranks(spec: str) -> Set[int]:
    return {int(x) for x in spec.replace(';', ',').split(',') if x.strip()}


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def parent_exclusions_for_second(second_rep: int | None) -> Set[int]:
    if second_rep is None or second_rep == E11:
        return set()
    excluded: Set[int] = set()
    found = False
    for orb in stab_e11_orbits():
        if orb['rep'] == second_rep:
            found = True
            break
        excluded.update(int(p) for p in orb['members'])
    if not found:
        raise ValueError(f'{second_rep} is not a Stab(E11) second-orbit representative')
    excluded.discard(E11)
    excluded.discard(second_rep)
    return excluded


def stabilizer_of_prefix(prefix: Sequence[int]):
    actions = make_actions()
    pref = list(prefix)
    return [img for img in actions if all(transform_mask(p, img) == p for p in pref)]


def candidate_orbits(prefix: Sequence[int], parent_excluded: Set[int], candidate_ranks: Set[int]):
    stab = stabilizer_of_prefix(prefix)
    fixed = set(prefix)
    unseen = {p for p in range(1,512) if p not in fixed and p not in parent_excluded and matrix_rank_of_mask(p) in candidate_ranks}
    orbits=[]
    while unseen:
        rep=min(unseen)
        members={transform_mask(rep,img) for img in stab}
        members={p for p in members if p in unseen}
        ranks=Counter(matrix_rank_of_mask(p) for p in members)
        orbits.append({'rep':rep,'size':len(members),'rank_hist':dict(sorted(ranks.items())),'members':sorted(members)})
        unseen-=members
    orbits.sort(key=lambda o:o['rep'])
    return stab, orbits


def branch_universe(base_fixed: Sequence[int], third_rep: int | None, parent_second_rep: int | None,
                    candidate_ranks: Set[int], exclude_candidate_before: bool):
    parent_excl = parent_exclusions_for_second(parent_second_rep)
    stab, orbits = candidate_orbits(base_fixed, parent_excl, candidate_ranks)
    fixed = list(base_fixed)
    if third_rep is not None and third_rep not in fixed:
        fixed.append(third_rep)
    excluded=set(parent_excl)
    third_orbit=None
    if third_rep is not None and exclude_candidate_before:
        found=False
        for i,orb in enumerate(orbits):
            if third_rep in orb['members']:
                found=True
                third_orbit={'orbit_index':i,'rep':orb['rep'],'size':orb['size'],'rank_hist':orb['rank_hist'],'fixed_is_rep':third_rep==orb['rep']}
                break
            excluded.update(int(p) for p in orb['members'])
        if not found:
            raise ValueError(f'third_rep {third_rep} is not in remaining candidate-rank orbits for prefix {base_fixed}')
    elif third_rep is not None:
        for i,orb in enumerate(orbits):
            if third_rep in orb['members']:
                third_orbit={'orbit_index':i,'rep':orb['rep'],'size':orb['size'],'rank_hist':orb['rank_hist'],'fixed_is_rep':third_rep==orb['rep']}
                break
    for p in fixed:
        excluded.discard(p)
    points=[p for p in range(1,512) if p not in excluded]
    return fixed, excluded, points, orbits, third_orbit, len(stab)


def row_selected(key:int,basis:Sequence[int],include_dims:Set[int],through_points:Sequence[int],through_dims:Set[int],seed_keys:Set[int],seed_dims:Set[int]):
    d=key&0xF
    if d in include_dims:
        return True,'include_dim'
    if d in through_dims and through_points and all(in_rowspace(p,basis,n=9) for p in through_points):
        return True,'through_prefix'
    if key in seed_keys and d in seed_dims:
        return True,'seed'
    return False,''


def add_rank1_projection(model,x,idx,fixed,rank1_cache:Path,rank_s:int):
    rank1_pts, rank1_cons, rank1_meta, _ = load_or_build_rank1_projection(rank1_cache, Path('data/wang_f2_lb20/wang_subspace_lut.pkl'), rank_s, False)
    fixed_set=set(fixed); fixed_rank1={p:i for i,p in enumerate(rank1_pts) if p in fixed_set}
    added=0; skipped=0; empty=0; hist=Counter(); row_var_hist=Counter(); cap_hist=Counter(); fixed_hist=Counter()
    for mask,cap,key in rank1_cons:
        fixed_in=0
        for p,i in fixed_rank1.items():
            if (mask>>i)&1: fixed_in+=1
        cap_rem=cap-fixed_in
        vars_in=[]; y=mask
        while y:
            lb=y & -y; i=lb.bit_length()-1; y^=lb; p=rank1_pts[i]
            if p in idx and p not in fixed_set:
                vars_in.append(x[idx[p]])
        hist[(mask.bit_count(),cap)]+=1; row_var_hist[len(vars_in)]+=1; cap_hist[cap_rem]+=1; fixed_hist[fixed_in]+=1
        if cap_rem<0:
            model.AddBoolOr([]); added+=1; empty+=1
        elif len(vars_in)<=cap_rem:
            skipped+=1
        else:
            model.Add(sum(vars_in)<=cap_rem); added+=1
    return {'rank1_projection_rows_added':added,'rank1_projection_skipped_vacuous':skipped,'rank1_projection_empty':empty,'rank1_projection_meta':{'compressed_intersections':rank1_meta.get('compressed_intersections'),'nonvacuous_constraints':rank1_meta.get('nonvacuous_constraints')},'rank1_projection_hist':{f'{a},{b}':c for (a,b),c in sorted(hist.items())},'rank1_projection_row_var_hist':dict(sorted(row_var_hist.items())),'rank1_projection_residual_cap_hist':dict(sorted(cap_hist.items())),'rank1_projection_fixed_in_hist':dict(sorted(fixed_hist.items()))}


def solve(lut:Dict[int,int], lut_meta:dict, base_fixed:Sequence[int], third_rep:int|None, parent_second_rep:int|None,
          candidate_ranks:Set[int], include_dims:Set[int], through_points:Sequence[int], through_dims:Set[int],
          seed_keys:Set[int], seed_dims:Set[int], add_rank1_proj:bool, rank1_cache:Path,
          rank_s:int, time_limit:float, workers:int, out:Path, exclude_candidate_before:bool=True):
    from ortools.sat.python import cp_model
    t0=time.time(); fixed, excluded, pts, orbits, third_orbit, stab_size = branch_universe(base_fixed, third_rep, parent_second_rep, candidate_ranks, exclude_candidate_before)
    idx={p:i for i,p in enumerate(pts)}; fixed_set=set(fixed)
    model=cp_model.CpModel(); x=[model.NewBoolVar(f'x_{p}') for p in pts]
    model.Add(sum(x)==rank_s)
    for p in fixed:
        model.Add(x[idx[p]]==1)
    rows_by_dim=Counter(); rows_by_lb=Counter(); source_by_dim=Counter(); row_var_hist=Counter(); cap_hist=Counter(); fixed_in_hist=Counter(); added=0; skipped=0; empty=0
    for i,(key,lb0) in enumerate(lut.items(),1):
        basis=unpack_basis(key); take,src=row_selected(key,basis,include_dims,through_points,through_dims,seed_keys,seed_dims)
        if not take: continue
        lb=int(lb0); cap=rank_s-lb; pts_in=subspace_points_from_basis(basis); fixed_in=sum(1 for p in fixed if p in pts_in); cap_rem=cap-fixed_in; vars_in=[x[idx[p]] for p in pts_in if p in idx and p not in fixed_set]
        d=key&0xF; rows_by_dim[d]+=1; rows_by_lb[lb]+=1; source_by_dim[(src,d)]+=1; row_var_hist[len(vars_in)]+=1; cap_hist[cap_rem]+=1; fixed_in_hist[fixed_in]+=1
        if cap_rem<0:
            model.AddBoolOr([]); added+=1; empty+=1
        elif len(vars_in)<=cap_rem:
            skipped+=1
        else:
            model.Add(sum(vars_in)<=cap_rem); added+=1
        if i%1_000_000==0:
            print(f'scanned {i:,}/{len(lut):,}; wang_added={added:,}; elapsed={time.time()-t0:.1f}s', flush=True)
    r1stats={}
    if add_rank1_proj:
        r1stats=add_rank1_projection(model,x,idx,fixed,rank1_cache,rank_s)
    build_elapsed=time.time()-t0
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=time_limit; solver.parameters.num_search_workers=workers
    t1=time.time(); st=solver.Solve(model); solve_elapsed=time.time()-t1
    names={cp_model.OPTIMAL:'OPTIMAL',cp_model.FEASIBLE:'FEASIBLE',cp_model.INFEASIBLE:'INFEASIBLE',cp_model.UNKNOWN:'UNKNOWN',cp_model.MODEL_INVALID:'MODEL_INVALID'}
    sol=None
    if st in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        sol=[p for p in pts if solver.Value(x[idx[p]])]
    payload={'problem':'prefix/orbit fixed T-level Wang occupation CP-SAT','field':'F2','rank_s':rank_s,'base_fixed':list(base_fixed),'fixed_points':fixed,'parent_second_rep':parent_second_rep,'third_rep':third_rep,'third_orbit':third_orbit,'candidate_ranks':sorted(candidate_ranks),'stabilizer_size':stab_size,'candidate_orbit_count':len(orbits),'candidate_orbits_summary':[{'rep':o['rep'],'size':o['size'],'rank_hist':o['rank_hist']} for o in orbits],'exclude_candidate_before':exclude_candidate_before,'excluded_point_count':len(excluded),'excluded_rank_hist':dict(sorted(Counter(matrix_rank_of_mask(p) for p in excluded).items())),'variable_point_count':len(pts),'variable_rank_hist':dict(sorted(Counter(matrix_rank_of_mask(p) for p in pts).items())),'include_dims':sorted(include_dims),'through_points':list(through_points),'through_dims':sorted(through_dims),'seed_dims':sorted(seed_dims),'seed_key_count':len(seed_keys),'wang_rows_added':added,'wang_rows_by_dim':dict(sorted(rows_by_dim.items())),'wang_rows_by_lb':dict(sorted(rows_by_lb.items())),'wang_source_by_dim':{f'{s},{d}':c for (s,d),c in sorted(source_by_dim.items())},'wang_row_var_hist':dict(sorted(row_var_hist.items())),'wang_residual_cap_hist':dict(sorted(cap_hist.items())),'wang_fixed_in_hist':dict(sorted(fixed_in_hist.items())),'wang_skipped_vacuous':skipped,'wang_empty':empty,**r1stats,'solver_status':names.get(st,str(st)),'solver_status_code':int(st),'solver_walltime':float(solver.WallTime()),'solver_num_conflicts':int(solver.NumConflicts()),'solver_num_branches':int(solver.NumBranches()),'build_elapsed_sec':build_elapsed,'solve_elapsed_sec':solve_elapsed,'support':sol,'support_dict':None if sol is None else {str(p):1 for p in sol},'support_size':None if sol is None else len(sol),'support_rank_hist':None if sol is None else dict(sorted(Counter(matrix_rank_of_mask(p) for p in sol).items())),'lut_meta_brief':{'coverage_ok':lut_meta.get('coverage_ok'),'conflict_count':lut_meta.get('conflict_count'),'subspace_count':lut_meta.get('subspace_count')},'meaning':'CP-SAT result for a symmetry-refined support branch. SAT supports require full-LUT scanning; INFEASIBLE requires CNF/DRAT replay for a mathematical proof.'}
    out.parent.mkdir(parents=True,exist_ok=True); out.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:payload[k] for k in ['solver_status','fixed_points','third_orbit','candidate_orbit_count','variable_point_count','support_size','support_rank_hist','wang_rows_added','build_elapsed_sec','solve_elapsed_sec']},indent=2,sort_keys=True)); print('saved',out)


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')); ap.add_argument('--rank',type=int,default=20); ap.add_argument('--base-fixed',required=True); ap.add_argument('--parent-second-rep',type=int,default=None); ap.add_argument('--candidate-ranks',default='2,3'); ap.add_argument('--list-orbits',action='store_true'); ap.add_argument('--third-rep',type=int,default=None); ap.add_argument('--include-dims',default='1,2,3'); ap.add_argument('--through-points',default=''); ap.add_argument('--through-dims',default='4-8'); ap.add_argument('--seed-dims',default='4-7'); ap.add_argument('--seed-json',type=Path,action='append',default=[]); ap.add_argument('--no-rank1-projection',action='store_true'); ap.add_argument('--rank1-cache',type=Path,default=Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl')); ap.add_argument('--time-limit',type=float,default=300); ap.add_argument('--workers',type=int,default=8); ap.add_argument('--out',type=Path,default=None); ap.add_argument('--no-exclude-candidate-before',action='store_true'); args=ap.parse_args()
    base=parse_ints(args.base_fixed); parent_excl=parent_exclusions_for_second(args.parent_second_rep); stab,orbs=candidate_orbits(base,parent_excl,parse_ranks(args.candidate_ranks))
    if args.list_orbits:
        print(json.dumps({'base_fixed':base,'parent_second_rep':args.parent_second_rep,'parent_excluded_count':len(parent_excl),'parent_excluded_rank_hist':dict(sorted(Counter(matrix_rank_of_mask(p) for p in parent_excl).items())),'candidate_ranks':sorted(parse_ranks(args.candidate_ranks)),'stabilizer_size':len(stab),'candidate_orbit_count':len(orbs),'orbits':[{'rep':o['rep'],'size':o['size'],'rank_hist':o['rank_hist']} for o in orbs]},indent=2,sort_keys=True)); return
    if args.third_rep is None or args.out is None:
        raise SystemExit('--third-rep and --out are required unless --list-orbits')
    lut,meta=load_lut(args.lut); print(f'loaded LUT {len(lut):,} coverage={meta.get("coverage_ok")} conflicts={meta.get("conflict_count")}')
    seed_keys=set()
    for p in args.seed_json:
        got=collect_violation_keys(p); print(f'seed {p}: {len(got)} keys'); seed_keys.update(got)
    through=parse_ints(args.through_points) if args.through_points.strip() else base
    solve(lut,meta,base,args.third_rep,args.parent_second_rep,parse_ranks(args.candidate_ranks),parse_dims(args.include_dims),through,parse_dims(args.through_dims),seed_keys,parse_dims(args.seed_dims),not args.no_rank1_projection,args.rank1_cache,args.rank,args.time_limit,args.workers,args.out,not args.no_exclude_candidate_before)

if __name__=='__main__': main()
