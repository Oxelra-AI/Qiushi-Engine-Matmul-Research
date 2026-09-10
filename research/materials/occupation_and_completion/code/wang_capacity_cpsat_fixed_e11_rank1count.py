#!/usr/bin/env python3
"""Fixed-E11 Wang support CP-SAT with explicit rank-1 count control.

This is a research instrument for the remaining mixed rank-20 support branches
over F2.  It reuses the fixed-E11 second-orbit branch semantics and can include
large Wang row blocks plus the full compressed projection onto rank-1 points.
It additionally constrains the number of selected rank-1 A-points, allowing us
to test whether the near-saturated rank-1 cases (18,17,...) are actually live.

SAT supports are still only support candidates and must be scanned against the
complete Wang LUT.  INFEASIBLE runs are solver evidence; theorem use requires a
CNF/DRAT replay or another independently checkable proof object.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Sequence, Set

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_capacity_profile import load_or_build as load_or_build_rank1_projection  # noqa: E402
from wang_capacity_lazy import in_rowspace, matrix_rank_of_mask, unpack_basis, subspace_points_from_basis  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11, collect_violation_keys, parse_dims, stab_e11_orbits  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def branch_points(second_rep: int, exclude_orbits_before: bool = True):
    fixed = [E11]
    if second_rep != E11:
        fixed.append(second_rep)
    excluded: Set[int] = set()
    if exclude_orbits_before and second_rep != E11:
        found = False
        for orb in stab_e11_orbits():
            if orb['rep'] == second_rep:
                found = True
                break
            excluded.update(int(p) for p in orb['members'])
        if not found:
            raise ValueError(f'{second_rep} is not a Stab(E11) representative')
        for p in fixed:
            excluded.discard(p)
    pts = [p for p in range(1,512) if p not in excluded]
    return fixed, excluded, pts


def row_selected(key: int, basis: Sequence[int], fixed: Sequence[int], include_dims: Set[int],
                 through_e11_dims: Set[int], through_pair_dims: Set[int], seed_keys: Set[int], seed_dims: Set[int]):
    d = key & 0xF
    if d in include_dims:
        return True, 'include_dim'
    if d in through_pair_dims and all(in_rowspace(p, basis, n=9) for p in fixed):
        return True, 'through_pair'
    if d in through_e11_dims and in_rowspace(E11, basis, n=9):
        return True, 'through_e11'
    if key in seed_keys and d in seed_dims:
        return True, 'seed'
    return False, ''


def add_rank1_projection_constraints(model, x, idx, fixed, rank1_pts, rank1_cons):
    fixed_set = set(fixed)
    fixed_rank1_index = {p:i for i,p in enumerate(rank1_pts) if p in fixed_set}
    rows_added=0; skipped=0; empty=0; hist=Counter(); cap_hist=Counter(); row_var_hist=Counter(); fixed_in_hist=Counter()
    for mask, cap, key in rank1_cons:
        fixed_in = 0
        for p, i in fixed_rank1_index.items():
            if (mask >> i) & 1:
                fixed_in += 1
        cap_rem = int(cap) - fixed_in
        vars_in = []
        y = int(mask)
        while y:
            lb = y & -y; i = lb.bit_length()-1; y ^= lb
            p = rank1_pts[i]
            if p in idx and p not in fixed_set:
                vars_in.append(x[idx[p]])
        hist[(int(mask).bit_count(), int(cap))] += 1
        cap_hist[cap_rem] += 1; row_var_hist[len(vars_in)] += 1; fixed_in_hist[fixed_in] += 1
        if cap_rem < 0:
            model.AddBoolOr([]); rows_added += 1; empty += 1
        elif len(vars_in) <= cap_rem:
            skipped += 1
        else:
            model.Add(sum(vars_in) <= cap_rem); rows_added += 1
    return {
        'rank1_projection_rows_added': rows_added,
        'rank1_projection_skipped_vacuous': skipped,
        'rank1_projection_empty': empty,
        'rank1_projection_hist': {f'{a},{b}':c for (a,b),c in sorted(hist.items())},
        'rank1_projection_residual_cap_hist': dict(sorted(cap_hist.items())),
        'rank1_projection_row_var_hist': dict(sorted(row_var_hist.items())),
        'rank1_projection_fixed_in_hist': dict(sorted(fixed_in_hist.items())),
    }


def solve(lut: Dict[int,int], lut_meta: dict, *, second_rep: int, rank_s: int,
          include_dims: Set[int], through_e11_dims: Set[int], through_pair_dims: Set[int],
          seed_keys: Set[int], seed_dims: Set[int], rank1_cache: Path,
          exact_rank1_count: int | None, min_rank1_count: int | None, max_rank1_count: int | None,
          time_limit: float, workers: int, out: Path, exclude_orbits_before: bool = True):
    from ortools.sat.python import cp_model

    t0 = time.time()
    fixed, excluded, pts = branch_points(second_rep, exclude_orbits_before)
    fixed_set = set(fixed); idx = {p:i for i,p in enumerate(pts)}
    model = cp_model.CpModel(); x=[model.NewBoolVar(f'x_{p}') for p in pts]
    model.Add(sum(x) == rank_s)
    for p in fixed:
        model.Add(x[idx[p]] == 1)
    rank1_vars = [x[idx[p]] for p in pts if matrix_rank_of_mask(p)==1]
    if exact_rank1_count is not None:
        model.Add(sum(rank1_vars) == exact_rank1_count)
    if min_rank1_count is not None:
        model.Add(sum(rank1_vars) >= min_rank1_count)
    if max_rank1_count is not None:
        model.Add(sum(rank1_vars) <= max_rank1_count)

    rows_by_dim=Counter(); rows_by_lb=Counter(); source_by_dim=Counter(); row_var_hist=Counter(); cap_hist=Counter(); fixed_in_hist=Counter()
    added=0; skipped=0; empty=0
    for i,(key,lb0) in enumerate(lut.items(),1):
        basis=unpack_basis(key); take,src=row_selected(key,basis,fixed,include_dims,through_e11_dims,through_pair_dims,seed_keys,seed_dims)
        if not take:
            continue
        lb=int(lb0); cap=rank_s-lb; pts_in=subspace_points_from_basis(basis)
        fixed_in=sum(1 for p in fixed if p in pts_in); cap_rem=cap-fixed_in
        vars_in=[x[idx[p]] for p in pts_in if p in idx and p not in fixed_set]
        d=key&0xF; rows_by_dim[d]+=1; rows_by_lb[lb]+=1; source_by_dim[(src,d)]+=1; row_var_hist[len(vars_in)]+=1; cap_hist[cap_rem]+=1; fixed_in_hist[fixed_in]+=1
        if cap_rem < 0:
            model.AddBoolOr([]); added+=1; empty+=1
        elif len(vars_in) <= cap_rem:
            skipped+=1
        else:
            model.Add(sum(vars_in)<=cap_rem); added+=1
        if i%1_000_000==0:
            print(f'scanned {i:,}/{len(lut):,}; wang_added={added:,}; elapsed={time.time()-t0:.1f}s', flush=True)

    rank1_pts, rank1_cons, rank1_meta, _ = load_or_build_rank1_projection(rank1_cache, Path('data/wang_f2_lb20/wang_subspace_lut.pkl'), rank_s, False)
    r1stats = add_rank1_projection_constraints(model, x, idx, fixed, rank1_pts, rank1_cons)
    build_elapsed=time.time()-t0
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=time_limit; solver.parameters.num_search_workers=workers
    t1=time.time(); st=solver.Solve(model); solve_elapsed=time.time()-t1
    names={cp_model.OPTIMAL:'OPTIMAL',cp_model.FEASIBLE:'FEASIBLE',cp_model.INFEASIBLE:'INFEASIBLE',cp_model.UNKNOWN:'UNKNOWN',cp_model.MODEL_INVALID:'MODEL_INVALID'}
    sol=None
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol=[p for p in pts if solver.Value(x[idx[p]])]
    payload={
        'problem':'fixed-E11 T-level Wang occupation CP-SAT with explicit rank-1 count',
        'field':'F2','rank_s':rank_s,'second_rep':second_rep,'fixed_points':fixed,
        'exact_rank1_count':exact_rank1_count,'min_rank1_count':min_rank1_count,'max_rank1_count':max_rank1_count,
        'include_dims':sorted(include_dims),'through_e11_dims':sorted(through_e11_dims),'through_pair_dims':sorted(through_pair_dims),'seed_dims':sorted(seed_dims),'seed_key_count':len(seed_keys),
        'rank1_projection_cache':str(rank1_cache),'rank1_projection_meta_brief':{'compressed_intersections':rank1_meta.get('compressed_intersections'),'nonvacuous_constraints':rank1_meta.get('nonvacuous_constraints')},
        'exclude_orbits_before':exclude_orbits_before,'variable_point_count':len(pts),'variable_rank_hist':dict(sorted(Counter(matrix_rank_of_mask(p) for p in pts).items())),'excluded_point_count':len(excluded),'excluded_rank_hist':dict(sorted(Counter(matrix_rank_of_mask(p) for p in excluded).items())),
        'wang_rows_added':added,'wang_rows_by_dim':dict(sorted(rows_by_dim.items())),'wang_rows_by_lb':dict(sorted(rows_by_lb.items())),'wang_source_by_dim':{f'{s},{d}':c for (s,d),c in sorted(source_by_dim.items())},'wang_row_var_hist':dict(sorted(row_var_hist.items())),'wang_residual_cap_hist':dict(sorted(cap_hist.items())),'wang_fixed_in_row_hist':dict(sorted(fixed_in_hist.items())),'wang_skipped_vacuous':skipped,'wang_empty':empty,
        **r1stats,
        'solver_status':names.get(st,str(st)),'solver_status_code':int(st),'solver_walltime':float(solver.WallTime()),'solver_num_conflicts':int(solver.NumConflicts()),'solver_num_branches':int(solver.NumBranches()),'build_elapsed_sec':build_elapsed,'solve_elapsed_sec':solve_elapsed,
        'support':sol,'support_dict':None if sol is None else {str(p):1 for p in sol},'support_size':None if sol is None else len(sol),'support_rank_hist':None if sol is None else dict(sorted(Counter(matrix_rank_of_mask(p) for p in sol).items())),
        'lut_meta_brief':{'coverage_ok':lut_meta.get('coverage_ok'),'conflict_count':lut_meta.get('conflict_count'),'subspace_count':lut_meta.get('subspace_count')},
        'meaning':'CP-SAT support-count probe for a symmetry-refined branch. SAT supports require full-LUT scanning; INFEASIBLE requires CNF/DRAT replay before theorem use.'
    }
    out.parent.mkdir(parents=True,exist_ok=True); out.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:payload[k] for k in ['solver_status','second_rep','exact_rank1_count','min_rank1_count','max_rank1_count','support_size','support_rank_hist','wang_rows_added','rank1_projection_rows_added','build_elapsed_sec','solve_elapsed_sec']},indent=2,sort_keys=True)); print('saved',out)


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')); ap.add_argument('--rank',type=int,default=20); ap.add_argument('--second-rep',type=int,required=True); ap.add_argument('--include-dims',default='1,2,3'); ap.add_argument('--through-e11-dims',default=''); ap.add_argument('--through-pair-dims',default='4-8'); ap.add_argument('--seed-dims',default='4-7'); ap.add_argument('--seed-json',type=Path,action='append',default=[]); ap.add_argument('--rank1-cache',type=Path,default=Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl')); ap.add_argument('--exact-rank1-count',type=int,default=None); ap.add_argument('--min-rank1-count',type=int,default=None); ap.add_argument('--max-rank1-count',type=int,default=None); ap.add_argument('--time-limit',type=float,default=300); ap.add_argument('--workers',type=int,default=8); ap.add_argument('--out',type=Path,required=True); ap.add_argument('--no-exclude-orbits-before',action='store_true'); args=ap.parse_args()
    lut,meta=load_lut(args.lut); print(f'loaded LUT {len(lut):,} coverage={meta.get("coverage_ok")} conflicts={meta.get("conflict_count")}')
    seed_keys=set()
    for p in args.seed_json:
        got=collect_violation_keys(p); print(f'seed {p}: {len(got)} keys'); seed_keys.update(got)
    solve(lut,meta,second_rep=args.second_rep,rank_s=args.rank,include_dims=parse_dims(args.include_dims),through_e11_dims=parse_dims(args.through_e11_dims),through_pair_dims=parse_dims(args.through_pair_dims),seed_keys=seed_keys,seed_dims=parse_dims(args.seed_dims),rank1_cache=args.rank1_cache,exact_rank1_count=args.exact_rank1_count,min_rank1_count=args.min_rank1_count,max_rank1_count=args.max_rank1_count,time_limit=args.time_limit,workers=args.workers,out=args.out,exclude_orbits_before=not args.no_exclude_orbits_before)


if __name__=='__main__': main()
