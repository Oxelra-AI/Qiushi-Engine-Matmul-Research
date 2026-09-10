#!/usr/bin/env python3
"""CP-SAT exploration of fixed-E11 Wang occupation branches with full row blocks.

This is an exact finite support-feasibility solver over the Wang occupation LUT,
using OR-Tools linear cardinality constraints rather than expanding rows into
forbidden subsets.  It is not a proof-producing final object, but it tests which
large row families should be included in later CNF/DRAT proof objects.

Default model for a Stab(E11) second representative q:
  * fix E11 and q;
  * omit all earlier Stab(E11)-orbit points for invariant-parent branching;
  * require exactly 20 selected projective A-points;
  * include all Wang rows in dimensions 1,2,3;
  * include all Wang rows of dimensions 4..8 containing E11 (or optionally the
    full fixed pair E11,q);
  * include optional seed rows from previous full-LUT scans.

Any FEASIBLE/OPTIMAL support must still be scanned against the complete
8,283,458-row LUT before it is meaningful.  INFEASIBLE is solver evidence for a
branch but should be converted to a DRAT-producing CNF before being used as a
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
from typing import Dict, Sequence, Set

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

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


def row_selected(key: int, basis: Sequence[int], fixed: Sequence[int], include_dims: Set[int], through_e11_dims: Set[int], through_pair_dims: Set[int], seed_keys: Set[int], seed_dims: Set[int]) -> tuple[bool,str]:
    d = key & 0xF
    if d in include_dims:
        return True, 'include_dim'
    if d in through_pair_dims:
        if all(in_rowspace(p,basis,n=9) for p in fixed):
            return True, 'through_pair'
    if d in through_e11_dims:
        if in_rowspace(E11,basis,n=9):
            return True, 'through_e11'
    if key in seed_keys and d in seed_dims:
        return True, 'seed'
    return False, ''


def solve(lut: Dict[int,int], lut_meta: dict, second_rep: int, rank_s: int,
          include_dims: Set[int], through_e11_dims: Set[int], through_pair_dims: Set[int],
          seed_keys: Set[int], seed_dims: Set[int], time_limit: float, workers: int,
          out: Path, exclude_orbits_before: bool = True) -> dict:
    from ortools.sat.python import cp_model

    t0 = time.time()
    fixed, excluded, pts = branch_points(second_rep, exclude_orbits_before)
    fixed_set = set(fixed)
    idx = {p:i for i,p in enumerate(pts)}
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x_{p}') for p in pts]
    model.Add(sum(x) == rank_s)
    for p in fixed:
        model.Add(x[idx[p]] == 1)

    rows_by_dim = Counter(); rows_by_lb = Counter(); source_by_dim = Counter(); row_var_hist = Counter(); residual_cap_hist = Counter(); fixed_in_hist = Counter()
    skipped_vacuous = 0; added = 0; empty_rows = 0
    # Build rows. Repeated lists of Python variables are heavy but acceptable for these branch tests.
    for i,(key,lb0) in enumerate(lut.items(),1):
        basis = unpack_basis(key)
        take, src = row_selected(key,basis,fixed,include_dims,through_e11_dims,through_pair_dims,seed_keys,seed_dims)
        if not take:
            continue
        lb = int(lb0); cap = rank_s - lb
        pts_in = subspace_points_from_basis(basis)
        fixed_in = sum(1 for p in fixed if p in pts_in)
        cap_rem = cap - fixed_in
        vars_in = [x[idx[p]] for p in pts_in if p in idx and p not in fixed_set]
        d = key & 0xF
        rows_by_dim[d] += 1; rows_by_lb[lb] += 1; source_by_dim[(src,d)] += 1; row_var_hist[len(vars_in)] += 1; residual_cap_hist[cap_rem] += 1; fixed_in_hist[fixed_in] += 1
        if cap_rem < 0:
            model.AddBoolOr([]); empty_rows += 1; added += 1
        elif len(vars_in) <= cap_rem:
            skipped_vacuous += 1
        else:
            model.Add(sum(vars_in) <= cap_rem); added += 1
        if i % 1_000_000 == 0:
            print(f'scanned {i:,}/{len(lut):,}; added={added:,}; elapsed={time.time()-t0:.1f}s', flush=True)
    build_elapsed = time.time()-t0
    solver = cp_model.CpSolver(); solver.parameters.max_time_in_seconds = time_limit; solver.parameters.num_search_workers = workers
    t1 = time.time(); status = solver.Solve(model); solve_elapsed = time.time()-t1
    names={cp_model.OPTIMAL:'OPTIMAL',cp_model.FEASIBLE:'FEASIBLE',cp_model.INFEASIBLE:'INFEASIBLE',cp_model.UNKNOWN:'UNKNOWN',cp_model.MODEL_INVALID:'MODEL_INVALID'}
    sol = None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = [p for p in pts if solver.Value(x[idx[p]])]
    payload = {
        'problem':'fixed-E11 T-level rank-20 Wang occupation CP-SAT with full row blocks',
        'field':'F2','rank_s':rank_s,'second_rep':second_rep,'fixed_points':fixed,
        'meaning':'Exact support feasibility over the encoded Wang row blocks. FEASIBLE support must be full-LUT scanned; INFEASIBLE needs CNF/DRAT reproduction for a proof object.',
        'include_dims':sorted(include_dims),'through_e11_dims':sorted(through_e11_dims),'through_pair_dims':sorted(through_pair_dims),'seed_dims':sorted(seed_dims),'seed_key_count':len(seed_keys),
        'exclude_orbits_before':exclude_orbits_before,'variable_point_count':len(pts),'variable_rank_hist':dict(sorted(Counter(matrix_rank_of_mask(p) for p in pts).items())),'excluded_point_count':len(excluded),'excluded_rank_hist':dict(sorted(Counter(matrix_rank_of_mask(p) for p in excluded).items())),
        'rows_added':added,'rows_seen_selected':sum(rows_by_dim.values()),'rows_by_dim':dict(sorted(rows_by_dim.items())),'rows_by_lb':dict(sorted(rows_by_lb.items())),'source_by_dim':{f'{s},{d}':c for (s,d),c in sorted(source_by_dim.items())},'row_var_hist':dict(sorted(row_var_hist.items())),'residual_cap_hist':dict(sorted(residual_cap_hist.items())),'fixed_in_row_hist':dict(sorted(fixed_in_hist.items())),'skipped_vacuous_rows':skipped_vacuous,'empty_rows':empty_rows,
        'solver_status':names.get(status,str(status)),'solver_status_code':int(status),'solver_walltime':float(solver.WallTime()),'solver_num_conflicts':int(solver.NumConflicts()),'solver_num_branches':int(solver.NumBranches()),'solve_elapsed_sec':solve_elapsed,'build_elapsed_sec':build_elapsed,
        'support':sol,'support_dict':None if sol is None else {str(p):1 for p in sol},'support_size':None if sol is None else len(sol),'support_rank_hist':None if sol is None else dict(sorted(Counter(matrix_rank_of_mask(p) for p in sol).items())),
        'lut_meta_brief':{'coverage_ok':lut_meta.get('coverage_ok'),'conflict_count':lut_meta.get('conflict_count'),'subspace_count':lut_meta.get('subspace_count')},
    }
    out.parent.mkdir(parents=True,exist_ok=True); out.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:payload[k] for k in ['solver_status','rows_added','rows_by_dim','variable_point_count','support_size','support_rank_hist','build_elapsed_sec','solve_elapsed_sec']},indent=2,sort_keys=True))
    print('saved',out)
    return payload


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')); ap.add_argument('--rank',type=int,default=20); ap.add_argument('--second-rep',type=int,required=True); ap.add_argument('--include-dims',default='1,2,3'); ap.add_argument('--through-e11-dims',default='4-8'); ap.add_argument('--through-pair-dims',default=''); ap.add_argument('--seed-dims',default='4-7'); ap.add_argument('--seed-json',type=Path,action='append',default=[]); ap.add_argument('--time-limit',type=float,default=300); ap.add_argument('--workers',type=int,default=8); ap.add_argument('--out',type=Path,required=True); ap.add_argument('--no-exclude-orbits-before',action='store_true'); args=ap.parse_args()
    lut,meta=load_lut(args.lut); print(f'loaded LUT {len(lut):,} coverage={meta.get("coverage_ok")} conflicts={meta.get("conflict_count")}')
    seed_keys=set()
    for p in args.seed_json:
        got=collect_violation_keys(p); print(f'seed {p}: {len(got)} keys'); seed_keys.update(got)
    solve(lut,meta,args.second_rep,args.rank,parse_dims(args.include_dims),parse_dims(args.through_e11_dims),parse_dims(args.through_pair_dims),seed_keys,parse_dims(args.seed_dims),args.time_limit,args.workers,args.out,not args.no_exclude_orbits_before)

if __name__=='__main__': main()
