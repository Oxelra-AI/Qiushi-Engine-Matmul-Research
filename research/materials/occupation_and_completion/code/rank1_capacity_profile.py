#!/usr/bin/env python3
"""Profile the rank-1-only projection of the full Wang occupation system.

The pure rank-1 branch has 49 variables.  This script caches the exact
compression of the full 8,283,458-row Wang LUT by intersections with those 49
rank-1 points, then asks CP-SAT for the maximum number of rank-1 points that can
be selected (optionally with E11 fixed), or for exact-size feasibility.  It is a
support-count instrument: any T-level support, even with higher-rank A-points,
cannot have a rank-1 subset that already violates these projected inequalities.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_only_capacity_cnf import compress_rank1, load_lut  # noqa: E402
from wang_capacity_lazy import matrix_rank_of_mask  # noqa: E402


def load_or_build(cache: Path, lut_path: Path, rank_s: int, force: bool = False):
    if cache.exists() and not force:
        with cache.open('rb') as f:
            payload = pickle.load(f)
        cached_rank_s = payload.get('rank_s')
        if cached_rank_s is not None and int(cached_rank_s) != int(rank_s):
            raise ValueError(f"rank-1 projection cache {cache} was built for rank_s={cached_rank_s}, not requested rank_s={rank_s}; rebuild with --force-rebuild or use a separate cache")
        return payload['pts'], payload['cons'], payload['meta'], payload.get('lut_meta', {})
    lut, lut_meta = load_lut(lut_path)
    pts, cons, meta = compress_rank1(lut, rank_s)
    cache.parent.mkdir(parents=True, exist_ok=True)
    with cache.open('wb') as f:
        pickle.dump({'pts': pts, 'cons': cons, 'meta': meta, 'lut_meta': lut_meta, 'rank_s': rank_s}, f, protocol=pickle.HIGHEST_PROTOCOL)
    return pts, cons, meta, lut_meta


def solve(pts: List[int], cons: List[Tuple[int,int,int]], fixed_point: int | None,
          exact_size: int | None, maximize: bool, time_limit: float, workers: int):
    from ortools.sat.python import cp_model
    model = cp_model.CpModel(); x=[model.NewBoolVar(f'x_{p}') for p in pts]
    idx={p:i for i,p in enumerate(pts)}
    if fixed_point is not None and fixed_point in idx:
        model.Add(x[idx[fixed_point]] == 1)
    elif fixed_point is not None:
        model.AddBoolOr([])
    for mask, cap, key in cons:
        inds=[i for i in range(len(pts)) if (mask >> i) & 1]
        if len(inds) > cap:
            model.Add(sum(x[i] for i in inds) <= cap)
    if exact_size is not None:
        model.Add(sum(x) == exact_size)
    if maximize:
        model.Maximize(sum(x))
    solver = cp_model.CpSolver(); solver.parameters.max_time_in_seconds=time_limit; solver.parameters.num_search_workers=workers
    t0=time.time(); st=solver.Solve(model); elapsed=time.time()-t0
    names={cp_model.OPTIMAL:'OPTIMAL',cp_model.FEASIBLE:'FEASIBLE',cp_model.INFEASIBLE:'INFEASIBLE',cp_model.UNKNOWN:'UNKNOWN',cp_model.MODEL_INVALID:'MODEL_INVALID'}
    sol=None
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol=[pts[i] for i in range(len(pts)) if solver.Value(x[i])]
    return {
        'status': names.get(st,str(st)), 'status_code': int(st), 'elapsed_sec': elapsed,
        'wall_time': float(solver.WallTime()), 'num_conflicts': int(solver.NumConflicts()), 'num_branches': int(solver.NumBranches()),
        'objective_value': None if not maximize or sol is None else float(solver.ObjectiveValue()),
        'best_objective_bound': None if not maximize else float(solver.BestObjectiveBound()),
        'solution': sol, 'solution_size': None if sol is None else len(sol),
        'solution_rank_hist': None if sol is None else dict(sorted(Counter(matrix_rank_of_mask(p) for p in sol).items())),
    }


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')); ap.add_argument('--cache',type=Path,default=Path('data/wang_capacity_rank1_only_cnf/rank1_intersection_cache.pkl')); ap.add_argument('--rank',type=int,default=20); ap.add_argument('--fixed-point',type=int,default=1); ap.add_argument('--no-fixed',action='store_true'); ap.add_argument('--exact-size',type=int,default=None); ap.add_argument('--maximize',action='store_true'); ap.add_argument('--time-limit',type=float,default=300); ap.add_argument('--workers',type=int,default=8); ap.add_argument('--force-rebuild',action='store_true'); ap.add_argument('--out',type=Path,required=True); args=ap.parse_args()
    pts,cons,meta,lut_meta=load_or_build(args.cache,args.lut,args.rank,args.force_rebuild)
    print(f'loaded compression pts={len(pts)} cons={len(cons)} cache={args.cache}')
    res=solve(pts,cons,None if args.no_fixed else args.fixed_point,args.exact_size,args.maximize,args.time_limit,args.workers)
    payload={'problem':'rank-1-only projection profile of full Wang occupation system','field':'F2','rank_s':args.rank,'fixed_point':None if args.no_fixed else args.fixed_point,'exact_size':args.exact_size,'maximize':args.maximize,'compression':meta,'lut_meta_brief':{'coverage_ok':lut_meta.get('coverage_ok'),'conflict_count':lut_meta.get('conflict_count'),'subspace_count':lut_meta.get('subspace_count')},'result':res,'meaning':'This constrains how many rank-1 A-points can appear in any full T-level support; CP-SAT optimality is computational evidence and should be CNF/DRAT reproduced if it becomes a theorem component.'}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:res[k] for k in ['status','objective_value','best_objective_bound','solution_size','elapsed_sec','num_conflicts','num_branches']},indent=2,sort_keys=True))
    print('saved',args.out)

if __name__=='__main__': main()
