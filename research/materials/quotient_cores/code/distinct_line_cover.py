#!/usr/bin/env python3
"""analysis: exact-cover view of the remaining distinct E11-core Wang system.

After analysis, the E11 rank-19 core branch is distinct projected A-directions.
The complete Wang table imposes sum_{p in U} x_p <= 19-L(U).  Since total
sum x_p = 19, the complement of each row is a lower-bound row

    sum_{p notin U} x_p >= L(U).

For a distinct 19-point support, if L(U) is close to 19 this forces a small
covering condition outside high-L subspaces.  This script builds a CP-SAT model
using only the strongest complete Wang rows (threshold L) and optional existing
low-violation hints.  It is a research instrument: FEASIBLE/UNKNOWN/INFEASIBLE
are not theorem-level unless converted into a proof object, but the supports it
produces are exact candidates for full complete-Wang rescanning and B/C tests.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path
from typing import List, Dict

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import ROOT, build_core_constraints, complete_core_wang_scan, saturation_domains, transversal_failures
from quotient_rank_cuts import build_contractions, point_mask_for_q
from candidate_source_qcut_scan import eval_candidate_sources
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis

OUTDIR = ROOT / 'workspace/data/distinct_line_cover'
ALL_POINTS = list(range(1, 256))
ALLMASK = (1 << 255) - 1


def bitset_points(bitset: int) -> List[int]:
    return [i + 1 for i in range(255) if (bitset >> i) & 1]


def load_hints(paths: List[Path]) -> List[List[int]]:
    hints=[]
    seen=set()
    for path in paths:
        if not path.exists():
            continue
        d=json.loads(path.read_text())
        for r in d.get('rounds', []):
            A=r.get('support') or r.get('A_cols')
            if not A or len(A)!=19 or len(set(A))!=19:
                continue
            key=tuple(int(x) for x in A)
            if key in seen:
                continue
            seen.add(key); hints.append(list(key))
    return hints


def analyze_support(label: str, A: List[int], records, T, contractions, masks):
    scan=complete_core_wang_scan(label,A,19,records,max_head=25)
    sat=saturation_domains(T,A)
    trans=transversal_failures(sat['sat_records'], sat['B_domains'], sat['C_domains'],9,9,max_report=10)
    qscan=eval_candidate_sources(label,A,contractions,masks,max_source_size=2,max_store=20)
    return {
        'label': label,
        'A_cols': A,
        'complete_wang_violations': scan['complete_violation_count'],
        'max_excess': scan['max_excess'],
        'violations_by_dim8': scan['violations_by_dim8'],
        'violations_by_L': scan['violations_by_full_lut_L'],
        'violations_head': scan['violations_head'],
        'zero_domain_terms': len(sat['summary']['zero_domain_terms']),
        'linear_pass': sat['summary']['linear_membership']['necessary_linear_test_passed'],
        'affine_dim': sat['summary']['linear_membership']['affine_solution_dimension_if_consistent'],
        'saturated_contractions': sat['summary']['saturated_contraction_count'],
        'transversal_failures': trans['failure_count_reported'],
        'quotient_rank_violations_size2': qscan['violated_guarded_instances'],
    }


def main():
    from ortools.sat.python import cp_model
    ap=argparse.ArgumentParser()
    ap.add_argument('--threshold-L', type=int, default=17)
    ap.add_argument('--solver-time', type=float, default=180.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--seed', type=int, default=4801)
    ap.add_argument('--enumerate', type=int, default=1, help='number of distinct supports to enumerate')
    ap.add_argument('--use-complement-lower', action='store_true')
    ap.add_argument('--forbid-hints', action='store_true')
    ap.add_argument('--out', type=Path, default=OUTDIR / 'threshold_L17_cover.json')
    args=ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0=time.time()

    lut,_=load_lut(ROOT/'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    core=CoreQuotient(1)
    records, meta=build_core_constraints(core,lut)
    T=np.load(ROOT/'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8)%2
    contractions=build_contractions(T)
    masks={q:point_mask_for_q(q) for q in contractions}

    selected=[]
    by_dim=Counter(); by_L=Counter(); by_cap=Counter(); complement_size=Counter()
    for rec in records:
        L=int(rec['L']); cap=19-L
        if L < args.threshold_L:
            continue
        if cap>=19:
            continue
        pts=bitset_points(int(rec['point_bitset']))
        if not pts:
            continue
        selected.append((rec, pts, cap))
        by_dim[int(rec['dim8'])]+=1; by_L[L]+=1; by_cap[cap]+=1; complement_size[255-len(pts)]+=1

    model=cp_model.CpModel()
    x={p:model.NewBoolVar(f'x_{p}') for p in ALL_POINTS}
    model.Add(sum(x[p] for p in ALL_POINTS)==19)
    for rec, pts, cap in selected:
        if args.use_complement_lower:
            pset=set(pts)
            outside=[x[p] for p in ALL_POINTS if p not in pset]
            model.Add(sum(outside) >= int(rec['L']))
        else:
            model.Add(sum(x[p] for p in pts) <= cap)

    # Contraction lower bounds are valid, cheap, and keep supports closer to actual core decompositions.
    clb=0
    for q,c in contractions.items():
        rk=int(c['rank'])
        if rk>0:
            model.Add(sum(x[p] for p in ALL_POINTS if ((q&p).bit_count()&1)) >= rk)
            clb+=1

    hints=load_hints([
        ROOT/'workspace/data/unconditional_qcuts/fresh_uncond_sep_10r.json',
        ROOT/'workspace/data/unconditional_qcuts/fresh_uncond_sep_50r.json',
        ROOT/'workspace/data/core_complete_transversal/core_e11_saturation_v3_complete_long.json',
    ])
    # Use the best known 15-violation support as hint unless forbidden.
    if hints:
        best=min(hints, key=lambda A: complete_core_wang_scan('hint',A,19,records,max_head=0)[0] if False else 0)
        # Hard-code preference to analysis round 8 if present, because it is the best known complete-Wang support.
        for A in hints:
            if A == [2,3,4,10,20,22,32,36,73,86,96,97,108,162,180,224,233,245,252]:
                best=A; break
        for p in ALL_POINTS:
            model.AddHint(x[p], 1 if p in set(best) else 0)
    if args.forbid_hints:
        for A in hints:
            model.Add(sum(x[p] for p in A) <= 18)

    build_sec=time.time()-t0
    solver=cp_model.CpSolver()
    solver.parameters.max_time_in_seconds=float(args.solver_time)
    solver.parameters.num_search_workers=int(args.workers)
    solver.parameters.random_seed=int(args.seed)

    solutions=[]
    statuses=[]
    for k in range(args.enumerate):
        ts=time.time(); st=solver.Solve(model); sec=time.time()-ts
        name=solver.StatusName(st); statuses.append({'iteration':k,'status':name,'solve_sec':round(sec,3)})
        print(f'iter {k} status={name} sec={sec:.2f}')
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            break
        A=[p for p in ALL_POINTS if solver.Value(x[p])]
        analysis=analyze_support(f'L{args.threshold_L}_solution_{k}',A,records,T,contractions,masks)
        solutions.append(analysis)
        print('  A=',A)
        print('  Wang',analysis['complete_wang_violations'],'zero',analysis['zero_domain_terms'],'lin',analysis['linear_pass'],'trans',analysis['transversal_failures'],'q',analysis['quotient_rank_violations_size2'])
        # block exact set for next enumeration
        model.Add(sum(x[p] for p in A) <= 18)

    out={
        'schema':'distinct_line_cover_v1',
        'field':'F2','core':'E11','rank_s':19,
        'threshold_L':args.threshold_L,
        'use_complement_lower':args.use_complement_lower,
        'selected_rows':len(selected),
        'selected_by_dim8':{str(k):int(v) for k,v in sorted(by_dim.items())},
        'selected_by_L':{str(k):int(v) for k,v in sorted(by_L.items())},
        'selected_by_cap':{str(k):int(v) for k,v in sorted(by_cap.items())},
        'contraction_lower_bounds':clb,
        'complete_core_table_meta':meta,
        'hint_count':len(hints),
        'forbid_hints':args.forbid_hints,
        'build_sec':round(build_sec,3),
        'solver_time_limit':args.solver_time,
        'statuses':statuses,
        'solutions':solutions,
        'elapsed_sec':round(time.time()-t0,3),
        'interpretation':'Restricted high-L complete-Wang model for distinct E11 core. Feasible supports are candidates only; complete Wang violations are computed against all 417199 rows.',
    }
    args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(args.out),'selected_rows':len(selected),'statuses':statuses,'solutions':len(solutions)},sort_keys=True))

if __name__=='__main__':
    main()
