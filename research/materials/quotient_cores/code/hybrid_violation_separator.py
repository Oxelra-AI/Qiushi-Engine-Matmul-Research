#!/usr/bin/env python3
"""analysis: adaptive separator using exact annihilator-weight Wang rows.

Start with high-L E11-core Wang rows (default L>=14) in the hybrid representation:
small U rows are direct point inequalities, large U rows are annihilator-weight
rows linked to the same Boolean support variables.  After each solve, rescan the
candidate against the complete 417199-row core table and add every newly violated
row.  This is a search/proof-engineering instrument, not a proof object.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints, saturation_domains, transversal_failures  # noqa: E402
from quotient_rank_cuts import build_contractions, point_mask_for_q  # noqa: E402
from candidate_source_qcut_scan import eval_candidate_sources  # noqa: E402
from wang_capacity_lazy import pack_basis, rref_basis, unpack_basis  # noqa: E402

OUTDIR = ROOT / 'workspace/data/hybrid_separator'
S = 19
POINTS = list(range(1, 256))


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}, payload.get('meta', {})


def parity_dot(q: int, p: int) -> int:
    return (int(q) & int(p)).bit_count() & 1


def bitset_points(bitset: int) -> List[int]:
    return [i+1 for i in range(255) if (int(bitset) >> i) & 1]


def annihilator_points(basis: Sequence[int], n: int = 8) -> List[int]:
    bs = [int(b) for b in basis]
    return [q for q in range(1, 1 << n) if all(parity_dot(q, u) == 0 for u in bs)]


def D_key_from_rec(rec: dict) -> int:
    D = annihilator_points(unpack_basis(int(rec['key8'])), 8)
    return pack_basis(rref_basis(D, n=8))


def load_best_hint(records: Sequence[dict]) -> List[int] | None:
    paths = [
        ROOT / 'workspace/data/distinct_line_cover/threshold_L15_300s.json',
        ROOT / 'workspace/data/unconditional_qcuts/fresh_uncond_sep_10r.json',
        ROOT / 'workspace/data/core_complete_transversal/core_e11_saturation_v3_complete_long.json',
    ]
    hints=[]
    for path in paths:
        if not path.exists(): continue
        d=json.loads(path.read_text())
        containers=[]
        containers.extend(d.get('solutions', []))
        containers.extend(d.get('rounds', []))
        for r in containers:
            A=r.get('A_cols') or r.get('support')
            if A and len(A)==S and len(set(A))==S:
                hints.append([int(x) for x in A])
    if not hints: return None
    def viol_count(A):
        sb=0
        for p in A: sb |= 1 << (p-1)
        cnt=0
        for rec in records:
            occ=(int(rec['point_bitset']) & sb).bit_count()
            if occ > S-int(rec['L']): cnt += 1
        return cnt
    return min(hints, key=viol_count)


def scan_all(A: Sequence[int], records: Sequence[dict], max_head: int = 40) -> dict:
    sb=0
    for p in A: sb |= 1 << (int(p)-1)
    violations=[]
    by_dim=Counter(); by_L=Counter(); by_excess=Counter(); by_dual_k=Counter()
    for idx, rec in enumerate(records):
        L=int(rec['L']); cap=S-L
        occ=(int(rec['point_bitset']) & sb).bit_count()
        if occ > cap:
            ex=occ-cap
            by_dim[int(rec['dim8'])]+=1; by_L[L]+=1; by_excess[ex]+=1; by_dual_k[8-int(rec['dim8'])]+=1
            violations.append((ex, L, int(rec['dim8']), idx, occ))
    violations.sort(key=lambda z: (z[0], z[1], z[4], -z[2]), reverse=True)
    head=[]
    for ex,L,d,idx,occ in violations[:max_head]:
        rec=records[idx]
        head.append({
            'record_index': idx,
            'key8': int(rec['key8']),
            'basis8': list(unpack_basis(int(rec['key8']))),
            'dim8': d,
            'codim_dual_k': 8-d,
            'D_key': D_key_from_rec(rec) if d < 8 else None,
            'D_nonzero': annihilator_points(unpack_basis(int(rec['key8'])),8) if d < 8 else [],
            'key9': int(rec['key9']),
            'L': L,
            'cap': S-L,
            'occupancy': occ,
            'excess': ex,
            'point_count': int(rec['point_count']),
        })
    return {
        'complete_violation_count': len(violations),
        'max_excess': max([v[0] for v in violations], default=0),
        'violations_by_dim8': {str(k): int(v) for k,v in sorted(by_dim.items())},
        'violations_by_L': {str(k): int(v) for k,v in sorted(by_L.items())},
        'violations_by_excess': {str(k): int(v) for k,v in sorted(by_excess.items())},
        'violations_by_dual_k': {str(k): int(v) for k,v in sorted(by_dual_k.items())},
        'violation_indices': [idx for _,_,_,idx,_ in violations],
        'violations_head': head,
    }


def main():
    from ortools.sat.python import cp_model
    ap=argparse.ArgumentParser()
    ap.add_argument('--initial-threshold-L', type=int, default=14)
    ap.add_argument('--annihilator-dim-min', type=int, default=5)
    ap.add_argument('--max-rounds', type=int, default=5)
    ap.add_argument('--solver-time', type=float, default=180.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--seed', type=int, default=4950)
    ap.add_argument('--max-add-per-round', type=int, default=0, help='0 means add all currently violated rows')
    ap.add_argument('--out', type=Path, default=OUTDIR / 'hybrid_separator_L14_5r.json')
    args=ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0=time.time()

    lut,_=load_lut(ROOT/'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records, meta=build_core_constraints(CoreQuotient(1), lut)
    T=np.load(ROOT/'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8)%2
    contractions=build_contractions(T)
    masks={q: point_mask_for_q(q) for q in contractions}

    model=cp_model.CpModel()
    x={p:model.NewBoolVar(f'x_{p}') for p in POINTS}
    model.Add(sum(x[p] for p in POINTS)==S)
    w={q:model.NewIntVar(0,S,f'w_{q}') for q in POINTS}
    for q in POINTS:
        model.Add(w[q] == sum(x[p] for p in POINTS if parity_dot(q,p)))

    added=set(); added_reasons={}; repr_count=Counter(); by_dim=Counter(); by_L=Counter(); direct_terms=0; ann_terms=0
    examples=[]

    def add_row(idx: int, reason: str) -> bool:
        nonlocal direct_terms, ann_terms
        if idx in added: return False
        rec=records[idx]
        L=int(rec['L']); cap=S-L; d=int(rec['dim8'])
        pts=bitset_points(int(rec['point_bitset']))
        if cap>=S or (not pts and cap>=0):
            return False
        direct_n=len(pts)
        ann_n=(1 << (8-d))-1 if d<8 else 10**9
        use_ann=(d>=args.annihilator_dim_min and ann_n<direct_n)
        if use_ann:
            D=annihilator_points(unpack_basis(int(rec['key8'])),8)
            k=8-d
            model.Add(sum(w[q] for q in D) >= (1 << (k-1))*L)
            repr_count['annihilator'] += 1; ann_terms += len(D)
            if len(examples)<25:
                examples.append({'idx':idx,'reason':reason,'repr':'annihilator','dim8':d,'L':L,'D_nonzero':D,'rhs':(1 << (k-1))*L,'direct_terms':direct_n,'ann_terms':len(D)})
        else:
            model.Add(sum(x[p] for p in pts) <= cap)
            repr_count['direct'] += 1; direct_terms += len(pts)
        added.add(idx); added_reasons[idx]=reason; by_dim[d]+=1; by_L[L]+=1
        return True

    for idx, rec in enumerate(records):
        if int(rec['L']) >= args.initial_threshold_L:
            add_row(idx, 'initial_threshold')
    for q,c in contractions.items():
        rk=int(c['rank'])
        if rk>0:
            model.Add(w[q] >= rk)

    hint=load_best_hint(records)
    if hint:
        hs=set(hint)
        for p in POINTS:
            model.AddHint(x[p], 1 if p in hs else 0)

    rounds=[]; final_status=None
    for r in range(args.max_rounds):
        solver=cp_model.CpSolver()
        solver.parameters.max_time_in_seconds=float(args.solver_time)
        solver.parameters.num_search_workers=int(args.workers)
        solver.parameters.random_seed=int(args.seed)+r
        ts=time.time(); st=solver.Solve(model); sec=time.time()-ts
        name=solver.StatusName(st)
        entry={'round':r,'solver_status':name,'solve_sec':round(sec,3),'active_rows':len(added),'repr_count':{str(k):int(v) for k,v in sorted(repr_count.items())}}
        print(f'round {r} status={name} rows={len(added)} sec={sec:.1f}')
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            final_status=name; rounds.append(entry); break
        A=[p for p in POINTS if solver.Value(x[p])]
        scan=scan_all(A, records, max_head=50)
        sat=saturation_domains(T,A)
        trans=transversal_failures(sat['sat_records'], sat['B_domains'], sat['C_domains'],9,9,max_report=10)
        qscan=eval_candidate_sources(f'round{r}',A,contractions,masks,max_source_size=2,max_store=20)
        entry.update({
            'A_cols':A,
            'complete_wang_violations':scan['complete_violation_count'],
            'max_excess':scan['max_excess'],
            'violations_by_dim8':scan['violations_by_dim8'],
            'violations_by_L':scan['violations_by_L'],
            'violations_by_dual_k':scan['violations_by_dual_k'],
            'violations_head':scan['violations_head'],
            'zero_domain_terms':len(sat['summary']['zero_domain_terms']),
            'linear_pass':sat['summary']['linear_membership']['necessary_linear_test_passed'],
            'affine_dim':sat['summary']['linear_membership']['affine_solution_dimension_if_consistent'],
            'transversal_failures':trans['failure_count_reported'],
            'quotient_rank_violations_size2':qscan['violated_guarded_instances'],
        })
        if scan['complete_violation_count']==0:
            final_status='COMPLETE_WANG_FEASIBLE'
            rounds.append(entry)
            break
        add_indices=scan['violation_indices'] if args.max_add_per_round<=0 else scan['violation_indices'][:args.max_add_per_round]
        new=0
        for idx in add_indices:
            if add_row(idx, f'round{r}_violation'):
                new += 1
        entry['new_rows_added_from_violations']=new
        print('  A',A,'viol',scan['complete_violation_count'],'byL',scan['violations_by_L'],'new',new,'zero',entry['zero_domain_terms'],'lin',entry['linear_pass'],'trans',entry['transversal_failures'],'q2',entry['quotient_rank_violations_size2'])
        rounds.append(entry)
        if new==0:
            final_status='SAT_WITH_ONLY_ALREADY_ADDED_VIOLATIONS'
            break

    out={
        'schema':'hybrid_violation_separator_v1',
        'field':'F2','core':'E11','rank_s':S,
        'initial_threshold_L':int(args.initial_threshold_L),
        'annihilator_dim_min':int(args.annihilator_dim_min),
        'complete_core_table_meta':meta,
        'constraint_summary':{
            'active_wang_rows':len(added),
            'repr_count':{str(k):int(v) for k,v in sorted(repr_count.items())},
            'rows_by_dim8':{str(k):int(v) for k,v in sorted(by_dim.items())},
            'rows_by_L':{str(k):int(v) for k,v in sorted(by_L.items())},
            'direct_point_terms_total':int(direct_terms),
            'annihilator_weight_terms_total':int(ann_terms),
            'weight_variables':255,
            'weight_equalities':255,
            'contraction_lower_bounds':255,
        },
        'representation_examples':examples,
        'hint_added': bool(hint),
        'model_stats_final': model.ModelStats(),
        'rounds':rounds,
        'final_status': final_status or (rounds[-1]['solver_status'] if rounds else None),
        'interpretation':'Adaptive exact Wang separator in linked annihilator-weight representation. COMPLETE_WANG_FEASIBLE would still need fixed-A B/C completion; UNKNOWN/timeout is not a lower bound proof.',
        'elapsed_sec':round(time.time()-t0,3),
    }
    args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(args.out),'final_status':out['final_status'],'rounds':len(rounds),'active_rows':len(added),'elapsed_sec':out['elapsed_sec']},sort_keys=True))

if __name__=='__main__':
    main()
