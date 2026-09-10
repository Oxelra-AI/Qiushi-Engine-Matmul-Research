#!/usr/bin/env python3
"""analysis extension: local hull membership for flags selected by a global LP solution.

The first analysis run tested 4D flags coming from pairs of old near-miss
violations. This script uses the saved complete-Wang fractional LP point and
selects 4D local color models from pairs of active global Wang constraints. This
is a more direct test of whether a fractional LP vertex is cut by a small shared
projection integer hull.
"""
from __future__ import annotations
import json, sys, time
from pathlib import Path
from itertools import combinations
from collections import defaultdict
import numpy as np

SCRIPTS=Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0,str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints
from wang_capacity_lazy import rref_basis, subspace_points_from_basis, unpack_basis
from fractional_local_membership import (
    dot2, intersection_basis, annihilator_basis, eval_color,
    build_local_constraints, local_matrix, LocalHullOracle,
    convex_membership_column_generation,
)

ROOT=Path('research/research_record')
OUTDIR=ROOT/'workspace/data/local_hull'
LUT_PATH=ROOT/'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl'
GLOBAL_PATH=OUTDIR/'global_fractional_solution.json'


def selected_active_pairs(records, x, max_pairs=8):
    # Compute exact slacks by direct bitset dot with x to avoid rebuilding sparse matrix.
    active=[]
    for idx,r in enumerate(records):
        cap=19-int(r['L'])
        bs=int(r['point_bitset'])
        lhs=0.0
        tmp=bs
        while tmp:
            bit=tmp & -tmp
            lhs += x[bit.bit_length()-1]
            tmp ^= bit
        slack=cap-lhs
        if abs(slack) < 1e-7 and int(r['dim8']) in (5,6):
            active.append({'row_index':idx,'key8':int(r['key8']),'dim8':int(r['dim8']),'L':int(r['L']),'cap':cap,'slack':slack,'basis8':list(unpack_basis(int(r['key8'])))})
    print('active dim5/6 rows',len(active))
    # Pair rows with 4D intersection; diversify by rank type and key of the intersection.
    candidates=[]; seenF=set()
    for a,b in combinations(active,2):
        inter=intersection_basis(a['basis8'], b['basis8'])
        if len(inter)!=4: continue
        Fkey=tuple(inter)
        if Fkey in seenF: continue
        seenF.add(Fkey)
        # Prefer pairs whose rows are both tight and low cap / high L; all are tight, sort by caps.
        score=(a['cap']+b['cap'], -(a['L']+b['L']), abs(a['dim8']-b['dim8']), a['row_index']+b['row_index'])
        candidates.append({'score':score,'rows':[a,b],'intersection_basis':inter})
    candidates.sort(key=lambda c:c['score'])
    return active, candidates[:max_pairs]


def main():
    t0=time.time(); OUTDIR.mkdir(parents=True, exist_ok=True)
    global_data=json.loads(GLOBAL_PATH.read_text())
    x=np.array(global_data['global_lp']['x_full'],dtype=float)
    lut,_=load_lut(LUT_PATH)
    core=CoreQuotient(1)
    records,_=build_core_constraints(core,lut)
    rec_by_key={int(r['key8']):r for r in records}
    active,pairs=selected_active_pairs(records,x,max_pairs=8)
    print('selected active pairs',len(pairs))
    pair_results=[]
    for pi,cand in enumerate(pairs):
        inter=cand['intersection_basis']
        ann=annihilator_basis(inter)
        constraints=build_local_constraints(ann, rec_by_key)
        oracle=LocalHullOracle(constraints)
        target=np.zeros(16)
        for p in range(1,256):
            target[eval_color(p,ann)] += x[p-1]
        A,b=local_matrix(constraints)
        slacks=b-A.dot(target)
        print(f"pair {pi}: rows={[r['row_index'] for r in cand['rows']]} dims={[r['dim8'] for r in cand['rows']]} L={[r['L'] for r in cand['rows']]} minslack={slacks.min():.3e} tight={np.sum(np.abs(slacks)<1e-7)}")
        cg=convex_membership_column_generation(target, oracle, max_iters=80)
        print('  status',cg['status'],'profiles',cg['final_profile_count'])
        hist=defaultdict(int)
        for con in constraints:
            hist[f"L{int(con['L'])}_cap{int(con['cap'])}"]+=1
        pair_results.append({
            'pair_index':pi,
            'selection':'active_global_rows_dim5_or_dim6_intersection_dim4',
            'active_rows':[{k:r[k] for k in ('row_index','key8','dim8','L','cap')} for r in cand['rows']],
            'score':list(cand['score']),
            'intersection_basis':inter,
            'annihilator_basis':ann,
            'target_profile':[float(v) for v in target],
            'target_sum':float(target.sum()),
            'target_min_local_slack':float(slacks.min()),
            'target_tight_local_constraints':int(np.sum(np.abs(slacks)<1e-7)),
            'local_constraint_L_cap_hist':dict(sorted(hist.items())),
            'hull_test':cg,
        })
    out=OUTDIR/'active_fractional_local_membership.json'
    out.write_text(json.dumps({
        'schema':'active_fractional_local_membership_v1',
        'elapsed_sec':time.time()-t0,
        'meaning':'Projection of the saved complete-Wang LP fractional point to 4D local color models selected from pairs of active global Wang constraints. Membership/separation statuses are projection-specific.',
        'global_solution_file':str(GLOBAL_PATH),
        'active_dim5_dim6_row_count':len(active),
        'selected_pair_count':len(pair_results),
        'pair_results':pair_results,
    },indent=2)+"\n")
    print('saved',out,'elapsed',time.time()-t0)
if __name__=='__main__': main()
