#!/usr/bin/env python3
"""analysis: independent original-LUT replay of dim-2 occupation raises.

This is separated from the dim3-overlay compatibility replay because the peer
asked specifically for the original-LUT dim-2 raises 479 and 484--491.  For each
selected dim-2 Wang orbit W with old lower bound L, construct all quotient
occupation rows from the canonical Wang LUT only and solve the length-L integer
occupation problem.  INFEASIBLE means the occupation layer alone raises the node
from L to L+1; it is still a CP-SAT result here, not a checked proof certificate.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from pathlib import Path

SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0,str(SCRIPT_DIR))

import dim2_replay_compat_graph as dg  # type: ignore

PROFILE=dg.PROFILE
OUTDIR=Path('data/dim2_compat')


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--indices',default='479,484,485,486,487,488,489,490,491')
    ap.add_argument('--time-limit',type=float,default=120.0)
    ap.add_argument('--workers',type=int,default=8)
    ap.add_argument('--out',type=Path,default=OUTDIR/'original_lut_dim2_raises.json')
    args=ap.parse_args()
    idxs={int(x) for x in args.indices.split(',') if x.strip()}
    lut,cache=dg.load_lut_cache()
    raw_lbs=dg.orbit_lbs_from_cache(cache,{})
    prof=json.loads(PROFILE.read_text())
    records=[]; t0=time.time()
    for rec in prof['dimension_2_orbits']:
        idx=int(rec['index'])
        if idx not in idxs:
            continue
        W=[int(x) for x in rec['constraint_values']]
        L=int(rec['rank_lower_bound'])
        rows,meta=dg.node_rows(W,lut,cache,raw_lbs,L)
        sol=dg.solve_cp(rows,9-len(dg.rref_basis(W,9)),L,args.time_limit,args.workers)
        row_hash_input=';'.join(f'{m}:{c}' for m,c in rows)
        import hashlib
        records.append({'index':idx,'basis':W,'rank_pattern':[dg.rank3(x) for x in dg.nonzero_span(W)],'old_lb':L,'attempted_raise_to':L+1,'row_count':len(rows),'row_meta':meta,'row_sha256':hashlib.sha256(row_hash_input.encode()).hexdigest(),'solve':sol,'raises_by_original_lut':sol.get('feasible') is False})
        print('orig-lut idx',idx,'rows',len(rows),'cap_hist',meta['cap_hist'],'status',sol.get('status'),'feasible',sol.get('feasible'),flush=True)
    out={'schema':'s0908_original_lut_dim2_raises_v1','meaning':'Original Wang LUT dim-2 occupation raise replay with no dim-3 overlay. INFEASIBLE is CP-SAT evidence pending certificate/replay formalization.','indices':sorted(idxs),'records':records,'summary':{'raised':[r['index'] for r in records if r['raises_by_original_lut']],'not_raised':[r['index'] for r in records if r['solve'].get('feasible') is True],'unknown':[r['index'] for r in records if r['solve'].get('feasible') is None]},'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(args.out),'summary':out['summary'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__':
    main()
