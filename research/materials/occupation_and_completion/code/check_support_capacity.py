#!/usr/bin/env python3
"""Check a selected A-factor support against Wang T-level or core capacity constraints.

Input JSON formats accepted:
  * wang_capacity_mip.py output with nonzero_solution
  * branch MIP/lazy outputs with solution
  * raw list of integer masks or {mask: multiplicity}
The script scans the full Wang LUT (T-level, n=9) and reports violations by
dimension/LB. It is a regression and scientific-inspection tool, not a solver.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from wang_capacity_lazy import unpack_basis, in_rowspace, matrix_rank_of_mask


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def extract_solution(path: Path, iteration=None) -> Dict[int,int]:
    data = json.loads(path.read_text())
    if isinstance(data, list):
        return {int(p): 1 for p in data}
    if 'nonzero_solution' in data:
        return {int(k): int(v) for k,v in data['nonzero_solution'].items() if int(v)}
    if 'solution' in data and data['solution'] is not None:
        return {int(k): int(v) for k,v in data['solution'].items() if int(v)}
    if 'support_dict' in data and data['support_dict'] is not None:
        return {int(k): int(v) for k,v in data['support_dict'].items() if int(v)}
    if 'support' in data and data['support'] is not None:
        if isinstance(data['support'], list):
            return {int(p): 1 for p in data['support']}
        if isinstance(data['support'], dict):
            return {int(k): int(v) for k,v in data['support'].items() if int(v)}
    if 'iterations' in data:
        iters = data['iterations']
        if iteration is None:
            cand = [e for e in iters if 'solution' in e]
            if not cand:
                raise ValueError('No solution in iterations')
            entry = cand[-1]
        else:
            entry = next(e for e in iters if e.get('iteration') == iteration and 'solution' in e)
        return {int(k): int(v) for k,v in entry['solution'].items() if int(v)}
    raise ValueError(f'No recognized solution in {path}')


def check(lut, sol, s, max_report=200):
    t0=time.time()
    support=list(sol.items())
    violations=[]
    occ_by_dim=Counter(); occ_by_dim_lb=Counter(); seen_by_dim=Counter(); seen_by_lb=Counter()
    worst_by_dim={}
    for key, lb in lut.items():
        basis=unpack_basis(key)
        occ=0
        for p,m in support:
            if in_rowspace(p,basis,n=9):
                occ += m
        dim=key & 0xF
        cap=s-lb
        seen_by_dim[dim]+=1; seen_by_lb[lb]+=1
        if occ>cap:
            v={"key":key,"dim":dim,"basis":list(basis),"lb":lb,"cap":cap,"occupancy":occ,"excess":occ-cap}
            violations.append(v)
            occ_by_dim[dim]+=1; occ_by_dim_lb[(dim,lb)]+=1
            old=worst_by_dim.get(dim)
            if old is None or (v['excess'],v['lb'],v['occupancy'])>(old['excess'],old['lb'],old['occupancy']):
                worst_by_dim[dim]=v
    violations.sort(key=lambda v:(v['excess'],v['lb'],v['occupancy'],-v['dim']), reverse=True)
    support_ranks=Counter(matrix_rank_of_mask(p) for p,m in support for _ in range(m))
    return {
        'elapsed_sec':time.time()-t0,
        'total_multiplicity':sum(sol.values()),
        'support_size':len(sol),
        'support':{str(k):v for k,v in sorted(sol.items())},
        'support_rank_hist':dict(support_ranks),
        'violation_count':len(violations),
        'violations_by_dim':dict(occ_by_dim),
        'violations_by_dim_lb':{f'{d},{lb}':c for (d,lb),c in sorted(occ_by_dim_lb.items())},
        'seen_by_dim':dict(seen_by_dim),
        'seen_by_lb':dict(seen_by_lb),
        'max_excess':max((v['excess'] for v in violations), default=0),
        'worst_by_dim':{str(d):v for d,v in sorted(worst_by_dim.items())},
        'violations_head':violations[:max_report],
    }


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('solution_json', type=Path)
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--iteration', type=int, default=None)
    ap.add_argument('--max-report', type=int, default=200)
    ap.add_argument('--out', type=Path, default=None)
    args=ap.parse_args()
    lut,meta=load_lut(args.lut)
    sol=extract_solution(args.solution_json,args.iteration)
    print(f'Loaded support size={len(sol)} total={sum(sol.values())} from {args.solution_json}')
    res=check(lut,sol,args.rank,args.max_report)
    res['source_solution_json']=str(args.solution_json)
    res['rank_s']=args.rank
    res['lut_meta_brief']={'coverage_ok':meta.get('coverage_ok'),'conflict_count':meta.get('conflict_count'),'subspace_count':meta.get('subspace_count')}
    brief={k:res[k] for k in ['elapsed_sec','total_multiplicity','support_size','support_rank_hist','violation_count','violations_by_dim','violations_by_dim_lb','max_excess']}
    print(json.dumps(brief,indent=2,sort_keys=True))
    if args.out:
        args.out.parent.mkdir(parents=True,exist_ok=True)
        args.out.write_text(json.dumps(res,indent=2,sort_keys=True)+'\n')
        print('saved',args.out)

if __name__=='__main__':
    main()
