#!/usr/bin/env python3
"""analysis: CEGAR for high-rank A-factor patterns under full Wang rows.

This strengthens the simultaneous dim-2 compatibility graph without introducing
B/C assumptions.  Variables are the 462 nonzero 3x3 matrices of rank >= 2;
vertex weight is rank(a)-1.  The model includes the independently replayed
(original-LUT) dim-2 raises 479 and 484--491 as pair exclusions.  It then
maximizes total high-rank excess and scans each candidate against the full
length-20 Wang row binary, considering only the selected high-rank points.  Any
violated row is added as a high-rank-only cut.  If a candidate of weight >=7
passes all scanned full Wang rows, the A-side high-rank pattern survives this
necessary test; if the optimized weight falls below 7 under a fully justified cut
set, the split-flattening rank-20 case would close (modulo proof certificates).

The run is exploratory/repairable unless converted into a replayable certificate.
"""
from __future__ import annotations

import argparse
import json
import pickle
import struct
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:
    cp_model = None

SCRIPT=Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0,str(SCRIPT))
import dim2_replay_compat_graph as dg  # type: ignore

MAGIC=b'WANG512\x01'
DEFAULT_BINARY=Path('data/wang_native/full_tensor/full_wang512_cap19_len20_all_dim9_allbinding.bin')
DEFAULT_ORIG_RAISES=Path('data/dim2_compat/original_lut_dim2_raises.json')
OUT=Path('data/highrank/highrank_wang_cegar.json')


def rowmask_from_words(words):
    z=0
    for i,w in enumerate(words): z |= int(w) << (64*i)
    return z


def iter_rows(path:Path):
    with open(path,'rb') as f:
        magic=f.read(8)
        if magic!=MAGIC: raise ValueError(f'bad magic {magic!r}')
        n=struct.unpack('<I',f.read(4))[0]
        for idx in range(n):
            cap,dim,_=struct.unpack('<BBH',f.read(4))
            words=struct.unpack('<8Q',f.read(64))
            yield idx,int(cap),int(dim),rowmask_from_words(words)


def load_original_raised_indices(path:Path)->set[int]:
    d=json.loads(path.read_text())
    return {int(r['index']) for r in d['records'] if r.get('raises_by_original_lut')}


def pair_orbit(a:int,b:int,cache)->int:
    return dg.pair_orbit(a,b,cache)


def scan(binary:Path, selected:Sequence[int], add_per_round:int):
    smask=0
    for p in selected: smask |= 1<<int(p)
    viol=[]; count=0; dimhist=Counter(); caphist=Counter(); maxex=0; rows=0
    t0=time.time()
    for idx,cap,dim,rowmask in iter_rows(binary):
        rows+=1
        occ=(rowmask & smask).bit_count()
        if occ>cap:
            ex=occ-cap; count+=1; maxex=max(maxex,ex); dimhist[dim]+=1; caphist[cap]+=1
            if len(viol)<add_per_round:
                viol.append({'row_index':idx,'cap':cap,'dim':dim,'occ':occ,'excess':ex,'row_mask':int(rowmask),'selected_in_row':[int(p) for p in selected if (rowmask>>int(p))&1]})
    return {'rows_checked':rows,'violation_count':count,'max_excess':maxex,'violation_dim_hist':{str(k):int(v) for k,v in sorted(dimhist.items())},'violation_cap_hist':{str(k):int(v) for k,v in sorted(caphist.items())},'violations':viol,'elapsed_sec':time.time()-t0}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--binary',type=Path,default=DEFAULT_BINARY)
    ap.add_argument('--orig-raises',type=Path,default=DEFAULT_ORIG_RAISES)
    ap.add_argument('--max-rounds',type=int,default=20)
    ap.add_argument('--solver-sec',type=float,default=60.0)
    ap.add_argument('--add-per-round',type=int,default=200)
    ap.add_argument('--workers',type=int,default=8)
    ap.add_argument('--out',type=Path,default=OUT)
    args=ap.parse_args()
    if cp_model is None: raise RuntimeError('ortools unavailable')
    lut,cache=dg.load_lut_cache()
    raised_dim2=load_original_raised_indices(args.orig_raises)
    vertices=[v for v in range(1,512) if dg.rank3(v)>=2]
    weights={v:dg.rank3(v)-1 for v in vertices}
    idx={v:i for i,v in enumerate(vertices)}
    model=cp_model.CpModel()
    x={v:model.NewBoolVar(f'x_{v}') for v in vertices}
    pair_cuts=0; pair_orbit_hist=Counter()
    for ii,a in enumerate(vertices):
        for b in vertices[ii+1:]:
            pos=pair_orbit(a,b,cache)
            if pos in raised_dim2:
                model.Add(x[a]+x[b] <= 1)
                pair_cuts+=1; pair_orbit_hist[pos]+=1
    model.Maximize(sum(weights[v]*x[v] for v in vertices))
    rounds=[]; cut_count=pair_cuts; t0=time.time(); final='MAX_ROUNDS'
    for rd in range(args.max_rounds):
        solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(args.solver_sec); solver.parameters.num_search_workers=int(args.workers); solver.parameters.random_seed=903200+rd
        st=solver.Solve(model); name=solver.StatusName(st)
        rec={'round':rd,'solve_status':name,'cuts_total':cut_count,'pair_cuts':pair_cuts}
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            final='CP_'+name; rounds.append(rec); break
        selected=[v for v in vertices if solver.Value(x[v])]
        wt=sum(weights[v] for v in selected)
        rec.update({'objective_weight':int(wt),'selected_count':len(selected),'rank_hist':{str(k):int(c) for k,c in sorted(Counter(dg.rank3(v) for v in selected).items())},'selected':selected,'selected_hex':[hex(v) for v in selected]})
        sc=scan(args.binary,selected,args.add_per_round)
        rec['scan_summary']={k:v for k,v in sc.items() if k!='violations'}
        if sc['violation_count']==0:
            final='FULL_WANG_HIGH_RANK_PATTERN'
            rounds.append(rec); break
        added=0
        for vr in sc['violations']:
            pts=[v for v in vertices if (int(vr['row_mask'])>>v)&1]
            rhs=int(vr['cap'])
            if rhs<0:
                model.Add(0<=-1); added+=1
            elif pts and rhs < len(pts):
                model.Add(sum(x[v] for v in pts) <= rhs); added+=1
        cut_count += added; rec['cuts_added_now']=added
        rounds.append(rec)
        print('round',rd,'weight',wt,'count',len(selected),'rankhist',rec['rank_hist'],'viol',sc['violation_count'],'maxex',sc['max_excess'],'add',added,flush=True)
        if wt<7:
            final='MAX_WEIGHT_BELOW_7_UNDER_ADDED_CUTS'
            break
    out={'schema':'s0908_highrank_wang_cegar_v1','meaning':'High-rank A-factor excess maximization under original dim2 raises plus CEGAR-added full Wang rows. Passing candidate is a necessary-pattern survivor; failure/timeout is not a theorem without proof traces.','parameters':{'binary':str(args.binary),'orig_raises':str(args.orig_raises),'max_rounds':args.max_rounds,'solver_sec':args.solver_sec,'add_per_round':args.add_per_round},'raised_dim2_indices':sorted(raised_dim2),'pair_cuts':pair_cuts,'pair_cut_orbit_hist':{str(k):int(v) for k,v in sorted(pair_orbit_hist.items())},'final_status':final,'rounds':rounds,'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(args.out),'final_status':final,'rounds':len(rounds),'last':{k:rounds[-1].get(k) for k in ['solve_status','objective_weight','selected_count','rank_hist','scan_summary']} if rounds else None,'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__': main()
