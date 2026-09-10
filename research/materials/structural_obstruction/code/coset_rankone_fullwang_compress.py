#!/usr/bin/env python3
"""analysis independent full-Wang compression for the surviving coset profile.

Structural reduction leaves, up to normalization and transpose, four high-rank
A-directions H in the canonical rank-2 lower-block coset, with profile one
rank-2 plus three rank-3, and sixteen further rank-one A-directions.  This
script does not use the peer's 43-variable prefilter.  It allows all 49 rank-one
A-directions as Boolean variables and compresses the complete full-Wang length-20
row table restricted to H plus these variables:

    |selected rank-one variables in row| <= cap(row) - |H intersect row|.

Together with sum x = 16, infeasibility excludes that H at the A-occupation
level.  CP-SAT status is solver evidence; the compressed constraint list is the
object to feed a proof-producing SAT/PB encoding later.
"""
from __future__ import annotations

import argparse
import json
import struct
import time
from collections import Counter
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:
    cp_model = None

MAGIC = b'WANG512\x01'
FULL_ROWS = Path('data/wang_native/full_tensor/full_wang512_cap19_len20_all_dim9_allbinding.bin')
OUTDIR = Path('data/coset_fullwang')


def gf2_rank_rows(rows: Sequence[int]) -> int:
    basis: List[int] = []
    for x0 in rows:
        x = int(x0)
        for b in basis:
            p = b.bit_length()-1
            if (x>>p)&1:
                x ^= b
        if not x:
            continue
        p = x.bit_length()-1
        for i,b in enumerate(basis):
            if (b>>p)&1:
                basis[i] = b ^ x
        basis.append(x); basis.sort(key=lambda z:z.bit_length(), reverse=True)
    return len(basis)


def mat_rank(x:int)->int:
    rows=[sum(((int(x)>>(3*i+j))&1)<<j for j in range(3)) for i in range(3)]
    return gf2_rank_rows(rows)


def outer_mask(u:int,v:int)->int:
    z=0
    for i in range(3):
        if (u>>i)&1:
            for j in range(3):
                if (v>>j)&1:
                    z |= 1 << (3*i+j)
    return z


def rank_one_points()->List[int]:
    pts=sorted({outer_mask(u,v) for u in range(1,8) for v in range(1,8)})
    assert len(pts)==49
    return pts


def canonical_Hs()->List[List[int]]:
    p=(1<<4)|(1<<8)
    rank2=[p|r for r in range(8) if mat_rank(p|r)==2]
    rank3=[p|r for r in range(8) if mat_rank(p|r)==3]
    Hs=[sorted(list(c2)+list(c3)) for c2 in combinations(rank2,1) for c3 in combinations(rank3,3)]
    Hs=sorted(Hs, key=lambda H: sorted([x^p for x in H]))
    assert len(Hs)==16
    return Hs


def rowmask_from_words(words: Tuple[int,...])->int:
    z=0
    for i,w in enumerate(words):
        z |= int(w) << (64*i)
    return z


def iter_rows(path:Path):
    with path.open('rb') as f:
        magic=f.read(8)
        if magic != MAGIC:
            raise ValueError(f'bad magic {magic!r}')
        n=struct.unpack('<I', f.read(4))[0]
        for idx in range(n):
            cap, dim, _ = struct.unpack('<BBH', f.read(4))
            words=struct.unpack('<8Q', f.read(64))
            yield idx, int(cap), int(dim), rowmask_from_words(words)


def compress_for_H(H: Sequence[int], full_rows: Path, max_store_examples:int=20):
    r1=rank_one_points(); var_index={x:i for i,x in enumerate(r1)}
    H_mask=sum(1<<int(h) for h in H)
    constraints: Dict[int,int] = {}
    row_count=0; active_count=0; trivial_count=0; impossible_rows=[]
    cap_hist=Counter(); rhs_hist=Counter(); dim_hist=Counter(); pop_hist=Counter(); h_occ_hist=Counter()
    for idx,cap,dim,rowmask in iter_rows(full_rows):
        row_count += 1
        h_occ=(rowmask & H_mask).bit_count()
        rhs=cap-h_occ
        vmask=0
        for x,i in var_index.items():
            if (rowmask>>x)&1:
                vmask |= 1<<i
        pop=vmask.bit_count()
        if rhs < 0:
            impossible_rows.append({'idx':idx,'cap':cap,'dim':dim,'h_occ':h_occ,'rhs':rhs,'var_pop':pop,'rowmask':rowmask})
            if len(impossible_rows) >= max_store_examples:
                # Still continue to count? If H alone impossible, enough, but this should not happen.
                pass
        if pop == 0 or rhs >= pop:
            trivial_count += 1
            continue
        active_count += 1
        if vmask not in constraints or rhs < constraints[vmask]:
            constraints[vmask] = rhs
        cap_hist[cap]+=1; rhs_hist[rhs]+=1; dim_hist[dim]+=1; pop_hist[pop]+=1; h_occ_hist[h_occ]+=1
    cons=sorted([(m,c) for m,c in constraints.items()], key=lambda mc:(mc[1],mc[0].bit_count(),mc[0]))
    return cons, {
        'full_row_count': row_count,
        'active_nontrivial_row_count_before_dedup': active_count,
        'trivial_or_empty_row_count': trivial_count,
        'unique_constraint_count': len(cons),
        'impossible_row_count': len(impossible_rows),
        'impossible_rows_head': impossible_rows[:max_store_examples],
        'cap_hist_active': {str(k):int(v) for k,v in sorted(cap_hist.items())},
        'rhs_hist_active': {str(k):int(v) for k,v in sorted(rhs_hist.items())},
        'dim_hist_active': {str(k):int(v) for k,v in sorted(dim_hist.items())},
        'var_pop_hist_active': {str(k):int(v) for k,v in sorted(pop_hist.items())},
        'H_occ_hist_active': {str(k):int(v) for k,v in sorted(h_occ_hist.items())},
    }


def solve_constraints(cons: Sequence[Tuple[int,int]], nvars:int=49, target:int=16, sec:float=30.0):
    if cp_model is None:
        return {'status':'NO_ORTOOLS','feasible':None}
    model=cp_model.CpModel(); x=[model.NewBoolVar(f'x{i}') for i in range(nvars)]
    model.Add(sum(x)==target)
    for mask,rhs in cons:
        if rhs < 0:
            model.Add(0<=-1)
        elif rhs < mask.bit_count():
            inds=[i for i in range(nvars) if (mask>>i)&1]
            if inds:
                model.Add(sum(x[i] for i in inds) <= int(rhs))
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(sec); solver.parameters.num_search_workers=8; solver.parameters.random_seed=9033
    t0=time.time(); st=solver.Solve(model); elapsed=time.time()-t0; name=solver.StatusName(st)
    rec={'status':name,'elapsed_sec':elapsed,'conflicts':int(solver.NumConflicts()),'branches':int(solver.NumBranches())}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol=[i for i in range(nvars) if solver.Value(x[i])]
        rec.update({'feasible':True,'solution_indices':sol})
    elif st == cp_model.INFEASIBLE:
        rec.update({'feasible':False})
    else:
        rec.update({'feasible':None})
    return rec


def write_opb(path: Path, cons: Sequence[Tuple[int,int]], nvars:int=49, target:int=16):
    # Simple OPB for proof-producing pseudo-Boolean solvers if available.
    with path.open('w') as f:
        f.write(f'* analysis coset H compressed full-Wang constraints; {nvars} variables\n')
        f.write(f'* #variable= {nvars} #constraint= {len(cons)+2}\n')
        f.write(' '.join(f'+1 x{i+1}' for i in range(nvars)) + f' = {target} ;\n')
        f.write(' '.join(f'+1 ~x{i+1}' for i in range(nvars)) + f' = {nvars-target} ;\n')
        for mask,rhs in cons:
            if rhs < 0:
                f.write(' >= 1 ;\n')
                continue
            if rhs >= mask.bit_count():
                continue
            terms=[f'+1 x{i+1}' for i in range(nvars) if (mask>>i)&1]
            if terms:
                f.write(' '.join(terms) + f' <= {int(rhs)} ;\n')


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--h', default='all', help='H index or all')
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    ap.add_argument('--full-rows', type=Path, default=FULL_ROWS)
    ap.add_argument('--solver-sec', type=float, default=30.0)
    ap.add_argument('--write-opb', action='store_true')
    args=ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    Hs=canonical_Hs(); r1=rank_one_points(); indices=list(range(len(Hs))) if args.h=='all' else [int(args.h)]
    out={'schema':'s0908_coset_rankone_fullwang_compress_v1','meaning':'Independent all-49-rank-one-variable compression of complete full-Wang rows for each surviving normalized high-rank coset H; UNSAT is solver evidence unless accompanied by a proof certificate.', 'full_rows':str(args.full_rows), 'rank_one_points':r1, 'records':[], 'started_at':time.time()}
    for hi in indices:
        t0=time.time(); H=Hs[hi]
        cons, meta=compress_for_H(H,args.full_rows)
        sol=solve_constraints(cons,49,16,args.solver_sec)
        rec={'h_index':hi,'H':H,'H_firstrows':[int(x ^ ((1<<4)|(1<<8))) for x in H], 'H_rank_hist':{str(k):int(v) for k,v in Counter(mat_rank(x) for x in H).items()}, 'compression':meta, 'solve':sol, 'elapsed_sec':time.time()-t0}
        if args.write_opb:
            opb=args.outdir/f'H{hi:02d}_fullwang49.opb'
            write_opb(opb,cons,49,16)
            rec['opb_path']=str(opb)
        (args.outdir/f'H{hi:02d}_constraints.json').write_text(json.dumps({'H':H,'rank_one_points':r1,'constraints':[{'mask':m,'rhs':c} for m,c in cons]},indent=2,sort_keys=True)+'\n')
        out['records'].append(rec)
        print('H',hi,'constraints',len(cons),'status',sol['status'],'elapsed',rec['elapsed_sec'], flush=True)
    out['summary']={'total':len(out['records']),'feasible':[r['h_index'] for r in out['records'] if r['solve'].get('feasible') is True], 'infeasible':[r['h_index'] for r in out['records'] if r['solve'].get('feasible') is False], 'unknown':[r['h_index'] for r in out['records'] if r['solve'].get('feasible') is None]}
    out['elapsed_sec']=time.time()-out['started_at']
    opath=args.outdir/'coset_rankone_fullwang_compress.json'
    opath.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(opath),'summary':out['summary'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))


if __name__=='__main__':
    main()
