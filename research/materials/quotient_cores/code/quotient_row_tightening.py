#!/usr/bin/env python3
"""Bottom-up local tightening tests for quotient Wang rows.

For each quotient row U with current cap c, test whether selecting c+1 points
inside U can satisfy all strict lower-dimensional child rows V<=U using the
native quotient Wang capacities.  If infeasible, then U can be tightened to cap
c.  Since we test exactly the already-stated cap, these runs mostly validate the
local closure mechanism; the reusable output identifies small OR-Tools cores or
SAT-hard rows.  A stronger use is to start from a deliberately weaker cap and
see which cap is forced by children.

The script is scoped to a filtered candidate set so it does not try to certify
hundreds of thousands of rows in one ARTIFACT.
"""
from __future__ import annotations
import argparse, json, struct, time, hashlib
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model

ROOT=Path('research/research_record')
OUTDIR=ROOT/'workspace/data/quotient_lift/tightening'
OUTDIR.mkdir(parents=True,exist_ok=True)
ROWS={'rank2':Path('data/wang_native/quotient_binaries/rank2_all_n19.bin'),
      'rank3':Path('data/wang_native/quotient_binaries/rank3_all_n19.bin')}
MAGIC=b'E11WANG1'; REC='<BBHQQQQ'; SZ=struct.calcsize(REC)


def sha(path:Path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()


def load_rows(path:Path):
    d=path.read_bytes(); assert d[:8]==MAGIC
    n=struct.unpack('<I',d[8:12])[0]; rows=[]; hist=Counter()
    for i in range(n):
        cap,dim,pad,w0,w1,w2,w3=struct.unpack(REC,d[12+i*SZ:12+(i+1)*SZ])
        mask=int(w0)|(int(w1)<<64)|(int(w2)<<128)|(int(w3)<<192)
        rows.append({'idx':i,'cap':int(cap),'dim':int(dim),'mask':mask,'pop':mask.bit_count()})
        hist[(int(dim),int(cap))]+=1
    return rows,{'count':n,'sha256':sha(path),'dim_cap_hist':{f'{d}:{c}':int(v) for (d,c),v in sorted(hist.items())}}


def pts(mask:int): return [i for i in range(1,256) if (mask>>i)&1]


def solve_inside(row, child_rows, target_occ:int, time_limit:float):
    Upts=pts(row['mask']); pos={p:i for i,p in enumerate(Upts)}
    model=cp_model.CpModel(); x=[model.NewBoolVar(f'x_{p}') for p in Upts]
    model.Add(sum(x)==target_occ)
    used=0; child_dim_hist=Counter(); child_cap_hist=Counter()
    for r in child_rows:
        inter=r['mask'] & row['mask']
        if inter==0 or inter==row['mask']: continue
        if inter != r['mask']: continue  # only true child rows V<=U
        # Child constraints with cap >= target_occ are irrelevant.
        if r['cap']>=target_occ: continue
        ps=[pos[p] for p in pts(r['mask'])]
        if len(ps)<=r['cap']: continue
        model.Add(sum(x[i] for i in ps) <= r['cap'])
        used+=1; child_dim_hist[r['dim']]+=1; child_cap_hist[r['cap']]+=1
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(time_limit); solver.parameters.num_search_workers=8
    t0=time.time(); st=solver.Solve(model); status=solver.StatusName(st)
    out={'status':status,'wall_time':solver.WallTime(),'elapsed_sec':time.time()-t0,'children_used':used,'child_dim_hist':dict(sorted(child_dim_hist.items())),'child_cap_hist':dict(sorted(child_cap_hist.items())),'branches':solver.NumBranches(),'conflicts':solver.NumConflicts()}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE): out['witness_points']=[Upts[i] for i in range(len(Upts)) if solver.Value(x[i])]
    return out


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--pivot',choices=['rank2','rank3'],required=True); ap.add_argument('--dim',type=int,required=True); ap.add_argument('--cap',type=int,required=True); ap.add_argument('--target-occ',type=int,default=0,help='occupancy to test; default cap+1 verifies current cap, cap tests one-ARTIFACT tightening'); ap.add_argument('--limit',type=int,default=50); ap.add_argument('--time-per-row',type=float,default=10); ap.add_argument('--label',default='')
    args=ap.parse_args(); t0=time.time(); rows,meta=load_rows(ROWS[args.pivot])
    candidates=[r for r in rows if r['dim']==args.dim and r['cap']==args.cap]
    # Prefer rows with small point sets? Within fixed dim all same pop; use native order for reproducibility.
    candidates=candidates[:args.limit]
    results=[]; hist=Counter()
    target_occ=args.target_occ or (args.cap+1)
    for j,r in enumerate(candidates):
        res=solve_inside(r,rows,target_occ,args.time_per_row)
        rr={'row_idx':r['idx'],'dim':r['dim'],'cap':r['cap'],'pop':r['pop'],'target_occ':target_occ,'result':res}
        results.append(rr); hist[res['status']]+=1
        print(j, 'idx',r['idx'],'target',target_occ,'status',res['status'],'children',res['children_used'],'time',res['elapsed_sec'],flush=True)
    out={'schema':'s0908_quotient_local_tightening_v1','meaning':'For selected quotient rows U, tests whether a requested number of points inside U is possible using strict child Wang rows V<=U. target_occ=cap+1 verifies the current cap from children; target_occ=cap tests one-ARTIFACT tightening. UNSAT at target_occ=cap would indicate a possible local cap decrease, but still needs proof-chain replay.','pivot':args.pivot,'rows_path':str(ROWS[args.pivot]),'rows_meta':meta,'dim':args.dim,'cap':args.cap,'target_occ':target_occ,'limit':args.limit,'time_per_row':args.time_per_row,'status_hist':dict(sorted(hist.items())),'results':results,'elapsed_sec':time.time()-t0}
    lab=args.label or f'{args.pivot}_dim{args.dim}_cap{args.cap}_first{args.limit}'
    p=OUTDIR/f'{lab}.json'; p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(p),'status_hist':out['status_hist'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))
if __name__=='__main__': main()
