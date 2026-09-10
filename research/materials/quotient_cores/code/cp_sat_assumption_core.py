#!/usr/bin/env python3
"""Try CP-SAT assumption-core extraction for quotient branch closure.

This is a proof-facing experiment, not a theorem: OR-Tools cores are useful row
selection data but not independently checkable proof certificates.  We encode
rank-2 branch 1 with every Wang row guarded by an assumption literal and ask for
an UNSAT core.  If successful, export the rows in the core as a compact binary
for exact DFS/SAT replay.
"""
from __future__ import annotations
import argparse, json, struct, hashlib, time
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model

ROOT=Path('research/research_record')
OUTDIR=ROOT/'workspace/data/quotient_lift/sat'
OUTDIR.mkdir(parents=True,exist_ok=True)


def sha(path:Path):
    h=hashlib.sha256();
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()


def read_rows(path:Path, max_cap:int):
    data=path.read_bytes()
    if data[:8]!=b'E11WANG1': raise ValueError('bad magic')
    n=struct.unpack('<I',data[8:12])[0]
    rows=[]; cap_hist=Counter(); dim_hist=Counter(); skipped=Counter()
    for i in range(n):
        rec=data[12+36*i:12+36*(i+1)]
        cap=rec[0]; dim=rec[1]
        if cap>max_cap: continue
        words=struct.unpack('<4Q',rec[4:36]); mask=0
        for j,w in enumerate(words): mask |= int(w)<<(64*j)
        pts=[p for p in range(1,256) if (mask>>p)&1]
        if len(pts)<=cap:
            skipped['tautological']+=1; continue
        rows.append({'index':i,'cap':cap,'dim':dim,'mask':mask,'pts':pts,'raw':rec.hex()})
        cap_hist[cap]+=1; dim_hist[dim]+=1
    return rows, {'source_count':n,'rows':len(rows),'cap_hist':dict(sorted(cap_hist.items())),'dim_hist':dict(sorted(dim_hist.items())),'skipped':dict(skipped)}


def write_rows(path:Path, rowrecs):
    with path.open('wb') as f:
        f.write(b'E11WANG1'); f.write(struct.pack('<I',len(rowrecs)))
        for r in rowrecs: f.write(bytes.fromhex(r['raw']))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--rows',type=Path,default=Path('data/wang_native/quotient_binaries/rank2_all_n19.bin'))
    ap.add_argument('--max-cap',type=int,default=5)
    ap.add_argument('--branch',type=int,default=1)
    ap.add_argument('--force',default='2')
    ap.add_argument('--forbid',default='1,3,9')
    ap.add_argument('--time-limit',type=float,default=300)
    ap.add_argument('--label',default='rank2_branch1_cap5_assumption_core')
    args=ap.parse_args(); t0=time.time()
    rows,stats=read_rows(args.rows,args.max_cap)
    force=[int(x) for x in args.force.split(',') if x.strip()]
    forbid=[int(x) for x in args.forbid.split(',') if x.strip()]
    model=cp_model.CpModel(); x={p:model.NewBoolVar(f'x_{p}') for p in range(1,256)}
    model.Add(sum(x.values())==19)
    for p in force: model.Add(x[p]==1)
    for p in forbid: model.Add(x[p]==0)
    assumps=[]; lit_to_row=[]
    for j,r in enumerate(rows):
        a=model.NewBoolVar(f'a_{j}')
        model.Add(sum(x[p] for p in r['pts']) <= int(r['cap'])).OnlyEnforceIf(a)
        assumps.append(a); lit_to_row.append(r)
    try:
        model.AddAssumptions(assumps)
    except AttributeError:
        for a in assumps: model.AddAssumption(a)
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(args.time_limit); solver.parameters.num_search_workers=8
    st=solver.Solve(model); status=solver.StatusName(st)
    out={'schema':'s0908_cp_sat_assumption_core_v1','meaning':'OR-Tools CP-SAT assumption core for row selection only; not an independently replayable proof.','rows_path':str(args.rows),'rows_sha256':sha(args.rows),'max_cap':args.max_cap,'branch':args.branch,'force':force,'forbid':forbid,'load_stats':stats,'status':status,'elapsed_sec':time.time()-t0,'solver_wall_time':solver.WallTime(),'conflicts':solver.NumConflicts(),'branches':solver.NumBranches()}
    core_rows=[]
    if status=='INFEASIBLE':
        core=solver.SufficientAssumptionsForInfeasibility()
        # Depending on OR-Tools version this may return literal indices or BoolVars.
        index_by_lit={a.Index():i for i,a in enumerate(assumps)}
        for lit in core:
            idx = index_by_lit.get(int(lit), None)
            if idx is not None: core_rows.append(lit_to_row[idx])
        out['core_literal_count']=len(core); out['mapped_core_row_count']=len(core_rows)
        out['core_cap_hist']=dict(sorted(Counter(r['cap'] for r in core_rows).items()))
        out['core_dim_hist']=dict(sorted(Counter(r['dim'] for r in core_rows).items()))
        out['core_source_indices']=[r['index'] for r in core_rows]
        if core_rows:
            binp=OUTDIR/f'{args.label}_core_rows.bin'; write_rows(binp,core_rows)
            out['core_rows_binary']=str(binp); out['core_rows_binary_sha256']=sha(binp)
    path=OUTDIR/f'{args.label}.json'; path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(path),'status':status,'mapped_core_row_count':out.get('mapped_core_row_count'),'core_binary':out.get('core_rows_binary'),'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__': main()
