#!/usr/bin/env python3
"""Proof-producing replay for the original-LUT dim-2 occupation raises.

For selected Wang dim-2 orbit indices (default 479 and 484--491), reconstruct
the original-LUT quotient occupation rows exactly as in analysis.  The integer
occupation problem is:

    x_q >= 0,  sum_q x_q = L,  sum_{q in row} x_q <= cap(row)

where L is the old node lower bound being tested.  Infeasibility raises the node
from L to L+1 at the occupation level.  This script first extracts a small CEGAR
core using CP-SAT integer variables, then encodes that core to a SAT formula with
L occurrence slots.  A satisfying assignment chooses one quotient point per slot;
row constraints count the chosen slots lying in each row.  CaDiCaL produces a
DRAT proof and drat-trim replays it.

The result certifies the SAT encoding of the extracted row subsystem.  The
mathematical correspondence to the Wang row table and the structural reduction
remain explicit premises recorded in the manifest.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import List, Sequence, Tuple

from ortools.sat.python import cp_model  # type: ignore
from pysat.card import CardEnc, EncType  # type: ignore
from pysat.formula import CNF  # type: ignore

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
import dim2_replay_compat_graph as dg  # type: ignore

OUTDIR = Path('data/dim2_raise_certs')


def sha256(path: Path) -> str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda:f.read(1<<20), b''):
            h.update(chunk)
    return h.hexdigest()


def solve_active(rows: Sequence[Tuple[int,int]], k:int, L:int, sec:float):
    model=cp_model.CpModel(); npts=(1<<k)-1
    xs=[model.NewIntVar(0,L,f'x_{q+1}') for q in range(npts)]
    model.Add(sum(xs)==L)
    for mask,cap in rows:
        if cap < 0:
            model.Add(0<=-1)
        elif cap < L:
            pts=[i for i in range(npts) if (mask>>i)&1]
            if pts:
                model.Add(sum(xs[i] for i in pts) <= int(cap))
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(sec); solver.parameters.num_search_workers=8; solver.parameters.random_seed=9033
    t0=time.time(); st=solver.Solve(model); elapsed=time.time()-t0; name=solver.StatusName(st)
    rec={'status':name,'elapsed_sec':elapsed,'conflicts':int(solver.NumConflicts()),'branches':int(solver.NumBranches())}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol=[int(solver.Value(x)) for x in xs]
        rec.update({'feasible':True,'solution':sol,'nonzero':[(i+1,v) for i,v in enumerate(sol) if v]})
    elif st == cp_model.INFEASIBLE:
        rec.update({'feasible':False})
    else:
        rec.update({'feasible':None})
    return rec


def extract_core(all_rows: Sequence[Tuple[int,int]], k:int, L:int, add_per_round:int, max_rounds:int, sec:float):
    active=[]; aset=set(); rounds=[]
    for rd in range(max_rounds):
        sol=solve_active(active,k,L,sec)
        rec={'round':rd,'active_count':len(active),'solve':{kk:vv for kk,vv in sol.items() if kk!='solution'}}
        if sol['feasible'] is False:
            rounds.append(rec); return active, rounds, 'INFEASIBLE'
        if sol['feasible'] is None:
            rounds.append(rec); return active, rounds, 'UNKNOWN'
        xs=sol['solution']
        viol=[]; max_ex=0
        for mask,cap in all_rows:
            occ=sum(xs[i] for i in range((1<<k)-1) if (mask>>i)&1)
            if occ > cap:
                ex=occ-cap; viol.append((mask,cap,ex,occ)); max_ex=max(max_ex,ex)
        rec['violation_count']=len(viol); rec['max_excess']=max_ex
        if not viol:
            rounds.append(rec); return active, rounds, 'FEASIBLE'
        viol.sort(key=lambda r:(-r[2], r[1], -r[0].bit_count(), r[0]))
        added=0
        for mask,cap,ex,occ in viol:
            key=(int(mask),int(cap))
            if key not in aset:
                aset.add(key); active.append(key); added += 1
                if added >= add_per_round: break
        rec['added']=added
        rounds.append(rec)
    return active, rounds, 'MAX_ROUNDS'


def var_id(slot:int, point:int, npts:int)->int:
    # slot 0..L-1, point 0..npts-1
    return slot*npts + point + 1


def encode_occurrence_cnf(active: Sequence[Tuple[int,int]], k:int, L:int, cnf_path:Path):
    npts=(1<<k)-1; cnf=CNF(); top=L*npts
    # Each slot chooses exactly one quotient point.
    for s in range(L):
        lits=[var_id(s,p,npts) for p in range(npts)]
        cnf.append(lits)  # at least one
        enc=CardEnc.atmost(lits=lits,bound=1,top_id=top,encoding=EncType.seqcounter)
        cnf.extend(enc.clauses); top=enc.nv
    for mask,cap in active:
        lits=[]
        for s in range(L):
            for p in range(npts):
                if (mask>>p)&1:
                    lits.append(var_id(s,p,npts))
        if cap < 0:
            cnf.append([])
        elif cap == 0:
            for lit in lits: cnf.append([-lit])
        elif cap < len(lits):
            enc=CardEnc.atmost(lits=lits,bound=int(cap),top_id=top,encoding=EncType.seqcounter)
            cnf.extend(enc.clauses); top=enc.nv
    cnf.to_file(str(cnf_path))
    return {'vars':cnf.nv,'clauses':len(cnf.clauses),'npts':npts,'slots':L}


def run_cmd(args: List[str], timeout:int):
    t0=time.time(); p=subprocess.run(args,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=timeout)
    return {'args':args,'returncode':p.returncode,'stdout_tail':p.stdout[-4000:],'stderr_tail':p.stderr[-4000:],'elapsed_sec':time.time()-t0}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--indices', default='479,484,485,486,487,488,489,490,491')
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    ap.add_argument('--add-per-round', type=int, default=500)
    ap.add_argument('--max-rounds', type=int, default=50)
    ap.add_argument('--core-solver-sec', type=float, default=10.0)
    ap.add_argument('--cadical-timeout', type=int, default=300)
    ap.add_argument('--drat-timeout', type=int, default=300)
    args=ap.parse_args(); args.outdir.mkdir(parents=True,exist_ok=True)
    idxs=[int(x) for x in args.indices.split(',') if x.strip()]
    lut,cache=dg.load_lut_cache(); raw_lbs=dg.orbit_lbs_from_cache(cache,{})
    profile=json.loads(dg.PROFILE.read_text())
    rec_by_idx={int(r['index']):r for r in profile['dimension_2_orbits']}
    records=[]; t0=time.time()
    for idx in idxs:
        start=time.time(); prec=rec_by_idx[idx]; W=[int(x) for x in prec['constraint_values']]; L=int(prec['rank_lower_bound']); k=9-len(dg.rref_basis(W,9))
        rows,meta=dg.node_rows(W,lut,cache,raw_lbs,L)
        active,rounds,status=extract_core(rows,k,L,args.add_per_round,args.max_rounds,args.core_solver_sec)
        rec={'index':idx,'basis':W,'rank_pattern':[dg.rank3(x) for x in dg.nonzero_span(W)],'old_lb':L,'attempted_raise_to':L+1,'quotient_dim':k,'row_count':len(rows),'row_meta':meta,'core_status':status,'active_count':len(active),'rounds':rounds,'elapsed_core_sec':time.time()-start}
        core_path=args.outdir/f'orbit{idx}_core.json'; cnf_path=args.outdir/f'orbit{idx}_core.cnf'; drat_path=args.outdir/f'orbit{idx}_core.drat'; log_path=args.outdir/f'orbit{idx}_proof_logs.json'
        core={'schema':'s0908_dim2_raise_core_v1','index':idx,'basis':W,'old_lb':L,'quotient_dim':k,'status':status,'active_constraints':[{'mask':m,'cap':c} for m,c in active],'rounds':rounds,'row_meta':meta}
        core_path.write_text(json.dumps(core,indent=2,sort_keys=True)+'\n')
        rec['core_path']=str(core_path); rec['core_sha256']=sha256(core_path)
        if status == 'INFEASIBLE':
            cnf_meta=encode_occurrence_cnf(active,k,L,cnf_path)
            rec['cnf_meta']=cnf_meta; rec['cnf_path']=str(cnf_path); rec['cnf_sha256']=sha256(cnf_path)
            cad=run_cmd(['cadical',str(cnf_path),str(drat_path)],args.cadical_timeout)
            rec['cadical_returncode']=cad['returncode']
            rec['drat_path']=str(drat_path); rec['drat_sha256']=sha256(drat_path) if drat_path.exists() else None
            dr=None
            if cad['returncode'] == 20 and drat_path.exists():
                dr=run_cmd(['drat-trim',str(cnf_path),str(drat_path)],args.drat_timeout)
                rec['drat_returncode']=dr['returncode']; rec['drat_verified']='s VERIFIED' in dr['stdout_tail']
            else:
                rec['drat_returncode']=None; rec['drat_verified']=False
            rec['verified']=bool(cad['returncode']==20 and rec.get('drat_returncode')==0 and rec.get('drat_verified'))
            log_path.write_text(json.dumps({'cadical':cad,'drat_trim':dr},indent=2,sort_keys=True)+'\n')
            rec['log_path']=str(log_path)
        else:
            rec['verified']=False
        rec['elapsed_sec']=time.time()-start
        records.append(rec)
        print('orbit',idx,'active',len(active),'core',status,'verified',rec.get('verified'),'elapsed',rec['elapsed_sec'],flush=True)
    manifest={'schema':'s0908_original_dim2_raise_drat_manifest_v1','meaning':'DRAT replay manifest for original-LUT dim-2 occupation raises 479 and 484--491 encoded as occurrence-slot CNF. Certifies the extracted row subsystems; source row generation and reduction premises remain recorded separately.','records':records,'summary':{'total':len(records),'verified':[r['index'] for r in records if r.get('verified')], 'failed':[r['index'] for r in records if not r.get('verified')]},'elapsed_sec':time.time()-t0}
    mpath=args.outdir/'original_dim2_raise_drat_manifest.json'
    mpath.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','manifest':str(mpath),'summary':manifest['summary'],'elapsed_sec':manifest['elapsed_sec']},indent=2,sort_keys=True))


if __name__=='__main__':
    main()
