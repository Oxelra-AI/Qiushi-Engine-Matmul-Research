#!/usr/bin/env python3
"""analysis cap-limited DRAT certificates for dim-2 orbit raises 484--491.

For each selected original Wang dim-2 orbit, reconstruct the induced quotient
occupation rows and keep only rows with cap <= the smallest cap threshold that
CP-SAT already found infeasible in a pilot (usually cap<=3, orbit 489 cap<=4).
Then extract a smaller CEGAR row subsystem, encode it as an occurrence-slot CNF,
and verify UNSAT with CaDiCaL + drat-trim.

A verified record proves the selected cap-limited row subsystem has no length-18
integer occupation solution.  It is therefore a proof object for that dim-2
raise once the row reconstruction from Wang's certified LUT is accepted.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

from ortools.sat.python import cp_model  # type: ignore
from pysat.card import CardEnc, EncType  # type: ignore
from pysat.formula import CNF  # type: ignore

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
import dim2_replay_compat_graph as dg  # type: ignore

OUTDIR = Path('data/dim2_caplimited_certs')
CAP_LIMITS = {484:3,485:3,486:3,487:3,488:3,489:4,490:3,491:3}


def sha256(path: Path) -> str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda:f.read(1<<20), b''):
            h.update(chunk)
    return h.hexdigest()


def row_hash(rows: Sequence[Tuple[int,int]]) -> str:
    return hashlib.sha256(';'.join(f'{int(m)}:{int(c)}' for m,c in rows).encode()).hexdigest()


def solve_int(rows: Sequence[Tuple[int,int]], k:int, L:int, sec:float, workers:int, log:bool=False) -> Dict:
    npts=(1<<k)-1
    model=cp_model.CpModel()
    xs=[model.NewIntVar(0,L,f'x_{i+1}') for i in range(npts)]
    model.Add(sum(xs)==L)
    for mask,cap in rows:
        if cap >= L or mask == 0:
            continue
        pts=[i for i in range(npts) if (mask>>i)&1]
        if cap < 0:
            model.Add(0<=-1)
        elif pts:
            model.Add(sum(xs[i] for i in pts) <= int(cap))
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(sec); solver.parameters.num_search_workers=int(workers); solver.parameters.random_seed=3400
    t0=time.time(); st=solver.Solve(model); elapsed=time.time()-t0
    rec={'status':solver.StatusName(st),'elapsed_sec':elapsed,'branches':int(solver.NumBranches()),'conflicts':int(solver.NumConflicts())}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol=[int(solver.Value(x)) for x in xs]
        rec.update({'feasible':True,'solution':sol,'nonzero':[(i+1,v) for i,v in enumerate(sol) if v]})
    elif st == cp_model.INFEASIBLE:
        rec.update({'feasible':False})
    else:
        rec.update({'feasible':None})
    return rec


def extract_core(rows: Sequence[Tuple[int,int]], k:int, L:int, add_per_round:int, max_rounds:int, sec:float, workers:int) -> Tuple[List[Tuple[int,int]], List[Dict], str]:
    active: List[Tuple[int,int]]=[]; aset=set(); rounds=[]
    # Seed rows of cap 0 and 1 first; these are usually strong and cheap.
    for m,c in rows:
        if c <= 1 and (m,c) not in aset:
            active.append((m,c)); aset.add((m,c))
    for rd in range(max_rounds):
        sol=solve_int(active,k,L,sec,workers)
        rec={'round':rd,'active_count':len(active),'solve':{kk:vv for kk,vv in sol.items() if kk!='solution'}}
        if sol.get('feasible') is False:
            rounds.append(rec); return active,rounds,'INFEASIBLE'
        if sol.get('feasible') is None:
            rounds.append(rec); return active,rounds,'UNKNOWN'
        xs=sol['solution']
        viol=[]; maxex=0
        for mask,cap in rows:
            occ=sum(xs[i] for i in range((1<<k)-1) if (mask>>i)&1)
            if occ>cap:
                ex=occ-cap; viol.append((mask,cap,ex,occ,mask.bit_count())); maxex=max(maxex,ex)
        rec['violation_count']=len(viol); rec['max_excess']=maxex
        if not viol:
            rounds.append(rec); return active,rounds,'FEASIBLE'
        viol.sort(key=lambda r:(-r[2], r[1], -r[4], r[0]))
        added=0
        for mask,cap,ex,occ,pop in viol:
            if (mask,cap) not in aset:
                active.append((int(mask),int(cap))); aset.add((int(mask),int(cap))); added += 1
                if added >= add_per_round: break
        rec['added']=added
        rounds.append(rec)
    return active,rounds,'MAX_ROUNDS'


def shrink_core(rows: List[Tuple[int,int]], k:int, L:int, sec:float, workers:int, max_passes:int=2) -> Tuple[List[Tuple[int,int]], List[Dict]]:
    cur=list(rows); events=[]
    for p in range(max_passes):
        removed=0; i=0
        while i < len(cur):
            trial=cur[:i]+cur[i+1:]
            sol=solve_int(trial,k,L,sec,workers)
            if sol.get('feasible') is False:
                ev={'pass':p,'removed_at':i,'removed_row':{'mask':cur[i][0],'cap':cur[i][1]},'remaining':len(trial),'solve':sol}
                events.append(ev); cur=trial; removed += 1
            else:
                i += 1
        if removed == 0:
            break
    return cur, events


def vid(s:int,p:int,npts:int)->int:
    return s*npts+p+1


def encode_cnf(rows: Sequence[Tuple[int,int]], k:int, L:int, path:Path) -> Dict:
    npts=(1<<k)-1; cnf=CNF(); top=L*npts
    stats={'slot_exactly_one_clauses':0,'row_constraints_encoded':0,'unit_forbidden_literals':0}
    for s in range(L):
        lits=[vid(s,p,npts) for p in range(npts)]
        cnf.append(lits); stats['slot_exactly_one_clauses'] += 1
        enc=CardEnc.atmost(lits=lits,bound=1,top_id=top,encoding=EncType.seqcounter)
        cnf.extend(enc.clauses); stats['slot_exactly_one_clauses'] += len(enc.clauses); top=enc.nv
    for mask,cap in rows:
        if cap >= L or mask == 0:
            continue
        lits=[]
        for s in range(L):
            base=s*npts+1
            for p in range(npts):
                if (mask>>p)&1:
                    lits.append(base+p)
        if cap < 0:
            cnf.append([]); stats['row_constraints_encoded'] += 1
        elif cap == 0:
            for lit in lits: cnf.append([-lit])
            stats['unit_forbidden_literals'] += len(lits); stats['row_constraints_encoded'] += 1
        elif cap < len(lits):
            enc=CardEnc.atmost(lits=lits,bound=int(cap),top_id=top,encoding=EncType.seqcounter)
            cnf.extend(enc.clauses); top=enc.nv; stats['row_constraints_encoded'] += 1
    path.parent.mkdir(parents=True,exist_ok=True); cnf.to_file(str(path))
    stats.update({'vars':cnf.nv,'clauses':len(cnf.clauses),'npts':npts,'slots':L,'path':str(path)})
    return stats


def run_cmd(args: List[str], timeout:int) -> Dict:
    t0=time.time()
    try:
        p=subprocess.run(args,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=timeout)
        return {'args':args,'returncode':p.returncode,'stdout_tail':p.stdout[-6000:],'stderr_tail':p.stderr[-6000:],'elapsed_sec':time.time()-t0,'timeout':False}
    except subprocess.TimeoutExpired as e:
        return {'args':args,'returncode':None,'stdout_tail':(e.stdout or '')[-6000:] if isinstance(e.stdout,str) else '', 'stderr_tail':(e.stderr or '')[-6000:] if isinstance(e.stderr,str) else '', 'elapsed_sec':time.time()-t0,'timeout':True}


def process(idx:int,args,lut,cache,raw,prof) -> Dict:
    rec_by_idx={int(r['index']):r for r in prof['dimension_2_orbits']}
    prec=rec_by_idx[idx]; W=[int(x) for x in prec['constraint_values']]; L=int(prec['rank_lower_bound']); k=9-len(dg.rref_basis(W,9))
    rows,meta=dg.node_rows(W,lut,cache,raw,L)
    caplim=args.cap_limit if args.cap_limit is not None else CAP_LIMITS[idx]
    rows_cap=[(m,c) for m,c in rows if c <= caplim]
    t0=time.time(); active,rounds,status=extract_core(rows_cap,k,L,args.add_per_round,args.max_rounds,args.core_sec,args.workers)
    shrunk=active; shrink_events=[]
    if status=='INFEASIBLE' and args.shrink:
        shrunk,shrink_events=shrink_core(active,k,L,args.shrink_sec,args.workers,args.shrink_passes)
    plain=solve_int(shrunk,k,L,args.core_sec,args.workers) if shrunk else None
    idxdir=args.outdir/f'orbit{idx}'; idxdir.mkdir(parents=True,exist_ok=True)
    core_path=idxdir/f'orbit{idx}_cap{caplim}_core.json'
    out={'schema':'s0908_dim2_caplimited_cert_v1','index':idx,'basis':W,'rank_pattern':[dg.rank3(x) for x in dg.nonzero_span(W)],'old_lb':L,'attempted_raise_to':L+1,'quotient_dim':k,'cap_limit':caplim,'all_row_count':len(rows),'caplimited_row_count':len(rows_cap),'all_row_meta':meta,'all_row_sha256':row_hash(rows),'caplimited_row_sha256':row_hash(rows_cap),'extract_status':status,'extract_rounds':rounds,'active_row_count':len(active),'shrunk_row_count':len(shrunk),'shrunk_row_sha256':row_hash(shrunk),'plain_shrunk_solve':plain,'shrink_removed_count':len(shrink_events),'shrink_events_head':shrink_events[:30],'shrunk_rows':[{'mask':m,'cap':c,'popcount':m.bit_count()} for m,c in shrunk],'elapsed_before_sat_sec':time.time()-t0}
    if args.cnf and plain and plain.get('feasible') is False:
        cnf_path=idxdir/f'orbit{idx}_cap{caplim}_core.cnf'; drat_path=idxdir/f'orbit{idx}_cap{caplim}_core.drat'; log_path=idxdir/f'orbit{idx}_cap{caplim}_proof_logs.json'
        cnfmeta=encode_cnf(shrunk,k,L,cnf_path); cnfmeta['sha256']=sha256(cnf_path)
        cad=run_cmd(['cadical',str(cnf_path),str(drat_path)],args.cadical_timeout)
        dr=None; verified=False
        if cad['returncode']==20 and drat_path.exists():
            dr=run_cmd(['drat-trim',str(cnf_path),str(drat_path)],args.drat_timeout)
            verified=(dr['returncode']==0 and 's VERIFIED' in dr['stdout_tail'])
        log_path.write_text(json.dumps({'cadical':cad,'drat_trim':dr},indent=2,sort_keys=True)+'\n')
        out.update({'cnf_meta':cnfmeta,'cnf_sha256':cnfmeta['sha256'],'drat_path':str(drat_path),'drat_sha256':sha256(drat_path) if drat_path.exists() else None,'cadical_returncode':cad['returncode'],'drat_returncode':None if dr is None else dr['returncode'],'drat_verified':verified,'proof_log_path':str(log_path)})
    out['elapsed_sec']=time.time()-t0
    core_path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    out['core_path']=str(core_path); out['core_sha256']=sha256(core_path)
    return out


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--indices',default='484,485,486,487,488,489,490,491'); ap.add_argument('--outdir',type=Path,default=OUTDIR); ap.add_argument('--cap-limit',type=int,default=None); ap.add_argument('--add-per-round',type=int,default=300); ap.add_argument('--max-rounds',type=int,default=80); ap.add_argument('--core-sec',type=float,default=10.0); ap.add_argument('--workers',type=int,default=8); ap.add_argument('--shrink',action='store_true'); ap.add_argument('--shrink-sec',type=float,default=5.0); ap.add_argument('--shrink-passes',type=int,default=1); ap.add_argument('--cnf',action='store_true'); ap.add_argument('--cadical-timeout',type=int,default=300); ap.add_argument('--drat-timeout',type=int,default=300); args=ap.parse_args(); args.outdir.mkdir(parents=True,exist_ok=True)
    lut,cache=dg.load_lut_cache(); raw=dg.orbit_lbs_from_cache(cache,{}); prof=json.loads(dg.PROFILE.read_text())
    records=[]
    for idx in [int(x) for x in args.indices.split(',') if x.strip()]:
        rec=process(idx,args,lut,cache,raw,prof)
        records.append({k:v for k,v in rec.items() if k not in ('shrunk_rows','all_row_meta','extract_rounds','shrink_events_head')})
        print('orbit',idx,'cap',rec['cap_limit'],'caprows',rec['caplimited_row_count'],'active',rec['active_row_count'],'shrunk',rec['shrunk_row_count'],'plain',None if rec['plain_shrunk_solve'] is None else rec['plain_shrunk_solve']['status'],'drat',rec.get('drat_verified'),'elapsed',rec['elapsed_sec'],flush=True)
    manifest={'schema':'s0908_dim2_caplimited_cert_manifest_v1','meaning':'Cap-limited occurrence-CNF DRAT certificate attempts for exactly the eight dim-2 orbit exclusions 484--491 needed by the shortened saturation route.','records':records,'summary':{'total':len(records),'extract_infeasible':[r['index'] for r in records if r['extract_status']=='INFEASIBLE'],'plain_infeasible':[r['index'] for r in records if r.get('plain_shrunk_solve',{}).get('feasible') is False],'drat_verified':[r['index'] for r in records if r.get('drat_verified') is True],'failed_drat':[r['index'] for r in records if r.get('drat_verified') is not True]}}
    mpath=args.outdir/'dim2_caplimited_cert_manifest.json'; mpath.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','manifest':str(mpath),'summary':manifest['summary']},indent=2,sort_keys=True))

if __name__=='__main__': main()
