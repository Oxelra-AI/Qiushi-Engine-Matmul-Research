#!/usr/bin/env python3
"""Encode a dim-2 occupation core by unary count variables and verify by DRAT.

The earlier occurrence-slot CNF is highly symmetric: it represents an integer
multiset of L quotient points as L labeled slots.  This script represents the
same nonnegative integer counts directly.  For each quotient point p and level
ell=1..L, variable u[p,ell] means x_p >= ell.  Monotonicity plus
sum_{p,ell} u[p,ell] = L gives an exact encoding of all integer counts
0 <= x_p <= L with total L.  A row occupation inequality becomes
sum_{p in row, ell} u[p,ell] <= cap(row).

This is much smaller and less symmetric, while remaining a plain CNF suitable
for CaDiCaL DRAT proof replay.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

from pysat.card import CardEnc, EncType  # type: ignore
from pysat.formula import CNF  # type: ignore


def sha256(path: Path) -> str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda:f.read(1<<20), b''):
            h.update(chunk)
    return h.hexdigest()


def run_cmd(args: List[str], timeout:int) -> Dict:
    t0=time.time()
    try:
        p=subprocess.run(args,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=timeout)
        return {'args':args,'returncode':p.returncode,'stdout_tail':p.stdout[-6000:],'stderr_tail':p.stderr[-6000:],'elapsed_sec':time.time()-t0,'timeout':False}
    except subprocess.TimeoutExpired as e:
        return {'args':args,'returncode':None,'stdout_tail':(e.stdout or '')[-6000:] if isinstance(e.stdout,str) else '', 'stderr_tail':(e.stderr or '')[-6000:] if isinstance(e.stderr,str) else '', 'elapsed_sec':time.time()-t0,'timeout':True}


def load_rows(core_json: Path) -> Tuple[List[Tuple[int,int]], int, int, Dict]:
    d=json.loads(core_json.read_text())
    L=int(d.get('old_lb', d.get('L',18)))
    k=int(d.get('quotient_dim', d.get('k',7)))
    row_key='shrunk_rows' if d.get('shrunk_rows') else 'selected_core_rows'
    if row_key not in d or not d[row_key]:
        raise SystemExit(f'No rows found in {core_json}')
    rows=[]
    for r in d[row_key]:
        rows.append((int(r['mask']), int(r['cap'])))
    meta={'source_core':str(core_json),'source_schema':d.get('schema'),'source_index':d.get('index'),'source_row_key':row_key,'source_row_count':len(rows),'source_row_sha256':hashlib.sha256(';'.join(f'{m}:{c}' for m,c in rows).encode()).hexdigest()}
    return rows,k,L,meta


def var_id(p:int, ell:int, L:int) -> int:
    # p 0..npts-1, ell 1..L
    return p*L + ell


def encode_unary(rows: Sequence[Tuple[int,int]], k:int, L:int, path:Path, encoding_name:str='seqcounter') -> Dict:
    enc_type = EncType.seqcounter if encoding_name == 'seqcounter' else EncType.totalizer
    npts=(1<<k)-1
    cnf=CNF(); top=npts*L
    stats={'monotonicity_clauses':0,'total_sum_clauses':0,'row_constraints_encoded':0,'unit_forbidden_literals':0,'row_constraints_skipped':0}
    # monotone u[p,ell+1] -> u[p,ell]
    for p in range(npts):
        for ell in range(1,L):
            cnf.append([-var_id(p,ell+1,L), var_id(p,ell,L)]); stats['monotonicity_clauses'] += 1
    all_lits=[var_id(p,ell,L) for p in range(npts) for ell in range(1,L+1)]
    enc=CardEnc.equals(lits=all_lits,bound=L,top_id=top,encoding=enc_type)
    cnf.extend(enc.clauses); stats['total_sum_clauses'] += len(enc.clauses); top=enc.nv
    for mask,cap in rows:
        if cap >= L or mask == 0:
            stats['row_constraints_skipped'] += 1; continue
        lits=[]
        for p in range(npts):
            if (mask>>p)&1:
                for ell in range(1,L+1):
                    lits.append(var_id(p,ell,L))
        if cap < 0:
            cnf.append([]); stats['row_constraints_encoded'] += 1
        elif cap == 0:
            for lit in lits:
                cnf.append([-lit])
            stats['unit_forbidden_literals'] += len(lits); stats['row_constraints_encoded'] += 1
        else:
            enc=CardEnc.atmost(lits=lits,bound=int(cap),top_id=top,encoding=enc_type)
            cnf.extend(enc.clauses); top=enc.nv; stats['row_constraints_encoded'] += 1
    path.parent.mkdir(parents=True,exist_ok=True)
    cnf.to_file(str(path))
    stats.update({'vars':cnf.nv,'clauses':len(cnf.clauses),'npts':npts,'levels':L,'count_variables':npts*L,'path':str(path),'encoding':encoding_name})
    return stats


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--core-json',type=Path,required=True)
    ap.add_argument('--outdir',type=Path,required=True)
    ap.add_argument('--name',default=None)
    ap.add_argument('--encoding',choices=['seqcounter','totalizer'],default='seqcounter')
    ap.add_argument('--solve',action='store_true')
    ap.add_argument('--cadical-timeout',type=int,default=300)
    ap.add_argument('--drat-timeout',type=int,default=300)
    args=ap.parse_args(); args.outdir.mkdir(parents=True,exist_ok=True)
    rows,k,L,meta=load_rows(args.core_json)
    stem=args.name or f"orbit{meta.get('source_index','x')}_unary_core"
    cnf_path=args.outdir/f'{stem}.cnf'; drat_path=args.outdir/f'{stem}.drat'; log_path=args.outdir/f'{stem}_proof_log.json'; meta_path=args.outdir/f'{stem}_meta.json'
    t0=time.time(); enc=encode_unary(rows,k,L,cnf_path,args.encoding); enc['sha256']=sha256(cnf_path); enc['elapsed_encode_sec']=time.time()-t0
    cad=dr=None; verified=False
    if args.solve:
        cad=run_cmd(['cadical',str(cnf_path),str(drat_path)],args.cadical_timeout)
        if cad['returncode']==20 and drat_path.exists():
            dr=run_cmd(['drat-trim',str(cnf_path),str(drat_path)],args.drat_timeout)
            verified=(dr['returncode']==0 and 's VERIFIED' in dr['stdout_tail'])
    if drat_path.exists():
        drat_sha=sha256(drat_path)
    else:
        drat_sha=None
    out={'schema':'s0908_unary_count_cnf_v1','meaning':'Unary-count CNF encoding of an integer occupation core. DRAT verification proves no nonnegative integer count vector of total L satisfies the selected row inequalities.','source':meta,'k':k,'L':L,'row_count':len(rows),'cnf_meta':enc,'cnf_path':str(cnf_path),'cnf_sha256':enc['sha256'],'drat_path':str(drat_path),'drat_sha256':drat_sha,'cadical_returncode':None if cad is None else cad['returncode'],'drat_returncode':None if dr is None else dr['returncode'],'drat_verified':verified,'elapsed_sec':time.time()-t0}
    meta_path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    log_path.write_text(json.dumps({'cadical':cad,'drat_trim':dr},indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','meta':str(meta_path),'cnf':str(cnf_path),'vars':enc['vars'],'clauses':enc['clauses'],'cadical':out['cadical_returncode'],'drat':out['drat_returncode'],'verified':verified,'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__': main()
