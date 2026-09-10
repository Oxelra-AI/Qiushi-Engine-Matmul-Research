#!/usr/bin/env python3
"""Filtered proof-producing CNF for pure rank-1 Wang occupation constraints.

The full rank-1 projection contains 149,444 compressed rows.  analysis CP-SAT
ablation found that the rows whose rank-1 intersection has size <= 13 already
make exact size 20 impossible.  This script encodes such a filtered row family
as a compact DIMACS formula with only direct forbidden-subset clauses (plus the
global exactly-20 sequential counter and E11 unit).  A DRAT-verified UNSAT run
is a small proof object for excluding the pure rank-1 branch, because the
encoded rows are a subset of the full Wang occupation system.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import List, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_capacity_profile import load_or_build  # noqa: E402


def sha256(path: Path) -> str | None:
    if not path.exists() or not path.is_file():
        return None
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(4 * 1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def write_cnf(pts: List[int], cons: List[Tuple[int,int,int]], rank_s: int, fixed_point: int,
              cnf: Path, meta: Path, max_intersection_size: int, include_groups: set[tuple[int,int]] | None = None) -> dict:
    from pysat.card import CardEnc, EncType
    t0=time.time(); var={p:i+1 for i,p in enumerate(pts)}; top=len(pts); clauses=[]
    enc=CardEnc.equals(lits=list(var.values()), bound=rank_s, top_id=top, encoding=EncType.seqcounter)
    clauses.extend(enc.clauses); top=enc.nv
    if fixed_point in var: clauses.append([var[fixed_point]])
    else: clauses.append([])
    selected=[]; hist=Counter(); direct=0; witness=[]
    for mask,cap,key in cons:
        size=mask.bit_count()
        if include_groups is not None:
            if (size,cap) not in include_groups: continue
        elif size > max_intersection_size:
            continue
        if size <= cap: continue
        selected.append((mask,cap,key)); hist[(size,cap)]+=1
        lits=[i+1 for i in range(len(pts)) if (mask>>i)&1]
        ncomb=math.comb(len(lits),cap+1)
        direct += ncomb
        for comb in itertools.combinations(lits,cap+1):
            clauses.append([-v for v in comb])
        if len(witness)<200:
            witness.append({'size':size,'cap':cap,'key':key,'dim':key&0xF,'clauses':ncomb})
    cnf.parent.mkdir(parents=True,exist_ok=True)
    with cnf.open('w') as f:
        f.write(f'p cnf {top} {len(clauses)}\n')
        for cl in clauses:
            f.write(' '.join(map(str,cl))+' 0\n')
    payload={'problem':'filtered pure rank-1 T-level Wang occupation CNF','field':'F2','rank_s':rank_s,'fixed_point':fixed_point,'rank1_points':pts,'filter':{'max_intersection_size':max_intersection_size,'include_groups':None if include_groups is None else sorted([list(g) for g in include_groups])},'selected_constraint_count':len(selected),'selected_constraint_hist':{f'{a},{b}':c for (a,b),c in sorted(hist.items())},'num_vars':top,'num_clauses':len(clauses),'global_cardinality_clauses':len(enc.clauses),'direct_capacity_clauses':direct,'witness_keys_head':witness,'cnf_path':str(cnf),'meaning':'UNSAT proves the pure rank-1 branch impossible using only this subset of Wang-projected rows; SAT/UNKNOWN is not an admissible support statement.','elapsed_sec':time.time()-t0}
    meta.parent.mkdir(parents=True,exist_ok=True); meta.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:payload[k] for k in ['selected_constraint_count','selected_constraint_hist','num_vars','num_clauses','direct_capacity_clauses','elapsed_sec']},indent=2,sort_keys=True))
    return payload


def run(cnf: Path, meta: Path, timeout: int):
    stem=cnf.stem; drat=cnf.with_suffix('.drat'); cadlog=cnf.with_suffix('.cadical.log'); trimlog=cnf.with_suffix('.drat_trim.log'); status=cnf.with_suffix('.status.json')
    cmd=['cadical','--unsat','--binary=false','-n']
    if timeout>0: cmd.extend(['-t',str(timeout)])
    cmd.extend([str(cnf),str(drat)])
    t0=time.time()
    with cadlog.open('w') as f:
        p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,text=True)
    res={'cnf':str(cnf),'meta':str(meta),'drat':str(drat),'cadical_log':str(cadlog),'drat_trim_log':str(trimlog),'cadical_exit':p.returncode,'cadical_elapsed_sec':time.time()-t0}
    if p.returncode==20:
        t1=time.time()
        with trimlog.open('w') as f:
            tr=subprocess.run(['drat-trim',str(cnf),str(drat)],stdout=f,stderr=subprocess.STDOUT,text=True)
        res['drat_trim_exit']=tr.returncode; res['drat_trim_elapsed_sec']=time.time()-t1
    else:
        res['drat_trim_exit']=None
    res['hashes']={str(p):sha256(p) for p in [cnf,meta,drat,cadlog,trimlog] if p.exists()}
    status.write_text(json.dumps(res,indent=2,sort_keys=True)+'\n')
    print(json.dumps(res,indent=2,sort_keys=True))


def parse_groups(s: str):
    if not s.strip(): return None
    out=set()
    for part in s.split(','):
        part=part.strip()
        if not part: continue
        if ':' in part: a,b=part.split(':')
        else: a,b=part.split('/')
        out.add((int(a),int(b)))
    return out


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')); ap.add_argument('--cache',type=Path,default=Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl')); ap.add_argument('--rank',type=int,default=20); ap.add_argument('--fixed-point',type=int,default=1); ap.add_argument('--max-intersection-size',type=int,default=13); ap.add_argument('--include-groups',default=''); ap.add_argument('--cnf',type=Path,required=True); ap.add_argument('--meta',type=Path,required=True); ap.add_argument('--solve',action='store_true'); ap.add_argument('--solver-time',type=int,default=0); args=ap.parse_args()
    pts,cons,cmeta,lmeta=load_or_build(args.cache,args.lut,args.rank,False)
    write_cnf(pts,cons,args.rank,args.fixed_point,args.cnf,args.meta,args.max_intersection_size,parse_groups(args.include_groups))
    if args.solve: run(args.cnf,args.meta,args.solver_time)

if __name__=='__main__': main()
