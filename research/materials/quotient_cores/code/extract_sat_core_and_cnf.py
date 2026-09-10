#!/usr/bin/env python3
"""Extract a small CEGAR core for one analysis coset-H full-Wang system and encode it to CNF.

The compressed systems have 49 Boolean rank-one variables and many at-most
constraints.  This script repeatedly solves a small active subset, scans all
compressed constraints for violations, adds the first violated constraints, and
then emits a DIMACS CNF using PySAT cardinality encodings.  The CNF + DRAT route
is intended as independent proof support for the A-side coset exclusion.
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

from ortools.sat.python import cp_model  # type: ignore
from pysat.card import CardEnc, EncType  # type: ignore
from pysat.formula import CNF  # type: ignore

DEFAULT_CONSTRAINT = Path('data/coset_fullwang/H00_constraints.json')
OUTDIR = Path('data/coset_fullwang_cert')


def solve_active(active, nvars=49, target=16, sec=10.0):
    model=cp_model.CpModel(); x=[model.NewBoolVar(f'x{i}') for i in range(nvars)]
    model.Add(sum(x)==target)
    for idx in active:
        mask,rhs = idx
        inds=[i for i in range(nvars) if (mask>>i)&1]
        if rhs < 0:
            model.Add(0<=-1)
        elif inds and rhs < len(inds):
            model.Add(sum(x[i] for i in inds) <= rhs)
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(sec); solver.parameters.num_search_workers=8; solver.parameters.random_seed=933
    t0=time.time(); st=solver.Solve(model); elapsed=time.time()-t0; name=solver.StatusName(st)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol=0
        for i in range(nvars):
            if solver.Value(x[i]): sol |= 1<<i
        return {'status':name,'feasible':True,'solution_mask':sol,'elapsed_sec':elapsed,'conflicts':solver.NumConflicts(),'branches':solver.NumBranches()}
    if st == cp_model.INFEASIBLE:
        return {'status':name,'feasible':False,'elapsed_sec':elapsed,'conflicts':solver.NumConflicts(),'branches':solver.NumBranches()}
    return {'status':name,'feasible':None,'elapsed_sec':elapsed,'conflicts':solver.NumConflicts(),'branches':solver.NumBranches()}


def extract_core(cons, add_per_round=1000, max_rounds=100, sec=10.0):
    active=[]; active_set=set(); rounds=[]
    for rd in range(max_rounds):
        sol=solve_active(active, sec=sec)
        rec={'round':rd,'active_count':len(active),'solve':sol}
        if sol['feasible'] is False:
            rounds.append(rec); return active, rounds, 'INFEASIBLE'
        if sol['feasible'] is None:
            rounds.append(rec); return active, rounds, 'UNKNOWN'
        sm=int(sol['solution_mask'])
        viol=[]
        max_ex=0
        for m,rhs in cons:
            occ=(sm & m).bit_count()
            if occ > rhs:
                viol.append((m,rhs,occ-rhs))
                if occ-rhs > max_ex: max_ex=occ-rhs
        rec['violation_count']=len(viol); rec['max_excess']=max_ex
        if not viol:
            rounds.append(rec); return active, rounds, 'FEASIBLE_SUPPORT'
        # Add most violated first, then smaller RHS/larger support.
        viol.sort(key=lambda x:(-x[2], x[1], -x[0].bit_count(), x[0]))
        added=0
        for m,rhs,ex in viol:
            key=(m,rhs)
            if key not in active_set:
                active_set.add(key); active.append(key); added += 1
                if added >= add_per_round: break
        rec['added']=added
        rounds.append(rec)
    return active, rounds, 'MAX_ROUNDS'


def encode_cnf(active, cnf_path:Path, nvars=49, target=16):
    cnf=CNF(); top=nvars
    # exactly target: atmost target and atleast target via negated atmost n-target
    enc=CardEnc.atmost(lits=list(range(1,nvars+1)), bound=target, top_id=top, encoding=EncType.seqcounter)
    cnf.extend(enc.clauses); top=enc.nv
    enc=CardEnc.atmost(lits=[-(i+1) for i in range(nvars)], bound=nvars-target, top_id=top, encoding=EncType.seqcounter)
    cnf.extend(enc.clauses); top=enc.nv
    for mask,rhs in active:
        lits=[i+1 for i in range(nvars) if (mask>>i)&1]
        if rhs < 0:
            cnf.append([])
        elif rhs < len(lits):
            if rhs == 0:
                for lit in lits: cnf.append([-lit])
            else:
                enc=CardEnc.atmost(lits=lits, bound=int(rhs), top_id=top, encoding=EncType.seqcounter)
                cnf.extend(enc.clauses); top=enc.nv
    cnf.to_file(str(cnf_path))
    return {'vars':cnf.nv,'clauses':len(cnf.clauses)}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--constraints', type=Path, default=DEFAULT_CONSTRAINT)
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    ap.add_argument('--add-per-round', type=int, default=1000)
    ap.add_argument('--max-rounds', type=int, default=50)
    ap.add_argument('--solver-sec', type=float, default=10.0)
    args=ap.parse_args(); args.outdir.mkdir(parents=True,exist_ok=True)
    d=json.loads(args.constraints.read_text())
    cons=[(int(r['mask']), int(r['rhs'])) for r in d['constraints']]
    t0=time.time(); active, rounds, status = extract_core(cons,args.add_per_round,args.max_rounds,args.solver_sec)
    core_path=args.outdir/(args.constraints.stem+'_cegar_core.json')
    core={'schema':'s0908_cegar_core_v1','source_constraints':str(args.constraints),'status':status,'active_count':len(active),'active_constraints':[{'mask':m,'rhs':rhs} for m,rhs in active],'rounds':rounds,'elapsed_sec':time.time()-t0}
    core_path.write_text(json.dumps(core,indent=2,sort_keys=True)+'\n')
    cnf_meta=None
    if status == 'INFEASIBLE':
        cnf_path=args.outdir/(args.constraints.stem+'_cegar_core.cnf')
        cnf_meta=encode_cnf(active,cnf_path)
        cnf_meta['path']=str(cnf_path)
        core['cnf']=cnf_meta
        core_path.write_text(json.dumps(core,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','core_path':str(core_path),'final':status,'active_count':len(active),'rounds':len(rounds),'cnf':cnf_meta,'elapsed_sec':core['elapsed_sec']},indent=2,sort_keys=True))


if __name__=='__main__':
    main()
