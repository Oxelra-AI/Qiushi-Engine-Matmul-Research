#!/usr/bin/env python3
"""
analysis: proof-producing pure-CNF replay for the Z4 x cyclic F2 subfamily.

Imports the native-XOR encoder from z4_cyclic_sat_f2.py, then expands every
XOR equation into Tseitin CNF so Kissat can emit a DRAT proof.  This is slower than
CryptoMiniSat, but gives a replayable certificate for UNSAT patterns.
"""
from __future__ import annotations
import argparse, json, os, subprocess, time
from pathlib import Path

import z4_cyclic_sat_f2 as z4

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / 'data' / 'z4_cyclic_f2_drat'


def add_xor_assert(clauses, next_var, terms, target):
    terms=[t for t in terms if t]
    if not terms:
        if target & 1:
            clauses.append(())
        return next_var
    if len(terms)==1:
        clauses.append((terms[0] if (target&1) else -terms[0],))
        return next_var
    acc=terms[0]
    for t in terms[1:-1]:
        s=next_var; next_var += 1
        # s <-> acc xor t
        clauses.append((-acc, -t, -s))
        clauses.append(( acc,  t, -s))
        clauses.append(( acc, -t,  s))
        clauses.append((-acc,  t,  s))
        acc=s
    last=terms[-1]
    if target & 1:
        # acc xor last = 1
        clauses.append(( acc,  last))
        clauses.append((-acc, -last))
    else:
        # acc xor last = 0
        clauses.append(( acc, -last))
        clauses.append((-acc,  last))
    return next_var


def write_pure_cnf(enc, path):
    clauses=list(enc.reg)
    next_var=enc.nv+1
    for target,terms in enc.xors:
        next_var=add_xor_assert(clauses,next_var,terms,target)
    nv=next_var-1
    with open(path,'w') as f:
        f.write(f'p cnf {nv} {len(clauses)}\n')
        for cl in clauses:
            f.write(' '.join(map(str,cl))+' 0\n')
    return nv,len(clauses)


def run_kissat(cnf, proof, timeout):
    t0=time.time()
    try:
        r=subprocess.run(['kissat',str(cnf),str(proof)],capture_output=True,text=True,timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT',time.time()-t0,'',''
    if r.returncode==20:
        return 'UNSAT',time.time()-t0,r.stdout,r.stderr
    if r.returncode==10:
        return 'SAT',time.time()-t0,r.stdout,r.stderr
    return f'RC{r.returncode}',time.time()-t0,r.stdout,r.stderr


def verify_drat(cnf, proof, timeout):
    if not proof.exists():
        return 'NO_PROOF',0.0,''
    t0=time.time()
    try:
        r=subprocess.run(['drat-trim',str(cnf),str(proof)],capture_output=True,text=True,timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT',time.time()-t0,''
    out=r.stdout+r.stderr
    if 'VERIFIED' in out:
        return 'VERIFIED',time.time()-t0,out[-2000:]
    return f'RC{r.returncode}',time.time()-t0,out[-2000:]


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--patterns',default='selected')
    ap.add_argument('--timeout',type=int,default=600)
    ap.add_argument('--verify-timeout',type=int,default=600)
    ap.add_argument('--require-nonzero',action='store_true')
    args=ap.parse_args()
    OUT.mkdir(parents=True,exist_ok=True)
    pats=z4.parse_patterns(args.patterns)
    results=[]
    print('DRAT replay patterns',pats,'require_nonzero',args.require_nonzero)
    for pat in pats:
        tag='p'+'_'.join(map(str,pat)) if pat else 'p0'
        print('\n',tag,pat)
        t0=time.time(); enc,_=z4.encode(pat,sym_break=True,require_nonzero=args.require_nonzero); enc_sec=time.time()-t0
        cnf=OUT/f'z4_cyclic_tseitin_{tag}.cnf'
        proof=OUT/f'z4_cyclic_tseitin_{tag}.drat'
        nv,nc=write_pure_cnf(enc,cnf)
        print('  cnf',nv,'vars',nc,'clauses','native vars',enc.nv,'reg',len(enc.reg),'xors',len(enc.xors),'enc',round(enc_sec,3))
        status,sec,stdout,stderr=run_kissat(cnf,proof,args.timeout)
        print(' ',status,round(sec,2),'s')
        rec={'pattern':pat,'tag':tag,'vars':nv,'clauses':nc,'native_vars':enc.nv,
             'regular_clauses':len(enc.reg),'xor_equations':len(enc.xors),'encode_sec':round(enc_sec,3),
             'status':status,'solve_sec':round(sec,3),'cnf':str(cnf),'proof':str(proof)}
        if status=='UNSAT':
            vst,vt,vout=verify_drat(cnf,proof,args.verify_timeout)
            rec['drat_status']=vst; rec['drat_verify_sec']=round(vt,3); rec['proof_bytes']=proof.stat().st_size if proof.exists() else 0
            rec['drat_tail']=vout
            print('  drat',vst,round(vt,2),'s','bytes',rec['proof_bytes'])
        if stdout.strip(): rec['solver_stdout_tail']=stdout[-2000:]
        if stderr.strip(): rec['solver_stderr_tail']=stderr[-2000:]
        results.append(rec)
        (OUT/'z4_cyclic_drat_results_partial.json').write_text(json.dumps({'results':results},indent=2)+'\n')
    out=OUT/'z4_cyclic_drat_results.json'
    out.write_text(json.dumps({'field':'F2','method':'Tseitin CNF + Kissat DRAT','patterns':pats,'results':results},indent=2)+'\n')
    print('Saved',out)

if __name__=='__main__':
    main()
