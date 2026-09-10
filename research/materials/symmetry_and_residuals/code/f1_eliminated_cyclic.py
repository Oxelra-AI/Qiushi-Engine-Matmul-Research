#!/usr/bin/env python3
"""
analysis: f=1 eliminated-cube encoding for cyclic F_2 rank-22 skeleton (f,m)=(1,7).

For f=1 the fixed cyclic term is a single cube X⊗X⊗X.  Instead of 511 cube
selector variables, introduce only the nine bits X_i and impose the full cyclic
coordinate equations
    orbit_sum(i,j,k) + X_i X_j X_k = T(i,j,k)
for the 249 cyclic coordinate orbits.  The diagonal entries (i,i,i) force
X_i = T(i,i,i)+sum_o U_oi V_oi W_oi, so the cube is automatically determined
by the orbit variables.  We also add the 120 orbit-only diagonal-collapse
high-degree constraints as redundant but useful consequences.

A SAT model is expanded and checked on all 729 Brent equations.
"""

from __future__ import annotations

import argparse, itertools, json, subprocess, time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / 'data' / 'f1_eliminated'
N = 9

import sys
sys.path.insert(0, str(SCRIPT_DIR))
import orbit_cube_decode_sat as oc


def encode_f1(m: int = 7, add_diag: bool = True, sym_break: bool = True):
    T = oc.build_T333(); reps = oc.cyclic_orbit_reps()
    enc = oc.CMSXOREncoder()
    X = enc.new_vars(N)
    U = [enc.new_vars(N) for _ in range(m)]
    V = [enc.new_vars(N) for _ in range(m)]
    W = [enc.new_vars(N) for _ in range(m)]
    if sym_break:
        # Cube has no ordering symmetry.  Free orbit symmetries only.
        for o in range(m):
            enc.add_lex_le(U[o], V[o])
            enc.add_lex_le(U[o], W[o])
        for o in range(m-1):
            enc.add_lex_le(U[o]+V[o]+W[o], U[o+1]+V[o+1]+W[o+1])
    for i,j,k in reps:
        terms = []
        for o in range(m):
            terms.extend(oc.orbit_contribution_vars(enc, U[o], V[o], W[o], i,j,k))
        terms.append(enc.AND3(X[i], X[j], X[k]))
        enc.add_xor(terms, T[i][j][k])
    if add_diag:
        anf = oc.trM3_anf_masks()
        for d in (2,3):
            for tup in itertools.combinations(range(N), d):
                mask = oc.mask_from_tuple(tup)
                terms = []
                for o in range(m):
                    terms.extend(oc.product_terms_for_mask(mask, U[o], V[o], W[o], enc))
                enc.add_xor(terms, anf.get(mask,0))
    return enc, {'X':X,'U':U,'V':V,'W':W,'reps':reps}


def run_cms(cnf: Path, timeout: int):
    t0=time.time()
    try:
        r=subprocess.run(['cryptominisat5','--verb','0',str(cnf)],capture_output=True,text=True,timeout=timeout)
    except subprocess.TimeoutExpired:
        return {'status':'TIMEOUT','time_sec':time.time()-t0,'returncode':None,'stdout':'','stderr':''}
    st='SAT' if r.returncode==10 else 'UNSAT' if r.returncode==20 else 'UNKNOWN'
    return {'status':st,'time_sec':time.time()-t0,'returncode':r.returncode,'stdout':r.stdout,'stderr':r.stderr}


def parse_assignment(stdout):
    a={}
    for line in stdout.splitlines():
        if line.startswith('v '):
            for tok in line[2:].split():
                lit=int(tok)
                if lit: a[abs(lit)] = lit > 0
    return a


def bits(a, arr): return [1 if a.get(v,False) else 0 for v in arr]


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--timeout',type=int,default=600)
    ap.add_argument('--no-diag',action='store_true')
    ap.add_argument('--no-sym-break',action='store_true')
    args=ap.parse_args()
    DATA_DIR.mkdir(parents=True,exist_ok=True)
    enc,v=encode_f1(7, add_diag=not args.no_diag, sym_break=not args.no_sym_break)
    cnf=DATA_DIR / ('f1_m7_eliminated' + ('_nodiag' if args.no_diag else '') + '.cnf')
    enc.write(cnf)
    print(json.dumps({'cnf':str(cnf),'vars':enc.nv,'regular_clauses':len(enc.reg),'xor_clauses':len(enc.xors),'and_cache':len(enc.and_cache),'diag_added':not args.no_diag},indent=2))
    sol=run_cms(cnf,args.timeout)
    print(json.dumps({'status':sol['status'],'sec':sol['time_sec'],'returncode':sol['returncode']},indent=2))
    rec={'cnf':str(cnf),'vars':enc.nv,'regular_clauses':len(enc.reg),'xor_clauses':len(enc.xors),'timeout':args.timeout,'status':sol['status'],'solve_sec':round(sol['time_sec'],6),'returncode':sol['returncode']}
    if sol['status']=='SAT':
        a=parse_assignment(sol['stdout'])
        X=bits(a,v['X'])
        orbits=[]
        for o in range(7):
            orbits.append((bits(a,v['U'][o]),bits(a,v['V'][o]),bits(a,v['W'][o])))
        err,bad=oc.verify_brent([X] if any(X) else [],orbits,oc.build_T333())
        rec.update({'X':X,'nonzero_cube':any(X),'orbits':[[U,V,W] for U,V,W in orbits],'nonzero_orbits':sum(1 for U,V,W in orbits if any(U) or any(V) or any(W)),'brent_errors':err,'bad_examples':bad})
        print(json.dumps({'X':X,'nonzero_orbits':rec['nonzero_orbits'],'brent_errors':err,'bad_examples':bad[:3]},indent=2))
    else:
        rec['stdout_tail']=sol['stdout'][-4000:]
        rec['stderr_tail']=sol['stderr'][-4000:]
    out=DATA_DIR/'f1_m7_eliminated_result.json'
    out.write_text(json.dumps(rec,indent=2)+'\n')
    print(f'Saved {out}')

if __name__=='__main__':
    main()
