#!/usr/bin/env python3
"""
analysis: fixed-cube scan for the surviving cyclic F_2 skeleton m=7, f=1.

For f=1 the cube side has only 512 choices (zero cube plus 511 nonzero cubes).
For each chosen cube c, solve the orbit-only cyclic equations
    sum_{o=1}^m cyclic(U_o,V_o,W_o) = T333 + c^3
over F_2, optionally with the 120 diagonal-collapse high-degree equations.
This removes the selector/cardinality part from the analysis cube-decoding
encoding and breaks the search into small independent instances.

A SAT result is expanded and checked against all 729 Brent equations.  A complete
UNSAT scan over all 512 cube masks would exclude the (f,m)=(1,7) cyclic F2
rank-22 skeleton, modulo proof replay if run with a proof-capable CNF encoder.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / "data" / "fixed_cube_scan"
N = 9

import sys
sys.path.insert(0, str(SCRIPT_DIR))
import orbit_cube_decode_sat as oc


def encode_fixed_cube(m: int, cube_mask: int, add_diag: bool = True, sym_break: bool = True):
    T = oc.build_T333(); reps = oc.cyclic_orbit_reps()
    enc = oc.CMSXOREncoder()
    U = [enc.new_vars(N) for _ in range(m)]
    V = [enc.new_vars(N) for _ in range(m)]
    W = [enc.new_vars(N) for _ in range(m)]
    if sym_break:
        for o in range(m):
            enc.add_lex_le(U[o], V[o])
            enc.add_lex_le(U[o], W[o])
        for o in range(m - 1):
            enc.add_lex_le(U[o] + V[o] + W[o], U[o+1] + V[o+1] + W[o+1])
    cube_vec = oc.mask_to_vec(cube_mask) if cube_mask else [0] * N
    for i,j,k in reps:
        terms = []
        for o in range(m):
            terms.extend(oc.orbit_contribution_vars(enc, U[o], V[o], W[o], i, j, k))
        target = T[i][j][k] ^ (cube_vec[i] & cube_vec[j] & cube_vec[k])
        enc.add_xor(terms, target)
    if add_diag:
        anf = oc.trM3_anf_masks()
        for d in (2,3):
            import itertools
            for tup in itertools.combinations(range(N), d):
                mask = oc.mask_from_tuple(tup)
                terms = []
                for o in range(m):
                    terms.extend(oc.product_terms_for_mask(mask, U[o], V[o], W[o], enc))
                enc.add_xor(terms, anf.get(mask,0))
    return enc, {"U": U, "V": V, "W": W, "reps": reps, "cube_mask": cube_mask}


def run_cms(cnf: Path, timeout: int):
    t0 = time.time()
    try:
        r = subprocess.run(["cryptominisat5", "--verb", "0", str(cnf)], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"status": "TIMEOUT", "time_sec": time.time() - t0, "returncode": None, "stdout": "", "stderr": ""}
    if r.returncode == 10:
        st = "SAT"
    elif r.returncode == 20:
        st = "UNSAT"
    else:
        st = "UNKNOWN"
    return {"status": st, "time_sec": time.time() - t0, "returncode": r.returncode, "stdout": r.stdout, "stderr": r.stderr}


def parse_assignment(stdout: str) -> Dict[int, bool]:
    d = {}
    for line in stdout.splitlines():
        if line.startswith('v '):
            for tok in line[2:].split():
                lit = int(tok)
                if lit == 0: continue
                d[abs(lit)] = lit > 0
    return d


def bits(assign, arr):
    return [1 if assign.get(v, False) else 0 for v in arr]


def extract(assign, vmap, m):
    orbits=[]
    for o in range(m):
        orbits.append((bits(assign, vmap['U'][o]), bits(assign, vmap['V'][o]), bits(assign, vmap['W'][o])))
    cube = oc.mask_to_vec(vmap['cube_mask']) if vmap['cube_mask'] else []
    return ([cube] if cube else []), orbits


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--m', type=int, default=7)
    ap.add_argument('--timeout', type=int, default=30)
    ap.add_argument('--limit', type=int, default=32)
    ap.add_argument('--start', type=int, default=0)
    ap.add_argument('--no-diag', action='store_true')
    ap.add_argument('--masks', default=None, help='comma-separated masks to scan instead of range')
    args = ap.parse_args()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    if args.masks:
        masks = [int(x) for x in args.masks.split(',') if x.strip()]
    else:
        all_masks = list(range(0, 1 << N))
        masks = all_masks[args.start: args.start + args.limit]
    T = oc.build_T333()
    records=[]
    for cm in masks:
        print('='*72)
        print(f'm={args.m} fixed cube mask={cm} vec={oc.mask_to_vec(cm) if cm else [0]*N}')
        t0=time.time(); enc,v=encode_fixed_cube(args.m, cm, add_diag=not args.no_diag, sym_break=True); enc_sec=time.time()-t0
        cnf=DATA_DIR / f'fixed_cube_m{args.m}_mask{cm}.cnf'
        enc.write(cnf)
        print(f'  encoded {enc.nv} vars, {len(enc.reg)} regular, {len(enc.xors)} xor in {enc_sec:.3f}s')
        sol=run_cms(cnf,args.timeout)
        print(f"  {sol['status']} {sol['time_sec']:.3f}s rc={sol['returncode']}")
        rec={'m':args.m,'cube_mask':cm,'cube_vec':oc.mask_to_vec(cm) if cm else [0]*N,
             'total_vars':enc.nv,'regular_clauses':len(enc.reg),'xor_clauses':len(enc.xors),
             'encoding_sec':round(enc_sec,6),'timeout':args.timeout,
             'status':sol['status'],'solve_sec':round(sol['time_sec'],6),'returncode':sol['returncode'],
             'cnf':str(cnf)}
        if sol['status']=='SAT':
            a=parse_assignment(sol['stdout']); cubes,orbits=extract(a,v,args.m); err,bad=oc.verify_brent(cubes,orbits,T)
            rec.update({'brent_errors':err,'bad_examples':bad,'cubes':cubes,'orbits':[[U,V,W] for U,V,W in orbits]})
            print(f'  verified brent_errors={err}')
            if err==0:
                print('  *** VERIFIED CYCLIC F2 RANK<=22 WITNESS FOUND ***')
                records.append(rec); break
        else:
            rec['stdout_tail']=sol['stdout'][-2000:]; rec['stderr_tail']=sol['stderr'][-2000:]
        records.append(rec)
        out=DATA_DIR / f'fixed_cube_scan_m{args.m}_start{args.start}_limit{args.limit}.json'
        out.write_text(json.dumps({'records':records},indent=2)+'\n')
    out=DATA_DIR / f'fixed_cube_scan_m{args.m}_start{args.start}_limit{args.limit}.json'
    out.write_text(json.dumps({'records':records},indent=2)+'\n')
    print(f'Saved {out}')

if __name__=='__main__':
    main()
