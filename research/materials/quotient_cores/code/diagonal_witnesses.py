#!/usr/bin/env python3
"""Extract compact primary-variable witnesses for the analysis diagonal collapse SAT cases.

The main diagonal-collapse script records UNSAT proofs for m<=3 but, for SAT
m>=4, kept only solver output tails.  This script reruns the small SAT cases,
extracts U,V,W orbit vectors, and directly recomputes the 120 high-degree ANF
coefficients of sum_o ell_U ell_V ell_W against tr(M^3).
"""

from __future__ import annotations

import itertools, json, subprocess, sys, time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT_DIR = WS / 'data' / 'diagonal_collapse'
sys.path.insert(0, str(SCRIPT_DIR))
import f2_diagonal_collapse as diag

N=9

def parse_assignment(stdout: str) -> Dict[int,int]:
    a={}
    for line in stdout.splitlines():
        if line.startswith('v '):
            for tok in line[2:].split():
                lit=int(tok)
                if lit: a[abs(lit)] = 1 if lit>0 else 0
    return a

def bits(a, arr): return [a.get(v,0) for v in arr]

def coeff_for_mask(orbits, mask: int) -> int:
    vs=diag.mask_vars(mask)
    val=0
    if len(vs)==2:
        p,q=vs
        assignments=[(p,p,q),(p,q,p),(q,p,p),(q,q,p),(q,p,q),(p,q,q)]
    elif len(vs)==3:
        assignments=list(itertools.permutations(vs,3))
    else:
        raise ValueError(mask)
    for U,V,W in orbits:
        for a,b,c in assignments:
            val ^= U[a] & V[b] & W[c]
    return val

def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    anf=diag.trM3_anf()
    targets={}
    for d in (2,3):
        for tup in itertools.combinations(range(N),d):
            mask=diag.mask_from_tuple(tup); targets[mask]=anf.get(mask,0)
    records=[]
    for m in [4,5,6,7]:
        enc,vmap=diag.encode_diagonal(m,targets,sym_break=True)
        cnf=OUT_DIR / f'diag_highdeg_m{m}_witness.cnf'
        enc.write_dimacs(cnf)
        t0=time.time(); r=subprocess.run(['kissat',str(cnf)],capture_output=True,text=True,timeout=120); dt=time.time()-t0
        status='SAT' if r.returncode==10 else 'UNSAT' if r.returncode==20 else 'UNKNOWN'
        rec={'m':m,'status':status,'solve_sec':round(dt,6),'returncode':r.returncode,'cnf':str(cnf),'total_vars':enc.nv,'clauses':len(enc.clauses)}
        if status=='SAT':
            a=parse_assignment(r.stdout)
            orbits=[]
            for o in range(m):
                orbits.append((bits(a,vmap['U'][o]),bits(a,vmap['V'][o]),bits(a,vmap['W'][o])))
            mism=[]
            for mask,tgt in targets.items():
                val=coeff_for_mask(orbits,mask)
                if val!=tgt:
                    mism.append({'mask':diag.mask_vars(mask),'got':val,'target':tgt})
            rec.update({'mismatch_count':len(mism),'mismatches':mism[:10],'orbits':[[U,V,W] for U,V,W in orbits],
                        'nonzero_orbits':sum(1 for U,V,W in orbits if any(U) or any(V) or any(W))})
            print({'m':m,'status':status,'mismatch_count':len(mism),'nonzero_orbits':rec['nonzero_orbits'],'solve_sec':dt})
        else:
            print({'m':m,'status':status,'solve_sec':dt})
        records.append(rec)
    out=OUT_DIR/'diagonal_collapse_sat_witnesses_m4_m7.json'
    out.write_text(json.dumps({'records':records},indent=2)+'\n')
    print(f'Saved {out}')
if __name__=='__main__': main()
