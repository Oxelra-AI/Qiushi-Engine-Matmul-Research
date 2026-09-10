#!/usr/bin/env python3
"""Compute selected drops for ballard_delete_linearization_v2 and save results.

Used after a long all-drop run timed out after drops 0..7.  This wrapper has the same
mathematics as v2, but accepts a drop list and writes after every drop.
"""
from __future__ import annotations
import argparse, json, time
from pathlib import Path
import numpy as np
import sympy as sp
import ballard_delete_linearization_v2 as v2

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'ballard_z4_cyclic'
OUT.mkdir(parents=True, exist_ok=True)
PRIMES=[1000003,1000033,65521,32003]

def rank_Q(A):
    M=sp.Matrix([[int(x) for x in row] for row in np.array(A,dtype=object).tolist()])
    return int(M.rank())

def compute_drop(drop:int):
    J,rhs,meta=v2.build_jacobian(drop, include_global=True)
    Aaug=np.concatenate([J,rhs.reshape(-1,1)],axis=1)
    t=time.time(); rq=rank_Q(J); raq=rank_Q(Aaug); sec=time.time()-t
    return {
        'drop':drop,'jacobian_shape':list(J.shape),'rhs_nonzero_monomials':int(sum(1 for x in rhs)),
        'rank_Q':rq,'augmented_rank_Q':raq,'rhs_in_Q_image': bool(raq==rq),'exact_rank_seconds':sec,
        'rank_mod_primes':{str(p):v2.rank_mod(J,p) for p in PRIMES},
        'augmented_rank_mod_primes':{str(p):v2.rank_mod(Aaug,p) for p in PRIMES},
    }

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--drops', default='8,9,10')
    ap.add_argument('--out', default='ballard_delete_linearization_v2_subset.json')
    args=ap.parse_args()
    drops=[int(x) for x in args.drops.split(',') if x.strip()]
    records=[]
    out=OUT/args.out
    for d in drops:
        rec=compute_drop(d)
        print(rec, flush=True)
        records.append(rec)
        out.write_text(json.dumps({'records':records}, indent=2)+'\n')
    print('Saved',out)
if __name__=='__main__': main()
