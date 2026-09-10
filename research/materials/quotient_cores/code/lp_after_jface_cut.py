#!/usr/bin/env python3
"""Re-solve the complete E11 Wang LP after adding the analysis J-face cut.

The analysis DRAT-verified J-face UNSAT gives the valid integer-hull cut
    sum_{p in J} x_p <= 18
for J = support of the saved analysis fractional LP solution.  This script adds
that one cut to the complete Wang LP relaxation and solves a few random linear
objectives.  It checks whether the cut merely removes the old fractional point or
starts a useful cutting-plane family.  New LP points are targets only; they are
not supports or rank evidence.
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path
from typing import Sequence

import numpy as np
from scipy import sparse
from scipy.optimize import linprog

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import ROOT, build_core_constraints

OUTDIR = ROOT / "workspace/data/global_J_face"
GLOBAL_PATH = ROOT / "workspace/data/local_hull/global_fractional_solution.json"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"


def build_sparse(records):
    rows=[]; cols=[]; vals=[]; b=[]
    for i,rec in enumerate(records):
        b.append(19-int(rec['L']))
        bs=int(rec['point_bitset'])
        while bs:
            bit=bs & -bs
            rows.append(i); cols.append(bit.bit_length()-1); vals.append(1.0)
            bs ^= bit
    A=sparse.csr_matrix((np.array(vals),(np.array(rows),np.array(cols))),shape=(len(records),255))
    return A,np.array(b,dtype=float)


def solve(A,b,J,seed,objective_kind='random'):
    rng=np.random.default_rng(seed)
    if objective_kind=='random':
        c=rng.normal(size=255)
    elif objective_kind=='maximize_J':
        c=np.zeros(255); c[[p-1 for p in J]]=-1.0
    elif objective_kind=='minimize_outside':
        c=np.ones(255); c[[p-1 for p in J]]=0.0
    else:
        raise ValueError(objective_kind)
    # add J cut as one extra row sum_J <= 18
    jr=np.zeros(255)
    for p in J: jr[p-1]=1.0
    A2=sparse.vstack([A,sparse.csr_matrix(jr.reshape(1,-1))],format='csr')
    b2=np.concatenate([b,[18.0]])
    t0=time.time()
    res=linprog(c,A_ub=A2,b_ub=b2,A_eq=sparse.csr_matrix(np.ones((1,255))),b_eq=np.array([19.0]),bounds=[(0.0,1.0)]*255,method='highs',options={'time_limit':120})
    info={'seed':seed,'objective_kind':objective_kind,'success':bool(res.success),'message':str(res.message),'elapsed_sec':time.time()-t0}
    if res.success:
        x=np.asarray(res.x,dtype=float); rounded=np.rint(x)
        slacks=b2-A2.dot(x)
        nz=[(i+1,float(v)) for i,v in enumerate(x) if v>1e-9]
        frac=[(i+1,float(v)) for i,v in enumerate(x) if abs(v-rounded[i])>1e-7]
        info.update({
            'objective_value':float(res.fun),
            'sum_x':float(x.sum()),
            'sum_on_old_J':float(sum(x[p-1] for p in J)),
            'outside_old_J_mass':float(19.0-sum(x[p-1] for p in J)),
            'j_cut_slack':float(slacks[-1]),
            'n_nonzero_coordinates_tol_1e-9':len(nz),
            'n_fractional_coordinates':len(frac),
            'max_round_distance':float(np.max(np.abs(x-rounded))),
            'nonzero_coordinates':nz,
            'fractional_coordinates':frac,
            'active_complete_wang_constraints_tol_1e-7':int(np.sum(np.abs(slacks[:-1])<1e-7)),
        })
    return info


def main():
    t0=time.time(); OUTDIR.mkdir(parents=True,exist_ok=True)
    old=json.loads(GLOBAL_PATH.read_text())
    xold=np.array(old['global_lp']['x_full'],dtype=float)
    J=[p for p in range(1,256) if xold[p-1]>1e-10]
    lut,_=load_lut(LUT_PATH)
    records,meta=build_core_constraints(CoreQuotient(1),lut)
    A,b=build_sparse(records)
    runs=[]
    for kind,seed in [('maximize_J',620620),('minimize_outside',620621),('random',620622),('random',620623),('random',620624)]:
        print('solve',kind,seed)
        r=solve(A,b,J,seed,kind)
        print({k:r.get(k) for k in ['success','objective_kind','sum_on_old_J','outside_old_J_mass','j_cut_slack','n_nonzero_coordinates_tol_1e-9','n_fractional_coordinates']})
        runs.append(r)
    out=OUTDIR/'lp_after_J65_cut.json'
    out.write_text(json.dumps({
        'schema':'lp_after_jface_cut_v1',
        'meaning':'Complete E11 Wang LP solved after adding the DRAT-supported integer cut sum_{p in J} x_p <= 18. New LP solutions are fractional targets only.',
        'old_global_solution_file':str(GLOBAL_PATH),
        'old_J_size':len(J),
        'old_J_points':J,
        'complete_meta':meta,
        'cut':'sum_{p in old_J} x_p <= 18',
        'runs':runs,
        'elapsed_sec':time.time()-t0,
    },indent=2)+'\n')
    print('saved',out,'elapsed',time.time()-t0)

if __name__=='__main__': main()
