#!/usr/bin/env python3
"""Save a nonzero 12x12 minor certificate for the BILR mixed-trace map Phi."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'plane_invariants'
OUT.mkdir(parents=True, exist_ok=True)

off=[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]
labels=[f'E{i}{j}' for i,j in off]+['H0','H1']
l2_pairs=[(i,j) for i in range(8) for j in range(i+1,8)]

def mat(M): return sp.Matrix(M)
def tf(M): return M-sp.trace(M)/3*sp.eye(3)
def coords(M):
    M=tf(M)
    c=[]
    for i,j in off: c.append(sp.simplify(M[i,j]))
    c.append(sp.simplify(M[0,0])); c.append(sp.simplify(-M[2,2]))
    return sp.Matrix(c)
def wedge(x,y):
    return sp.Matrix([sp.simplify(x[i]*y[j]-x[j]*y[i]) for i,j in l2_pairs])
with open(WS/'data'/'ballard_z4_cyclic'/'ballard_z4_cyclic_scheme.json') as f: scheme=json.load(f)
cols=[]; col_labels=[]
for j,rep in enumerate(scheme['free_orbit_representatives']):
    u,v,w=[coords(mat(rep[k])) for k in ['U','V','W']]
    cols += [wedge(v,w), wedge(w,u), wedge(u,v)]
    col_labels += [f'P{j}:a(v^w)', f'P{j}:b(w^u)', f'P{j}:d(u^v)']
Phi=sp.Matrix.hstack(*cols)
assert Phi.rank()==12
# greedy independent row set
chosen=[]
for r in range(Phi.rows):
    cand=chosen+[r]
    if Phi.extract(cand, list(range(12))).rank() > len(chosen):
        chosen=cand
    if len(chosen)==12: break
minor=Phi.extract(chosen, list(range(12)))
det=sp.factor(minor.det())
assert det!=0
results={
    'scope':'Nonzero 12x12 minor certificate for BILR mixed-trace Phi over Q.',
    'sl3_basis':labels,
    'lambda2_row_pairs':[[labels[i],labels[j]] for i,j in l2_pairs],
    'domain_column_labels':col_labels,
    'selected_row_indices':chosen,
    'selected_row_pairs':[[labels[l2_pairs[i][0]],labels[l2_pairs[i][1]]] for i in chosen],
    'selected_column_indices':list(range(12)),
    'determinant':str(det),
    'rank':int(Phi.rank()),
    'minor_matrix':[[str(Phi[i,j]) for j in range(12)] for i in chosen],
}
out=OUT/'bilr_phi_rank12_minor.json'
with open(out,'w') as f: json.dump(results,f,indent=2)
print(json.dumps({'out':str(out),'determinant':str(det),'rows':chosen},indent=2))
