#!/usr/bin/env python3
"""analysis: exact Heisenberg/Z3^2 invariant-triple obstruction for fixed-plane orbits.

Over F_p with a primitive cube root, use the two commuting diagonal matrices on sl3
whose weights are the root positions.  Enumerate the invariant coordinate trivectors.
The fixed-plane-only four-orbit ansatz would need omega to be a sum of four invariant
basis trivectors; if omega has more than four nonzero independent invariant coordinates,
that ansatz is impossible.
"""
from __future__ import annotations
import argparse, importlib.util, itertools, json
from pathlib import Path

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'exterior_linear_sections'
spec=importlib.util.spec_from_file_location('s57', WS/'scripts'/'invariant_linear_section.py')
s57=importlib.util.module_from_spec(spec); spec.loader.exec_module(s57)  # type: ignore

# sl3 basis E01,E02,E10,E12,E20,E21,H0,H1.  Diagonal conjugation by diag(alpha,beta,gamma)
# gives weights chi_i - chi_j on Eij and 0,0 on H0,H1.
SL3_WEIGHTS=[(1,0),(1,1),(2,0),(0,1),(2,2),(0,2),(0,0),(0,0)]

def target_in_eigenbasis_same(p):
    # In this diagonal basis the sl3 basis is already an eigenbasis; use analysis omega/3 support.
    return s57.target_old(p)

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--prime',type=int,default=7); args=ap.parse_args(); p=args.prime
    inv=[]
    for t in s57.TRIPLES:
        wt=((SL3_WEIGHTS[t[0]][0]+SL3_WEIGHTS[t[1]][0]+SL3_WEIGHTS[t[2]][0])%3,
            (SL3_WEIGHTS[t[0]][1]+SL3_WEIGHTS[t[1]][1]+SL3_WEIGHTS[t[2]][1])%3)
        if wt==(0,0): inv.append(t)
    target=target_in_eigenbasis_same(p)
    nz=[s57.TRIPLES[i] for i,c in enumerate(target) if c%p]
    noninv=[t for t in nz if t not in inv]
    # Coordinate invariant basis trivectors are independent by construction; each fixed coordinate plane contributes one.
    rec={'prime':p,'weights':SL3_WEIGHTS,'invariant_triple_count':len(inv),'invariant_triples':[list(t) for t in inv],
         'target_nonzero_count':len(nz),'target_nonzero_triples':[list(t) for t in nz],
         'target_nonzero_outside_invariants':[list(t) for t in noninv],
         'min_fixed_coordinate_planes_needed':len(nz) if not noninv else None,
         'four_fixed_planes_impossible': (not noninv and len(nz)>4),
         'interpretation':'This tests only the fixed-coordinate-plane H-invariant ansatz. It does not exclude 1+3 patterns or non-coordinate invariant planes.'}
    path=OUT/'heisenberg_z3_fixed_orbit_obstruction.json'
    path.write_text(json.dumps(rec,indent=2,sort_keys=True)+'\n')
    print(json.dumps(rec,indent=2,sort_keys=True)); print('SAVED',path)
if __name__=='__main__': main()
