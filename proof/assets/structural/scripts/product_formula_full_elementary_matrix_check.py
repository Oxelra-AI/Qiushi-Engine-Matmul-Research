#!/usr/bin/env python3
"""Complete elementary sparse-matrix check of the A-split product formula.

This is a less tautological companion to `short_saturation_checks.py`.
It builds the actual 27x27 permutation matrix P for T_{333} in the A-split
flattening convention and compares

    F(A,B,C) P^{-1} F(A',B',C')

with

    F(A (B' C^T) A', B, C')

for all 729 x 729 elementary simple tensor pairs.  Since both sides are
multilinear in A,B,C,A',B',C', agreement on elementary matrix units proves the
formula for arbitrary factors over F2.

The check uses sparse one-entry descriptions of elementary F matrices and the
actual P^{-1} lookup table derived from P, rather than hard-coding the same
condition on both sides.
"""
from __future__ import annotations

import json
import time
from itertools import product
from pathlib import Path

OUT = Path('assets/structural/data/structural/product_formula_full_elementary_matrix_check.json')


def idx_A_B(i:int, p:int, q:int) -> int:
    return i*9 + p*3 + q


def idx_A_C(j:int, r:int, s:int) -> int:
    return j*9 + r*3 + s


def build_P_positions():
    # P[row=(i,(j,k)), col=(j,(i,k))] = 1 for matrix multiplication.
    pos=[]
    for i in range(3):
        for j in range(3):
            for k in range(3):
                row=idx_A_B(i,j,k)
                col=idx_A_C(j,i,k)
                pos.append((row,col))
    assert len(pos)==27 and len({r for r,c in pos})==27 and len({c for r,c in pos})==27
    return pos


def elementary_F_pos(A, B, C):
    # A=(i,j), B=(p,q), C=(r,s); F has one at row (i,(p,q)), col (j,(r,s)).
    (i,j),(p,q),(r,s)=A,B,C
    return (idx_A_B(i,p,q), idx_A_C(j,r,s))


def compose_sparse(f1, pinv_lookup, f2):
    # f1=(row1,col1), f2=(row2,col2).  Product f1 * Pinv * f2 is nonzero iff Pinv[col1,row2]=1.
    row1,col1=f1; row2,col2=f2
    if pinv_lookup.get((col1,row2),0):
        return {(row1,col2)}
    return set()


def predicted_sparse(A,B,C,Ap,Bp,Cp):
    # Compute elementary A(B' C^T)A'.  Return sparse F positions; at most one for elementary inputs.
    (i,j)=A; (p,q)=B; (r,s)=C
    (u,v)=Ap; (x,y)=Bp; (z,w)=Cp
    out=set()
    # B' C^T has entry (x,r)=1 iff y=s.  A times this times A' is E_{i,v} iff j=x, y=s, r=u.
    if j==x and y==s and r==u:
        out.add((idx_A_B(i,p,q), idx_A_C(v,z,w)))
    return out


def main():
    t0=time.time()
    P=build_P_positions()
    # Pinv is transpose of permutation P: Pinv[col,row] = 1 for each P[row,col]=1.
    pinv_lookup={(c,r):1 for r,c in P}
    coords=list(product(range(3),range(3)))
    elems=list(product(coords,coords,coords))
    failures=[]; checks=0; nonzero_lhs=0; nonzero_rhs=0
    for A,B,C in elems:
        f1=elementary_F_pos(A,B,C)
        for Ap,Bp,Cp in elems:
            checks += 1
            f2=elementary_F_pos(Ap,Bp,Cp)
            lhs=compose_sparse(f1,pinv_lookup,f2)
            rhs=predicted_sparse(A,B,C,Ap,Bp,Cp)
            if lhs: nonzero_lhs += 1
            if rhs: nonzero_rhs += 1
            if lhs != rhs:
                failures.append({'A':A,'B':B,'C':C,'Ap':Ap,'Bp':Bp,'Cp':Cp,'lhs':sorted(lhs),'rhs':sorted(rhs)})
                if len(failures)>=20:
                    break
        if len(failures)>=20:
            break
    out={'schema':'s0908_product_formula_full_elementary_matrix_check_v1','meaning':'Sparse actual-P elementary check of F(A,B,C)PinvF(Ap,Bp,Cp)=F(A(Bp C^T)Ap,B,Cp). By multilinearity, elementary agreement proves the formula for all factors over F2.','P_position_count':len(P),'P_is_permutation':len({r for r,c in P})==27 and len({c for r,c in P})==27,'checks':checks,'nonzero_lhs_count':nonzero_lhs,'nonzero_rhs_count':nonzero_rhs,'failure_count':len(failures),'failures_head':failures,'elapsed_sec':time.time()-t0}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(OUT),'checks':checks,'failures':len(failures),'nonzero_lhs':nonzero_lhs,'nonzero_rhs':nonzero_rhs,'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__': main()
