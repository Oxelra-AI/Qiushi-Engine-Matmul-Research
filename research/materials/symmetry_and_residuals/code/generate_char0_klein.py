#!/usr/bin/env python3
"""Generate characteristic-zero Singular equations for the analysis Klein exterior chart.

The Klein diagonal eigenbasis is rational.  We construct it directly over Q using the
same ordered character basis as the finite-field script and impose proportionality of
invariant Pluecker coordinates in the pivot chart.
"""
from __future__ import annotations
import itertools
from fractions import Fraction
from pathlib import Path

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'exterior_linear_sections'
TRIPLES=list(itertools.combinations(range(8),3)); TIDX={t:i for i,t in enumerate(TRIPLES)}
VARS=[f'x{i}' for i in range(15)]
# Character-ordered Klein eigenbasis in original sl3 basis from finite-field output:
# weights: (0,0): H0,H1; (0,1): E12,E21; (1,0): E02,E20; (1,1): E01,E10
# old basis: E01,E02,E10,E12,E20,E21,H0,H1.
old_indices=[6,7,3,5,1,4,0,2]
weights=[(0,0),(0,0),(0,1),(0,1),(1,0),(1,0),(1,1),(1,1)]

def sign_perm(lst):
    inv=0
    for i in range(len(lst)):
        for j in range(i+1,len(lst)):
            if lst[i]>lst[j]: inv+=1
    return -1 if inv%2 else 1

def target_old():
    v=[Fraction(0) for _ in range(56)]
    for t,c in { (0,2,6):1, (0,3,4):1, (1,2,5):-1, (1,4,6):1, (1,4,7):1, (3,5,7):1}.items():
        v[TIDX[t]]=Fraction(c)
    return v

def target_new_from_permutation():
    # new basis vector j = old basis vector old_indices[j].  Wedge coords transform by sorting old indices.
    old=target_old(); new=[Fraction(0) for _ in range(56)]
    for tnew in TRIPLES:
        old_tuple=[old_indices[j] for j in tnew]
        sold=tuple(sorted(old_tuple))
        if len(set(sold))<3: continue
        new[TIDX[tnew]]=old[TIDX[sold]]*sign_perm(old_tuple)
    return new

def poly_const(c,n): return {tuple([0]*n): Fraction(c)} if c else {}
def poly_var(i,n):
    e=[0]*n; e[i]=1; return {tuple(e):Fraction(1)}
def trim(A): return {m:c for m,c in A.items() if c}
def add(A,B):
    C=A.copy()
    for m,c in B.items(): C[m]=C.get(m,Fraction(0))+c
    return trim(C)
def neg(A): return {m:-c for m,c in A.items() if c}
def sub(A,B): return add(A,neg(B))
def mul(A,B):
    C={}
    for ma,ca in A.items():
        for mb,cb in B.items():
            m=tuple(x+y for x,y in zip(ma,mb)); C[m]=C.get(m,Fraction(0))+ca*cb
    return trim(C)
def scalar(A,s): return {m:c*s for m,c in A.items() if c*s}
def det3(M,n):
    return add(sub(mul(M[0][0],sub(mul(M[1][1],M[2][2]),mul(M[1][2],M[2][1]))),
                   mul(M[0][1],sub(mul(M[1][0],M[2][2]),mul(M[1][2],M[2][0])))),
               mul(M[0][2],sub(mul(M[1][0],M[2][1]),mul(M[1][1],M[2][0]))))
def chart_polys(pivot):
    n=15; nonpiv=[j for j in range(8) if j not in pivot]
    B=[[{} for _ in range(8)] for __ in range(3)]
    for r,c in enumerate(pivot): B[r][c]=poly_const(1,n)
    idx=0
    for c in nonpiv:
        for r in range(3): B[r][c]=poly_var(idx,n); idx+=1
    return [det3([[B[r][c] for c in tri] for r in range(3)],n) for tri in TRIPLES]

def poly_to_sing(poly):
    if not poly: return '0'
    terms=[]
    for mon,c in sorted(poly.items(), key=lambda kv:(sum(kv[0]),kv[0])):
        factors=[]
        if c == -1 and sum(mon)>0:
            factors.append('-1')
        elif c != 1 or sum(mon)==0:
            factors.append(str(c.numerator) if c.denominator==1 else f'({c.numerator}/{c.denominator})')
        for i,e in enumerate(mon):
            if e==1: factors.append(VARS[i])
            elif e>1: factors.append(f'{VARS[i]}^{e}')
        terms.append('*'.join(factors) if factors else '1')
    return ' + '.join(terms).replace('+ -','- ')

def main():
    pivot=(2,5,6)
    target=target_new_from_permutation()
    inv=[t for t in TRIPLES if ((sum(weights[i][0] for i in t)%2)==0 and (sum(weights[i][1] for i in t)%2)==0)]
    polys=chart_polys(pivot); tp=target[TIDX[pivot]]
    assert tp != 0
    eqs=[]
    for tri in inv:
        if tri==pivot: continue
        eq=sub(scalar(polys[TIDX[tri]],tp), poly_const(target[TIDX[tri]],15))
        if eq: eqs.append(eq)
    varstr=','.join(VARS); eqstr=',\n'.join(poly_to_sing(e) for e in eqs)
    content=f'''// analysis characteristic-zero Klein diagonal exterior chart\nring r=0,({varstr}),dp;\nideal I=\n{eqstr};\nideal G=std(I);\nprint("char0 Klein pivot {pivot} equations {len(eqs)}");\nprint("dim"); dim(G);\nprint("degree"); degree(G);\nprint("size"); size(G);\nprint("indep"); indepSet(G);\nprint("lead_first30"); for (int i=1; i<=size(G) and i<=30; i=i+1) {{ lead(G[i]); }}\nquit;\n'''
    path=OUT/'klein_diag_char0_256.sing'; path.write_text(content); print(path)
    meta={'pivot':pivot,'target_nonzero':{str(TRIPLES[i]):str(c) for i,c in enumerate(target) if c},'invariant_count':len(inv),'invariants':[str(t) for t in inv]}
    (OUT/'klein_diag_char0_256_meta.json').write_text(__import__('json').dumps(meta,indent=2)+'\n')
if __name__=='__main__': main()
