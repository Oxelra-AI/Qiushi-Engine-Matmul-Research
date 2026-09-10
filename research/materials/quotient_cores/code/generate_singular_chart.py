#!/usr/bin/env python3
"""Generate Singular scripts for analysis finite-symmetry exterior charts."""
from __future__ import annotations
import argparse, importlib.util
from pathlib import Path

WS = Path(__file__).resolve().parent.parent
SRC = WS / 'scripts' / 'invariant_linear_section.py'
spec = importlib.util.spec_from_file_location('s57', SRC)
s57 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s57)  # type: ignore

VARS=[f'x{i}' for i in range(15)]

def poly_to_singular(poly,p):
    if not poly: return '0'
    terms=[]
    for mon,c in sorted(poly.items(), key=lambda kv:(sum(kv[0]),kv[0])):
        c%=p
        if c==0: continue
        factors=[]
        if c!=1 or sum(mon)==0:
            factors.append(str(c))
        for i,e in enumerate(mon):
            if e==1: factors.append(VARS[i])
            elif e>1: factors.append(f'{VARS[i]}^({e})')
        terms.append('*'.join(factors) if factors else '1')
    return ' + '.join(terms) if terms else '0'

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--prime',type=int,default=5)
    ap.add_argument('--family',required=True)
    ap.add_argument('--pivot',required=True)
    ap.add_argument('--out',required=True)
    ap.add_argument('--field-equations',action='store_true')
    ap.add_argument('--order',default='dp',choices=['dp','lp'])
    args=ap.parse_args()
    p=args.prime
    pivot=tuple(int(x) for x in args.pivot.split(','))
    gens3_ad,_=s57.group_ad_generators(args.family,p)
    E,weights=s57.simultaneous_eigenbasis(gens3_ad,args.family,p)
    L=s57.lambda3_matrix(E,p)
    target_new=s57.solve_square(L,s57.target_old(p),p)
    inv_tr=s57.invariant_triples(weights,args.family)
    polys,_=s57.chart_plucker_polys(pivot,p)
    tp=target_new[s57.TIDX[pivot]]%p
    eqs=[]
    for tri in inv_tr:
        if tri==pivot: continue
        idx=s57.TIDX[tri]
        eq=s57.poly_sub(s57.poly_scalar(polys[idx],tp,p), s57.poly_const(target_new[idx]%p,15,p), p)
        if eq: eqs.append(eq)
    eqstr=',\n'.join(poly_to_singular(e,p) for e in eqs)
    field_block=''
    if args.field_equations:
        field_eqs=','.join([f'{v}^{p}-{v}' for v in VARS])
        field_block=f'\nideal Fq = {field_eqs};\nI = I,Fq;\n'
    varstr=','.join(VARS)
    content=f'''// analysis generated Singular chart\n// family={args.family} prime={p} pivot={pivot}\nLIB "general.lib";\noption(redSB);\nring r={p},({varstr}),{args.order};\nideal I=\n{eqstr};\n{field_block}\nprint("family={args.family} prime={p} pivot={pivot} equations={len(eqs)} field_equations={args.field_equations} order={args.order}");\nprint("computing std");\nideal G=std(I);\nprint("std_done");\nprint("dim");\ndim(G);\nprint("vdim");\nvdim(G);\nprint("degree");\ndegree(G);\nprint("ncols_std");\nsize(G);\nprint("indep");\nindepSet(G);\nprint("G");\nG;\nquit;\n'''
    out=Path(args.out); out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(content)
    print(out)

if __name__=='__main__': main()
