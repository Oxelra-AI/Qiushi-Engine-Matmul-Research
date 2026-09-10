#!/usr/bin/env python3
"""
analysis: exact modular tail test for the BILR residual, pattern 4+4+2.

After the two size-4 orbits are recovered from the off-blocks, include hidden tail
scalars h1,h2.  This script tests whether the remaining p^3+pq^2 tail can be a
single length-2 Z4 cube orbit:
    (P+Q)^3+(P-Q)^3 = 2P^3+6P Q^2.
It works over F_65521 on the BILR residual only, using the generic variants from
analysis.  This is a positive/control calculation for the tail equations; analysis's
Koszul--Young rank already proves the fixed BILR residual has Waring rank 11.
"""
from __future__ import annotations

import json
from pathlib import Path
import numpy as np
import sympy as sp

import z4_qbasis_selftest as qb
import z4_tail_branch_analyzer as ta
from z4_qbasis_generic_extractor import P, p3_indices, pq2_indices

SCRIPT_DIR=Path(__file__).resolve().parent
WS=SCRIPT_DIR.parent
OUT=WS/'data'/'z4_qbasis'
OUT.mkdir(parents=True,exist_ok=True)

h1,h2,a0,a1,a2,b0,b1=sp.symbols('h1 h2 a0 a1 a2 b0 b1')

# p^3 monomial coefficient order from p3_indices(): combinations (0,1,2).
def p3_cube_exprs(coeff=2):
    a=[a0,a1,a2]
    mons=[]
    for i in range(3):
        for j in range(i,3):
            for k in range(j,3):
                # coefficient in (a0 x0+a1 x1+a2 x2)^3
                # count permutations of multiset.
                inds=[i,j,k]
                mult=len(set(__import__('itertools').permutations(inds)))
                mons.append(coeff*mult*a[i]*a[j]*a[k])
    return mons

# pq^2 coefficient order: for each p row, q0^2, q0q1, q1^2.
def pq2_exprs(coeff=6):
    a=[a0,a1,a2]
    return [coeff*a[i]*b0*b0 if col==0 else coeff*a[i]*2*b0*b1 if col==1 else coeff*a[i]*b1*b1 for i in range(3) for col in range(3)]

def tail_data_for_variant(var,C,weights):
    l1=var['l1']; l2=var['l2']
    T1=qb.orbit_cube(l1,weights,P,4); T2=qb.orbit_cube(l2,weights,P,4)
    p3_idx=p3_indices(); pq_idx=pq2_indices()
    C3=[int(C[i])%P for i in p3_idx]; Cpq=[int(C[i])%P for i in pq_idx]
    T13=[int(T1[i])%P for i in p3_idx]; T23=[int(T2[i])%P for i in p3_idx]
    T1pq=[int(T1[i])%P for i in pq_idx]; T2pq=[int(T2[i])%P for i in pq_idx]
    return C3,Cpq,T13,T23,T1pq,T2pq

def groebner_empty_for_chart(C3,Cpq,T13,T23,T1pq,T2pq,chart_var):
    eqs=[]
    for val,t1,t2,expr in zip(Cpq,T1pq,T2pq,pq2_exprs(6)):
        eqs.append(int(val)-int(t1)*h1-int(t2)*h2-expr)
    for val,t1,t2,expr in zip(C3,T13,T23,p3_cube_exprs(2)):
        eqs.append(int(val)-int(t1)*h1-int(t2)*h2-expr)
    if chart_var=='b0':
        subs={b0:1}
        vars=[h1,h2,a0,a1,a2,b1]
    elif chart_var=='b1':
        subs={b1:1}
        vars=[h1,h2,a0,a1,a2,b0]
    else:
        raise ValueError(chart_var)
    eqs=[sp.Poly(e.subs(subs),*vars,modulus=P).as_expr() for e in eqs]
    try:
        G=sp.groebner(eqs,*vars,modulus=P,order='lex')
        empty=any(sp.Poly(g.as_expr(),*vars,modulus=P).total_degree()==0 and int(g.as_expr())%P!=0 for g in G.polys)
        degrees=[int(sp.Poly(g.as_expr(),*vars,modulus=P).total_degree()) for g in G.polys[:20]]
        return {'status':'ok','empty':bool(empty),'basis_size':len(G.polys),'basis_degrees_prefix':degrees}
    except Exception as exc:
        return {'status':'exception','empty':None,'error':repr(exc)}

def main():
    a0m,Q,Qi,mu,weights,diag_ok,ii=qb.q_basis(P); assert diag_ok
    sch=json.loads((WS/'data'/'ballard_z4_cyclic'/'ballard_z4_cyclic_scheme.json').read_text())
    T0_y=np.stack([qb.transform_stored_form_to_y(sch['free_orbit_representatives'][0][key],Q,Qi,P) for key in ['U','V','W']],axis=1)%P
    C=(qb.target_vec_short(P)-qb.free_contribution(T0_y,weights,P))%P
    variants=ta.extract_generic_variants(C,weights)
    # Many variants differ only by sign/order. Test all but stop if any chart is nonempty.
    records=[]
    for vi,var in enumerate(variants):
        C3,Cpq,T13,T23,T1pq,T2pq=tail_data_for_variant(var,C,weights)
        r0=groebner_empty_for_chart(C3,Cpq,T13,T23,T1pq,T2pq,'b0')
        r1=groebner_empty_for_chart(C3,Cpq,T13,T23,T1pq,T2pq,'b1')
        records.append({'variant_index':vi,'order':[int(x) for x in var['order']],'signs':[int(x) for x in var['signs']],'chart_b0_eq_1':r0,'chart_b1_eq_1':r1})
        print(f"variant {vi}: b0 empty={r0.get('empty')} status={r0.get('status')}; b1 empty={r1.get('empty')} status={r1.get('status')}",flush=True)
    all_empty=all(r['chart_b0_eq_1'].get('empty') is True and r['chart_b1_eq_1'].get('empty') is True for r in records)
    result={'prime':P,'scope':'BILR fixed residual, generic off-block variants, exact modular test of 4+4+2 tail as a single length-2 orbit','variant_count':len(variants),'all_charts_empty_for_all_variants':bool(all_empty),'records':records,'interpretation':'If all charts are empty, the BILR residual has no 4+4+2 tail in these generic variants over F_65521. This remains a fixed-residual control, not a six-parameter characteristic-zero family theorem.'}
    out=OUT/'bilr_tail442_groebner.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'out':str(out),'variant_count':len(variants),'all_empty':all_empty},indent=2))
if __name__=='__main__': main()
