#!/usr/bin/env python3
"""Compute residual-cubic Koszul--Young ranks for analysis symmetry-section points.

For each extracted F_5 exterior one-orbit solution, choose the determinant scale that
makes the four-orbit exterior sum equal omega/3, form

  R = tr(X^3) - 3 * sum_{h in H} (hU)(hV)(hW)

as a commutative cubic in the 9 gl_3 variables, and compute the p-modular
Koszul--Young flattening rank.  Rank > 700 certifies Waring rank > 10 for that
finite-field residual; rank <= 700 is a candidate signal needing reconstruction.
"""
from __future__ import annotations
import argparse, importlib.util, itertools, json, sys, time
from pathlib import Path
import numpy as np

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'exterior_linear_sections'
# import analysis linear-section functions
spec=importlib.util.spec_from_file_location('s57', WS/'scripts'/'invariant_linear_section.py')
s57=importlib.util.module_from_spec(spec); spec.loader.exec_module(s57)  # type: ignore
# import BILR KY machinery
sys.path.insert(0,str(WS/'scripts'))
import ballard_z4_cyclic_scheme as bilr  # type: ignore

p_default=5

def sl_to_gl9(c,p):
    # c in E01,E02,E10,E12,E20,E21,H0,H1 coordinates.
    return [c[6]%p,c[0]%p,c[1]%p,c[2]%p,(-c[6]+c[7])%p,c[3]%p,c[4]%p,c[5]%p,(-c[7])%p]

def chart_cols_from_vals(pivot, vals, p):
    nonpiv=[j for j in range(8) if j not in pivot]
    B=[[0]*8 for _ in range(3)]
    for r,c in enumerate(pivot): B[r][c]=1
    it=iter(vals)
    for c in nonpiv:
        for r in range(3): B[r][c]=next(it)%p
    return [[B[r][c] for c in range(8)] for r in range(3)]

def setup_family(family,p,pivot):
    gens_ad,_=s57.group_ad_generators(family,p)
    E,weights=s57.simultaneous_eigenbasis(gens_ad,family,p)
    Einv=s57.mat_inv(E,p)
    L=s57.lambda3_matrix(E,p)
    target_new=s57.solve_square(L,s57.target_old(p),p)
    Gnew=[s57.mat_mul(s57.mat_mul(Einv,A,p),E,p) for A in gens_ad]
    if family.startswith('c4'):
        ops=[s57.mat_pow(Gnew[0],k,p) for k in range(4)]
    else:
        ops=[s57.mat_mul(s57.mat_pow(Gnew[0],a,p),s57.mat_pow(Gnew[1],b,p),p) for a in range(2) for b in range(2)]
    scale=(target_new[s57.TIDX[pivot]]%p)*s57.inv_mod(len(ops),p)%p
    return E,ops,scale,target_new

def residual_coeffs_for_point(family,p,pivot,vals):
    E,ops,scale,target_new=setup_family(family,p,pivot)
    coeff={tuple(k):v%p for k,v in bilr.target_trM3_coeffs().items()}
    cols_new=chart_cols_from_vals(pivot,vals,p)
    for Op in ops:
        cols_old=[]
        for c in cols_new:
            cn=s57.mat_vec(Op,c,p)
            co=s57.mat_vec(E,cn,p)
            cols_old.append(sl_to_gl9(co,p))
        U,V,W=cols_old
        U=[(scale*x)%p for x in U]
        factor=3%p
        for i,j,k in itertools.product(range(9), repeat=3):
            val=(factor*U[i]*V[j]*W[k])%p
            if val:
                key=tuple(sorted((i,j,k)))
                coeff[key]=(coeff.get(key,0)-val)%p
    return {k:(v%p) for k,v in coeff.items() if v%p}

def rank_for_coeffs(coeff,p):
    # Convert coefficients to small signed integers; bilr KY scales by 6 internally.
    signed={k:(v if v<=p//2 else v-p) for k,v in coeff.items()}
    K=bilr.koszul_matrix_from_coeffs(signed,p=4)
    return int(bilr.rank_mod_np(K,p))

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--prime',type=int,default=5)
    ap.add_argument('--families',default='c4_regular,klein_diag')
    ap.add_argument('--max-points',type=int,default=0,help='0 means all')
    args=ap.parse_args()
    p=args.prime
    data=json.loads((OUT/'f5_extracted_symmetry_points.json').read_text())
    result={'prime':p,'families':{},'interpretation':'KY rank >700 excludes Waring rank <=10 for that residual over this finite field; finite-field points need not lift to characteristic zero.'}
    for fam in [x.strip() for x in args.families.split(',') if x.strip()]:
        rec=data[fam]
        pivot=tuple(rec['pivot'])
        pts=rec['records']
        if args.max_points: pts=pts[:args.max_points]
        ranks=[]; examples=[]; t0=time.time()
        for idx,pt in enumerate(pts):
            coeff=residual_coeffs_for_point(fam,p,pivot,pt['vals'])
            rk=rank_for_coeffs(coeff,p)
            ranks.append(rk)
            if len(examples)<5 or rk<=700:
                examples.append({'index':idx,'rank':rk,'nonzero_coeffs':len(coeff),'phi_rank':pt['phi_rank'],'vals':pt['vals']})
            print(f'{fam} point {idx}/{len(pts)} KY_rank={rk}', flush=True)
        hist={str(r):ranks.count(r) for r in sorted(set(ranks))}
        result['families'][fam]={'pivot':list(pivot),'points_tested':len(pts),'rank_histogram':hist,'min_rank':min(ranks) if ranks else None,'max_rank':max(ranks) if ranks else None,'candidate_rank_le_700_count':sum(1 for r in ranks if r<=700),'examples':examples,'elapsed_sec':round(time.time()-t0,3)}
    path=OUT/f'f5_symmetry_residual_koszul_ranks_{"_".join(result["families"].keys())}.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
    print('SAVED',path)
if __name__=='__main__': main()
