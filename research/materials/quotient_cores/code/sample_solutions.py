#!/usr/bin/env python3
"""Randomly sample points on analysis finite-symmetry linear sections and test plane invariants."""
from __future__ import annotations
import argparse, importlib.util, itertools, json, random
from pathlib import Path

WS=Path(__file__).resolve().parent.parent
spec=importlib.util.spec_from_file_location('s57', WS/'scripts'/'invariant_linear_section.py')
s57=importlib.util.module_from_spec(spec); spec.loader.exec_module(s57)  # type: ignore
OUT=WS/'data'/'exterior_linear_sections'

PAIRS=list(itertools.combinations(range(8),2))

def wedge2(u,v,p): return [(u[i]*v[j]-u[j]*v[i])%p for i,j in PAIRS]

def phi_rank_from_planes(planes,p):
    cols=[]
    for U,V,W in planes:
        cols.extend([wedge2(V,W,p), wedge2(W,U,p), wedge2(U,V,p)])
    return s57.rank_mod(s57.mat_trans(cols),p)

def orbit_planes_from_pvec(pvec, Lams, p):
    # This cannot reconstruct planes. Use point basis instead.
    raise NotImplementedError

def chart_cols_from_vals(pivot, vals, p):
    nonpiv=[j for j in range(8) if j not in pivot]
    cols=[[0]*8 for _ in range(3)]
    for r,c in enumerate(pivot): cols[r][c]=1
    it=iter(vals)
    for c in nonpiv:
        for r in range(3): cols[r][c]=next(it)%p
    # return three column vectors in eigenbasis coordinates
    return [[cols[r][c] for c in range(8)] for r in range(3)]

def eval_poly(poly, vals, p):
    s=0
    for mon,c in poly.items():
        term=c%p
        for val,e in zip(vals,mon):
            if e: term=(term*pow(val,e,p))%p
        s=(s+term)%p
    return s

def equations_for(family,p,pivot):
    gens_ad,_=s57.group_ad_generators(family,p)
    E,weights=s57.simultaneous_eigenbasis(gens_ad,family,p)
    Einv=s57.mat_inv(E,p)
    L=s57.lambda3_matrix(E,p)
    target_new=s57.solve_square(L,s57.target_old(p),p)
    inv_tr=s57.invariant_triples(weights,family)
    polys,_=s57.chart_plucker_polys(pivot,p)
    tp=target_new[s57.TIDX[pivot]]%p
    eqs=[]
    for tri in inv_tr:
        if tri==pivot: continue
        idx=s57.TIDX[tri]
        eq=s57.poly_sub(s57.poly_scalar(polys[idx],tp,p), s57.poly_const(target_new[idx]%p,15,p), p)
        if eq: eqs.append(eq)
    return eqs,E,Einv,target_new,inv_tr

def mat_vec(A,x,p): return s57.mat_vec(A,x,p)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--prime',type=int,default=5)
    ap.add_argument('--family',required=True)
    ap.add_argument('--pivot',required=True)
    ap.add_argument('--samples',type=int,default=200000)
    ap.add_argument('--seed',type=int,default=5701)
    args=ap.parse_args()
    p=args.prime; pivot=tuple(int(x) for x in args.pivot.split(',')); random.seed(args.seed)
    eqs,E,Einv,target_new,inv_tr=equations_for(args.family,p,pivot)
    gens_ad,_=s57.group_ad_generators(args.family,p)
    # Group matrices in eigenbasis for orbit generation.
    E_inv=s57.mat_inv(E,p)
    Gnew=[s57.mat_mul(s57.mat_mul(E_inv,A,p),E,p) for A in gens_ad]
    if args.family.startswith('c4'):
        orbit_ops=[s57.mat_pow(Gnew[0],k,p) for k in range(4)]
    else:
        orbit_ops=[s57.mat_mul(s57.mat_pow(Gnew[0],a,p),s57.mat_pow(Gnew[1],b,p),p) for a in range(2) for b in range(2)]
    hits=[]; phi_ranks=[]
    for t in range(args.samples):
        vals=[random.randrange(p) for _ in range(15)]
        if all(eval_poly(e,vals,p)==0 for e in eqs):
            cols=chart_cols_from_vals(pivot,vals,p)
            # orbit planes in eigenbasis
            planes=[]
            for Op in orbit_ops:
                planes.append([mat_vec(Op,c,p) for c in cols])
            phir=phi_rank_from_planes(planes,p)
            pvec=s57.wedge3_cols(cols,p)
            hits.append({'vals':vals,'phi_rank':phir,'plucker_nonzero':sum(1 for x in pvec if x%p)})
            phi_ranks.append(phir)
            if len(hits)>=20: break
    out={'family':args.family,'prime':p,'pivot':list(pivot),'samples':args.samples,'hits_found':len(hits),'hit_rate_estimate':len(hits)/args.samples,'phi_rank_histogram':{str(r):phi_ranks.count(r) for r in sorted(set(phi_ranks))},'hits':hits}
    outpath=OUT/f'sampled_{args.family}_p{p}_{"".join(map(str,pivot))}.json'
    outpath.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
    print('SAVED',outpath)
if __name__=='__main__': main()
