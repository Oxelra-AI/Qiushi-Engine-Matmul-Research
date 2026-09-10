#!/usr/bin/env python3
"""Extract F_5 points from the analysis C4/Klein exterior linear sections.

The lex Groebner bases with field equations show 32 F_5 points in the selected
c4_regular and klein_diag Pluecker charts.  This script uses the triangular bases,
verifies the original invariant Pluecker equations, then computes orbit-plane
geometry and the mixed-independent-verification-record rank for each extracted point.
"""
from __future__ import annotations
import importlib.util, itertools, json
from pathlib import Path

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'exterior_linear_sections'
spec=importlib.util.spec_from_file_location('s57', WS/'scripts'/'invariant_linear_section.py')
s57=importlib.util.module_from_spec(spec); spec.loader.exec_module(s57)  # type: ignore
p=5
PAIRS=list(itertools.combinations(range(8),2))

def mod(x): return x%p

def eval_poly(poly, vals):
    s=0
    for mon,c in poly.items():
        term=c%p
        for val,e in zip(vals,mon):
            if e: term=(term*pow(val,e,p))%p
        s=(s+term)%p
    return s%p

def equations_for(family,pivot):
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
    Gnew=[]
    E_inv=s57.mat_inv(E,p)
    for A in gens_ad:
        Gnew.append(s57.mat_mul(s57.mat_mul(E_inv,A,p),E,p))
    if family.startswith('c4'):
        orbit_ops=[s57.mat_pow(Gnew[0],k,p) for k in range(4)]
    else:
        orbit_ops=[s57.mat_mul(s57.mat_pow(Gnew[0],a,p),s57.mat_pow(Gnew[1],b,p),p) for a in range(2) for b in range(2)]
    return eqs, orbit_ops, target_new, inv_tr

def chart_cols_from_vals(pivot, vals):
    nonpiv=[j for j in range(8) if j not in pivot]
    B=[[0]*8 for _ in range(3)]
    for r,c in enumerate(pivot): B[r][c]=1
    it=iter(vals)
    for c in nonpiv:
        for r in range(3): B[r][c]=next(it)%p
    return [[B[r][c] for c in range(8)] for r in range(3)]

def wedge2(u,v): return [(u[i]*v[j]-u[j]*v[i])%p for i,j in PAIRS]

def phi_rank(planes):
    cols=[]
    for U,V,W in planes:
        cols.extend([wedge2(V,W),wedge2(W,U),wedge2(U,V)])
    return s57.rank_mod(s57.mat_trans(cols),p)

def plane_key(cols):
    R,piv=s57.rref_mod([c[:] for c in cols],p)
    nz=[tuple(row) for row in R if any(x%p for x in row)]
    return tuple(nz)

def orbit_geometry(cols, orbit_ops):
    planes=[]
    for Op in orbit_ops:
        planes.append([s57.mat_vec(Op,c,p) for c in cols])
    ranks=[s57.rank_mod(pl,p) for pl in planes]
    keys=[plane_key(pl) for pl in planes]
    distinct=len(set(keys))
    intersections=[]
    for i,j in itertools.combinations(range(len(planes)),2):
        ri=s57.rank_mod(planes[i],p); rj=s57.rank_mod(planes[j],p)
        rsum=s57.rank_mod(planes[i]+planes[j],p)
        intersections.append(ri+rj-rsum)
    return planes, {'plane_ranks':ranks,'distinct_planes':distinct,'pairwise_intersection_dims':intersections,'phi_rank':phi_rank(planes)}

def solve_c4_regular():
    sols=[]
    for x10,x11,x12,x13 in itertools.product(range(p), repeat=4):
        if (x13**4-1)%p: continue
        if (x12**4-1)%p: continue
        g4=(x11*x13**2-x11-x12*x13**2+x12)%p
        g5=(x11**2-2*x12**2*x13**2+2*x12**2+2*x13**3+2*x13)%p
        g6=(x10*x13**2+x10-2*x11*x13-2*x12**3*x13**2-2*x12**3+2*x12*x13)%p
        g7=(x10*x11-x10*x12-2*x11*x12**3+2*x11*x12*x13-2*x12**2*x13**3+x12**2*x13+2*x13**2-1)%p
        g8=(x10**2-2*x10*x12*x13+x11*x12**3*x13-x11*x12+2*x12**2*x13**2+x12**2-x13**3-2*x13)%p
        if any([g4,g5,g6,g7,g8]): continue
        vals=[0]*15
        vals[14]=0; vals[13]=x13; vals[12]=x12; vals[11]=x11; vals[10]=x10
        vals[9]=-(x10*x12*x13-2*x11*x12+2*x12**2-2*x13)
        vals[8]=-(x10*x12**2+2*x10*x13-x11*x12**2*x13-2*x11+x12**3*x13**3+x12**3*x13+2*x12*x13**2+x12)
        vals[7]=-(x10*x12**2*x13-2*x10+x11*x12**2+x11*x13-2*x12**3*x13**2+2*x12**3-2*x12*x13**3+x12*x13)
        vals[6]=-(x10*x12**3+2*x10*x12*x13+x11*x12**3*x13+2*x11*x12-2*x12**2*x13**2-2*x13)
        vals[5]=2*x13**3
        vals[4]=-1
        vals[3]=-(2*x10+2*x11*x12**2+2*x11*x13-x12**3*x13**2+2*x12**3+x12*x13**3-x12*x13)
        vals[2]=x12**3
        vals[1]=-(x10*x12**2+2*x11*x12**2*x13-x11+2*x12**3*x13**3-2*x12**3*x13+x12*x13**2+2*x12)
        vals[0]=1
        sols.append([v%p for v in vals])
    return sols

def solve_klein():
    sols=[]
    for x9,x11,x12,x13 in itertools.product(range(p), repeat=4):
        cons=[x13**5-x13, x12*x13, x12**4+x13**4-1, x11*x13, x11**4+x13**4-1, x9*x13**4-x9, x9*x12, x9*x11, x9**4-x13**4]
        if any(c%p for c in cons): continue
        vals=[0]*15
        vals[14]=0; vals[13]=x13; vals[12]=x12; vals[11]=x11; vals[10]=0; vals[9]=x9
        vals[8]=-(x9**3*x13**3)
        vals[7]=-(x11**3*x12**3)
        vals[6]=0
        vals[5]=x9**3-x11*x12
        vals[4]=x9*x13
        vals[3]=-(x11**3)
        vals[2]=x9**3
        vals[1]=x12**3
        vals[0]=-(x11**3+x13**3)
        sols.append([v%p for v in vals])
    return sols

def analyze_family(family,pivot,sols):
    eqs,ops,target_new,inv_tr=equations_for(family,pivot)
    records=[]
    bad=0
    for vals in sols:
        errs=[eval_poly(e,vals) for e in eqs]
        if any(errs): bad+=1
        cols=chart_cols_from_vals(pivot,vals)
        planes,geom=orbit_geometry(cols,ops)
        pvec=s57.wedge3_cols(cols,p)
        records.append({'vals':vals,'plucker_nonzero':sum(1 for z in pvec if z%p),'max_equation_error':max(errs) if errs else 0,**geom})
    hist={}
    for r in records:
        key=(r['phi_rank'],r['distinct_planes'],tuple(sorted(r['pairwise_intersection_dims'])))
        hist[str(key)]=hist.get(str(key),0)+1
    return {'family':family,'pivot':list(pivot),'solution_count':len(sols),'bad_original_equation_solutions':bad,'geometry_histogram':hist,'records':records}

def main():
    out={'prime':p,'source':'extracted from triangular lex Groebner bases with field equations for selected target-nonzero charts'}
    out['c4_regular']=analyze_family('c4_regular',(0,2,7),solve_c4_regular())
    out['klein_diag']=analyze_family('klein_diag',(2,5,6),solve_klein())
    path=OUT/'f5_extracted_symmetry_points.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k in ['prime','source']},indent=2))
    for fam in ['c4_regular','klein_diag']:
        rec=out[fam]
        print(fam, 'solutions', rec['solution_count'], 'bad', rec['bad_original_equation_solutions'])
        print(json.dumps(rec['geometry_histogram'],indent=2,sort_keys=True))
    print('SAVED',path)
if __name__=='__main__': main()
