#!/usr/bin/env python3
"""
analysis: exact PGL_3-invariant data for the rank-4 exterior fiber at the BILR point.

A pure cyclic free-orbit configuration is a 4-tuple of planes
  P_j = <u_j,v_j,w_j> in sl_3
with sum_j u_j ∧ v_j ∧ w_j = the Cartan trivector omega.  The analysis correction is
that mixed-trace injectivity is constant on the BILR component under internal
recombination/global adjoint motion, so sampling does not test other components.
The right instrument is exact invariant data of the plane configuration.

This script extracts, over Q:
  * trace-free plane bases and ranks;
  * the restricted determinant plane cubic det(x u + y v + z w);
  * the restricted Killing conic tr((x u + y v + z w)^2);
  * whether the plane is closed under commutator;
  * pairwise intersection dimensions;
  * the mixed-trace map Phi: direct sum Lambda^2(P_j) -> Lambda^2(sl_3) rank.

The output is a JSON file to be used as a component-classification reference, not as a
classification theorem by itself.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp

WS = Path(__file__).resolve().parent.parent
OUT_DIR = WS / "data" / "plane_invariants"
OUT_DIR.mkdir(parents=True, exist_ok=True)

# sl3 coordinate basis
sl3_off = [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]
sl3_labels = [f"E{i}{j}" for i,j in sl3_off] + ["H0","H1"]

def mat(M):
    return sp.Matrix([[sp.Rational(M[i][j]) for j in range(3)] for i in range(3)])

def tr(M):
    return sp.trace(M)

def tracefree(M):
    return sp.simplify(M - tr(M)/3 * sp.eye(3))

def sl3_coords(M):
    M = tracefree(M)
    coords = []
    for i,j in sl3_off:
        coords.append(sp.simplify(M[i,j]))
    # H0=E00-E11, H1=E11-E22; for trace-free diagonal, c_H0=d0, c_H1=-d2
    coords.append(sp.simplify(M[0,0]))
    coords.append(sp.simplify(-M[2,2]))
    # verify reconstruction
    R = sp.zeros(3,3)
    for coeff,(i,j) in zip(coords[:6], sl3_off):
        R[i,j] += coeff
    H0 = sp.diag(1,-1,0); H1 = sp.diag(0,1,-1)
    R += coords[6]*H0 + coords[7]*H1
    assert sp.simplify(R - M) == sp.zeros(3,3)
    return sp.Matrix(coords)

def wedge2(x,y):
    out=[]
    for i in range(8):
        for j in range(i+1,8):
            out.append(sp.simplify(x[i]*y[j]-x[j]*y[i]))
    return sp.Matrix(out)

def rank_cols(cols):
    if not cols:
        return 0
    return int(sp.Matrix.hstack(*cols).rank())

def in_span(v, cols):
    M = sp.Matrix.hstack(*cols)
    return int(M.rank()) == int(sp.Matrix.hstack(*cols, v).rank())

def comm(A,B):
    return sp.simplify(A*B - B*A)

def poly_coeff_dict(poly, vars):
    P = sp.Poly(sp.expand(poly), *vars, domain=sp.QQ)
    d = {}
    for monom, coeff in P.terms():
        if coeff:
            key = ''.join(f'{vars[i]}^{monom[i]}' for i in range(len(vars)) if monom[i]) or '1'
            d[key] = str(coeff)
    return d

def rat_str(x):
    x = sp.factor(sp.Rational(x)) if x.is_Rational else sp.factor(x)
    return str(x)

with open(WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json") as f:
    scheme = json.load(f)
reps = scheme["free_orbit_representatives"]

x,y,z = sp.symbols('x y z')
vars3=(x,y,z)
planes=[]
plane_coord_cols=[]
for j,rep in enumerate(reps):
    U = tracefree(mat(rep["U"]))
    V = tracefree(mat(rep["V"]))
    W = tracefree(mat(rep["W"]))
    mats=[U,V,W]
    coords=[sl3_coords(M) for M in mats]
    plane_coord_cols.append(coords)
    rankP = rank_cols(coords)
    X = x*U + y*V + z*W
    det_poly = sp.factor(X.det())
    kill_poly = sp.factor(sp.trace(X*X))
    kill_mat = sp.Matrix([[sp.trace(mats[a]*mats[b]) for b in range(3)] for a in range(3)])
    comm_records=[]
    closed=True
    for a in range(3):
        for b in range(a+1,3):
            cvec=sl3_coords(comm(mats[a],mats[b]))
            inside=in_span(cvec, coords)
            closed = closed and inside
            comm_records.append({"pair":[a,b],"inside_plane":bool(inside),"coords":[rat_str(cvec[i]) for i in range(8)]})
    # singularity witness for determinant cubic: solve partials + cubic in affine charts quickly.
    partials=[sp.diff(det_poly,v) for v in vars3]
    singular_origin_only = None
    try:
        # homogeneous cubic is smooth iff ideal of partials has no nonzero projective point.
        # Check three affine charts x=1,y=1,z=1 by Groebner basis containing 1.
        chart_empty=[]
        for var in vars3:
            subs={var:1}
            remaining=[u for u in vars3 if u != var]
            Gbasis=sp.groebner([p.subs(subs) for p in partials], *remaining, domain=sp.QQ)
            chart_empty.append(bool(1 in Gbasis.polys or Gbasis.reduce(1)[1] == 0))
        # groebner reduce(1)==0 means 1 in ideal.  If all charts empty, no nonzero singular point.
        singular_origin_only = all(chart_empty)
    except Exception as e:
        singular_origin_only = f"not_computed:{type(e).__name__}"
    planes.append({
        "plane_index": j,
        "rank": rankP,
        "basis_matrix_entries_tracefree": [[[rat_str(M[a,b]) for b in range(3)] for a in range(3)] for M in mats],
        "basis_sl3_coords_columns": [[rat_str(coords[col][r]) for r in range(8)] for col in range(3)],
        "determinant_cubic_factor": str(det_poly),
        "determinant_cubic_coefficients": poly_coeff_dict(det_poly, vars3),
        "killing_conic_factor": str(kill_poly),
        "killing_conic_matrix": [[rat_str(kill_mat[a,b]) for b in range(3)] for a in range(3)],
        "killing_conic_det": rat_str(kill_mat.det()),
        "commutator_closed_subalgebra": bool(closed),
        "commutators": comm_records,
        "det_cubic_smooth_projective_by_partial_charts": singular_origin_only,
    })

# Pairwise intersections.
pairwise=[]
for i in range(4):
    for j in range(i+1,4):
        ri=rank_cols(plane_coord_cols[i]); rj=rank_cols(plane_coord_cols[j])
        rsum=rank_cols(plane_coord_cols[i]+plane_coord_cols[j])
        pairwise.append({"pair":[i,j],"intersection_dim":int(ri+rj-rsum),"sum_rank":int(rsum)})

# Mixed-trace map columns for each plane: v∧w, w∧u, u∧v.
phi_cols=[]
for coords in plane_coord_cols:
    u,v,w=coords
    phi_cols.extend([wedge2(v,w), wedge2(w,u), wedge2(u,v)])
Phi=sp.Matrix.hstack(*phi_cols)
phi_rank=int(Phi.rank())
phi_kernel=Phi.nullspace()

# Cartan/exterior sum vector for reference.
def wedge3(a,b,c):
    out=[]
    for i in range(8):
        for j in range(i+1,8):
            for k in range(j+1,8):
                out.append(sp.simplify(
                    a[i]*(b[j]*c[k]-b[k]*c[j])
                    - a[j]*(b[i]*c[k]-b[k]*c[i])
                    + a[k]*(b[i]*c[j]-b[j]*c[i])
                ))
    return sp.Matrix(out)
Omega=sum((wedge3(*cols) for cols in plane_coord_cols), sp.zeros(56,1))

results={
    "scope":"Exact invariant data for the BILR rank-4 exterior plane configuration; not a component classification theorem.",
    "sl3_basis":sl3_labels,
    "planes":planes,
    "pairwise_intersections":pairwise,
    "mixed_trace_map_rank":phi_rank,
    "mixed_trace_domain_dim":12,
    "mixed_trace_injective": bool(phi_rank==12),
    "mixed_trace_kernel_dim": int(12-phi_rank),
    "mixed_trace_kernel_basis": [[rat_str(v[i]) for i in range(v.rows)] for v in phi_kernel],
    "exterior_sum_nonzero_coordinates": int(sum(1 for val in Omega if val!=0)),
    "exterior_sum_vector_lambda3_sl3_basis": [rat_str(Omega[i]) for i in range(56)],
    "interpretation":"At the BILR component, internal SL3 recombination keeps each plane fixed and global adjoint moves all planes by PGL3, so Phi rank 12 is an exact component-local statement. Other rank-4 exterior components require comparison by the plane invariants above.",
}

out=OUT_DIR/"bilr_plane_invariants.json"
with open(out,'w') as f:
    json.dump(results,f,indent=2)
print(json.dumps({
    "out":str(out),
    "plane_ranks":[p["rank"] for p in planes],
    "det_cubic_factors":[p["determinant_cubic_factor"] for p in planes],
    "killing_conic_dets":[p["killing_conic_det"] for p in planes],
    "subalgebra_flags":[p["commutator_closed_subalgebra"] for p in planes],
    "pairwise_intersections":pairwise,
    "mixed_trace_rank":phi_rank,
    "mixed_trace_injective":phi_rank==12,
},indent=2))
