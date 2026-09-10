#!/usr/bin/env python3
"""
analysis: exact cubic residual control for the trace-moment instrument.

For a traceless pure cyclic decomposition, after the lower trace moments are separated,
the remaining sl_3 cubic equation is

  tr(X0^3) - 3*sum_j lambda_Uj(X0) lambda_Vj(X0) lambda_Wj(X0)
    = sum_i w_i mu_i(X0)^3 + sum_{invisible cubes} lambda_i(X0)^3,

where c_i=tr(L_i), mu_i=lambda_i/c_i, w_i=c_i^3 for active cubes.

This script verifies this normalized cubic identity for the exact BILR 11-cube/4-orbit
positive control over Z.  It also records the polynomial support of the residual that
a hypothetical (10,4) cubature must match.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp

WS = Path(__file__).resolve().parent.parent
OUT_DIR = WS / "data" / "moment_cubature"
OUT_DIR.mkdir(parents=True, exist_ok=True)

sl3_off=[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]
sl3_labels=[f"E{i}{j}" for i,j in sl3_off]+["H0","H1"]
xs=sp.symbols('x0:8')

def basis_matrix(k):
    M=sp.zeros(3,3)
    if k<6:
        i,j=sl3_off[k]; M[i,j]=1
    elif k==6:
        M[0,0]=1; M[1,1]=-1
    else:
        M[1,1]=1; M[2,2]=-1
    return M
basis=[basis_matrix(k) for k in range(8)]
X=sum((xs[k]*basis[k] for k in range(8)), sp.zeros(3,3))
target=sp.expand(sp.trace(X**3))

def mat(M): return sp.Matrix([[sp.Integer(M[i][j]) for j in range(3)] for i in range(3)])
def tracefree(M): return sp.simplify(M - sp.trace(M)/3*sp.eye(3))
def linear_form_from_stored_L(L):
    L=mat(L)
    return sp.expand(sum(L[j,i]*X[i,j] for i in range(3) for j in range(3)))
def linear_form_from_matrix_A(A):
    # A is an ordinary matrix in tr(A^T X) convention, matching stored free reps.
    return sp.expand(sum(A[j,i]*X[i,j] for i in range(3) for j in range(3)))

def poly_terms(poly):
    P=sp.Poly(sp.expand(poly), *xs, domain=sp.QQ)
    return {monom: coeff for monom,coeff in P.terms() if coeff}

def digest_terms(poly):
    terms=poly_terms(poly)
    out=[]
    for monom,coeff in sorted(terms.items()):
        out.append({"monom":list(monom),"coeff":str(coeff)})
    return out

with open(WS/"data"/"ballard_z4_cyclic"/"ballard_z4_cyclic_scheme.json") as f:
    scheme=json.load(f)

cube_poly=0
nodes=[]
for idx,L in enumerate(scheme["cubes"]):
    Lm=mat(L)
    c=sp.trace(Lm)
    lam=linear_form_from_stored_L(L)
    assert c != 0
    mu=sp.expand(lam/c)
    w=c**3
    cube_poly += w*mu**3
    nodes.append({"idx":idx,"c":int(c),"w":int(w),"lambda":str(lam),"mu":str(mu)})
cube_poly=sp.expand(cube_poly)

free_poly=0
free_records=[]
for j,rep in enumerate(scheme["free_orbit_representatives"]):
    U=tracefree(mat(rep["U"])); V=tracefree(mat(rep["V"])); W=tracefree(mat(rep["W"]))
    # Free reps are stored in the same tr(L^T X) convention.
    lU=linear_form_from_matrix_A(U); lV=linear_form_from_matrix_A(V); lW=linear_form_from_matrix_A(W)
    free_poly += lU*lV*lW
    free_records.append({"j":j,"lambda_U":str(lU),"lambda_V":str(lV),"lambda_W":str(lW)})
free_poly=sp.expand(free_poly)
residual=sp.expand(target - 3*free_poly)
diff=sp.expand(residual - cube_poly)

# Symmetric coefficient vector sizes.
monoms=list(sp.polys.monomials.itermonomials(xs,3))
# Keep exactly degree 3 monomials in deterministic lex order by exponent tuple.
monom_exp=[]
for m in monoms:
    P=sp.Poly(m,*xs)
    exp=P.monoms()[0]
    if sum(exp)==3:
        monom_exp.append(exp)
monom_exp=sorted(set(monom_exp), reverse=True)

def coeff_vector(poly):
    P=sp.Poly(sp.expand(poly),*xs,domain=sp.QQ)
    return [P.coeff_monomial(exp) for exp in monom_exp]

vec_target=coeff_vector(target)
vec_free=coeff_vector(3*free_poly)
vec_resid=coeff_vector(residual)
vec_cube=coeff_vector(cube_poly)

results={
    "scope":"Exact Z verification of the normalized sl3 cubic residual for the BILR pure cyclic control.",
    "sl3_basis":sl3_labels,
    "degree3_monomial_count":len(monom_exp),
    "target_nonzero_terms":sum(1 for c in vec_target if c!=0),
    "free_part_nonzero_terms":sum(1 for c in vec_free if c!=0),
    "residual_nonzero_terms":sum(1 for c in vec_resid if c!=0),
    "cube_part_nonzero_terms":sum(1 for c in vec_cube if c!=0),
    "identity_residual_equals_11_active_cubes": bool(diff==0),
    "max_abs_residual_coeff": str(max(abs(c) for c in vec_resid)),
    "nodes":nodes,
    "free_orbits":free_records,
    "residual_terms": digest_terms(residual),
    "interpretation":"Any traceless (10,4) solution must satisfy the lower moment equations and then match this type of cubic residual, with only ten cube slots: k=10 active, or k=9 active plus one trace-zero/invisible cube. The BILR identity is an 11-active-node positive control, not a rank-22 solution.",
}

out=OUT_DIR/"cubic_residual_control.json"
with open(out,'w') as f: json.dump(results,f,indent=2)
print(json.dumps({
    "out":str(out),
    "identity_ok":results["identity_residual_equals_11_active_cubes"],
    "degree3_monomial_count":len(monom_exp),
    "residual_nonzero_terms":results["residual_nonzero_terms"],
    "cube_nonzero_terms":results["cube_part_nonzero_terms"],
},indent=2))
