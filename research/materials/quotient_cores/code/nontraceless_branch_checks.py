#!/usr/bin/env python3
"""
analysis: exact algebra for the non-traceless pure-cyclic branch.

Purpose:
  Protect the trace-graded cyclic theorem from an invalid extension to m>=5.
  The free-orbit traces enter the s-linear, s^2, s^3 equations.  A single orbit
  contributes
      q = a*lambda_V*lambda_W + b*lambda_W*lambda_U + d*lambda_U*lambda_V
  to the s-linear quadratic on sl_3.  In formal independent orbit coordinates the
  symmetric matrix is hollow and has rank 0,2,or 3 in characteristic zero, never
  rank 1; after pullback to sl_3, dependent triples may lower the rank to 1.

The script also constructs an exact dependent-traceless-part orbit: w=u+v, so the
trivector u∧v∧w vanishes and the mixed-trace equation has a two-parameter family
of nonzero traces.  Its q is generically rank 2.  Therefore adding such an orbit
can destroy the f>=8 rank contradiction for the (f,m)=(7,5) skeleton, so the
m>=5 cases remain mathematically open until the full mixed-trace plus s^2,s^3
system is handled.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp

WS=Path(__file__).resolve().parent.parent
OUT_DIR=WS/"data"/"moment_cubature"
OUT_DIR.mkdir(parents=True,exist_ok=True)

# General q_j in coordinates X=lambda_U, Y=lambda_V, Z=lambda_W.
X,Y,Z,a,b,d=sp.symbols('X Y Z a b d')
q=a*Y*Z + b*Z*X + d*X*Y
M=sp.Matrix([[0,d/2,b/2],[d/2,0,a/2],[b/2,a/2,0]])
M2=sp.Matrix([[0,d,b],[d,0,a],[b,a,0]])  # twice M; same rank in char != 2.

det_M2=sp.factor(M2.det())
rank_cases=[]
for vals,name in [
    ({a:0,b:0,d:0},"all_zero"),
    ({a:1,b:0,d:0},"one_nonzero"),
    ({a:1,b:2,d:0},"two_nonzero"),
    ({a:1,b:2,d:3},"three_nonzero"),
]:
    rank_cases.append({"case":name,"matrix_2q":str(M2.subs(vals)),"rank":int(M2.subs(vals).rank()),"q":str(q.subs(vals))})

# Dependent traceless parts: W=U+V.  The free trivector is zero, but mixed trace can vanish
# with d=a+b.
U,V=sp.symbols('U V')
W=U+V
q_dep=sp.expand(a*V*W + b*W*U + (a+b)*U*V)
M_dep=sp.hessian(q_dep,(U,V))/2  # symmetric matrix for q_dep
rank_dep_generic_det=sp.factor(M_dep.det())
example_dep={a:1,b:2}
q_dep_ex=sp.expand(q_dep.subs(example_dep))
M_dep_ex=sp.Matrix(M_dep.subs(example_dep))

# Mixed-trace relation for W=U+V:
# V∧W=-U∧V, W∧U=-U∧V, U∧V=U∧V, so (-a-b+d) U∧V=0 -> d=a+b.
mixed_relation="For W=U+V, V∧W=-U∧V and W∧U=-U∧V, so a(V∧W)+b(W∧U)+d(U∧V)=0 iff d=a+b."

# General nonzero-trace moment equations for a pure cyclic decomposition in X0+sI.
s1="tr(X0^2) = sum_i c_i lambda_i^2 + sum_j (a_j lambda_Vj lambda_Wj + b_j lambda_Wj lambda_Uj + d_j lambda_Uj lambda_Vj)"
s2="0 = sum_i c_i^2 lambda_i + sum_j (a_j*b_j lambda_Wj + a_j*d_j lambda_Vj + b_j*d_j lambda_Uj)"
s3="3 = sum_i c_i^3 + 3*sum_j a_j*b_j*d_j"

results={
    "scope":"Exact characteristic-zero algebra showing why the trace-graded f>=8 argument is conditional on ker(Phi)=0/traceless free orbits.",
    "q_single_orbit":"a*Y*Z + b*Z*X + d*X*Y",
    "two_times_symmetric_matrix":str(M2),
    "two_times_matrix_determinant":str(det_M2),
    "rank_consequence":"In formal independent coordinates (lambda_U,lambda_V,lambda_W), over characteristic zero a nonzero single-orbit q has rank 2 if a*b*d=0 and at least one coefficient is nonzero, and rank 3 if a*b*d is nonzero; rank 1 never occurs before pullback. After pullback to sl_3, dependent triples can lower the rank to 1.",
    "rank_cases":rank_cases,
    "dependent_orbit_branch":{
        "traceless_relation":"W=U+V, hence U∧V∧W=0 and the orbit adds no Cartan/exterior volume.",
        "mixed_trace_relation":mixed_relation,
        "trace_solution_family":"(a,b,d)=(a,b,a+b), two parameters; nonzero traces may remain even though the mixed-trace equation is satisfied by this orbit alone.",
        "q_after_relation":str(q_dep),
        "q_matrix":str(M_dep),
        "q_matrix_det":str(rank_dep_generic_det),
        "generic_rank":"2 unless a^2+a*b+b^2=0; for example a=1,b=2 has rank 2 over Q.",
        "example_a1_b2_q":str(q_dep_ex),
        "example_a1_b2_matrix":str(M_dep_ex),
        "example_a1_b2_rank":int(M_dep_ex.rank()),
    },
    "nonzero_trace_moment_equations":{"s1":s1,"s2":s2,"s3":s3},
    "skeleton_budget_correction":"For m=5,6,7 the cube counts f=7,4,1 can only be contradicted by the s-linear rank after proving rank(sum_j q_j) is <1,<4,<7 respectively. Dependent-orbit branches can give rank-2 contributions, and further pullback degeneracies can even produce rank 1, so the earlier extension beyond the traceless case is not justified.",
    "interpretation":"The established cyclic theorem is: m>=4 unconditionally from the Cartan exterior rank argument, and m<=4 only under the explicit mixed-trace injectivity/tracelessness hypothesis. The m>=5 pure cyclic skeletons require a separate exact treatment of decomposable-bivector relations together with the s2 and s3 equations.",
}

out=OUT_DIR/"nontraceless_branch_algebra.json"
with open(out,'w') as f: json.dump(results,f,indent=2)
print(json.dumps({
    "out":str(out),
    "det_2q":str(det_M2),
    "single_orbit_rank_cases":rank_cases,
    "dependent_example_rank":int(M_dep_ex.rank()),
    "dependent_example_q":str(q_dep_ex),
},indent=2))
