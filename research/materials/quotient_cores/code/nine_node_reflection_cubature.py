#!/usr/bin/env python3
"""
analysis: explicit 9-node rational cubature for the first three trace moments.

This complements moment_cubature_instrument.py, whose simple diagonal-square
search did not find a certificate.  The construction is the rational reflection
certificate suggested by the analysis verification review:

  D = diag(1,1,1,1,1,1,-1,-1,-1), 1=(1,...,1), g=e4+e5+e6.
  The D-norms of 1 and g are both 3.  Let S=-r_{1+g}; then S is a D-isometry
  and S(1)=g.  Choose z_0,...,z_7 in g^perp whose D-Gram matrix is the trace
  form K on sl_3.  Then B=[S z_0 ... S z_7] has 1^T D B=0 and B^T D B=K.

Rows of B are mu_i; weights are the diagonal entries of D.  Hence
  sum w_i=3, sum w_i mu_i=0, sum w_i mu_i mu_i^T=K.
This shows the first three trace moments alone do not exclude 9 active nodes.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'moment_cubature'
OUT.mkdir(parents=True, exist_ok=True)

weights=[sp.Integer(1)]*6+[sp.Integer(-1)]*3
D=sp.diag(*weights)
one=sp.Matrix([1]*9)
g=sp.Matrix([0,0,0,1,1,1,0,0,0])
v=one+g
inner=lambda x,y: (x.T*D*y)[0]
assert inner(one,one)==3
assert inner(g,g)==3
assert inner(v,v)==12

def reflection(x):
    return sp.simplify(x - sp.Rational(2)*inner(x,v)/inner(v,v)*v)
# S=-r_v as a matrix.
Scols=[-reflection(sp.eye(9).col(i)) for i in range(9)]
S=sp.Matrix.hstack(*Scols)
assert S.T*D*S == D
assert S*one == g
assert S*g == one

# z vectors in g^perp.  Use 0-based indices: e1 is index 0, ..., e9 index 8.
def e(i): return sp.eye(9).col(i)
z=[None]*8
z[0]=e(0)+e(6)
z[2]=(e(0)-e(6))/2
z[1]=e(1)+e(7)
z[4]=(e(1)-e(7))/2
z[3]=e(2)+e(8)
z[5]=(e(2)-e(8))/2
z[6]=e(3)-e(4)
z[7]=e(4)-e(5)
for zz in z:
    assert inner(g,zz)==0
Z=sp.Matrix.hstack(*z)

# K in this investigation sl3 basis.
off=[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]
labels=[f'E{i}{j}' for i,j in off]+['H0','H1']
K=sp.zeros(8,8)
for a,(i,j) in enumerate(off):
    for b,(k,l) in enumerate(off):
        K[a,b]=1 if (j==k and i==l) else 0
K[6,6]=2; K[6,7]=-1; K[7,6]=-1; K[7,7]=2
assert Z.T*D*Z == K

B=S*Z
wvec=sp.Matrix(weights)
assert one.T*D*B == sp.zeros(1,8)
assert B.T*D*B == K
assert B.rank()==8

results={
    'scope':'Explicit rational 9-node certificate for the first three trace moments only; not a rank-22 decomposition or residual-cubic solution.',
    'sl3_basis':labels,
    'weights':[int(w) for w in weights],
    'sum_weights':str(sum(weights)),
    'D_norm_one':str(inner(one,one)),
    'D_norm_g':str(inner(g,g)),
    'D_norm_one_plus_g':str(inner(v,v)),
    'S_is_D_isometry':bool(S.T*D*S==D),
    'S_one_equals_g':bool(S*one==g),
    'Z_in_g_orthogonal':all(inner(g,zz)==0 for zz in z),
    'Z_gram_equals_K':bool(Z.T*D*Z==K),
    'B_linear_moment_zero':bool(one.T*D*B==sp.zeros(1,8)),
    'B_quadratic_moment_K':bool(B.T*D*B==K),
    'B_rank':int(B.rank()),
    'mu_rows':[[str(sp.factor(B[i,j])) for j in range(8)] for i in range(9)],
    'S_matrix':[[str(sp.factor(S[i,j])) for j in range(9)] for i in range(9)],
    'Z_columns':[[str(sp.factor(Z[i,j])) for i in range(8)] for j in range(8)],
    'interpretation':'The normalized moment system has rational 9-active-node solutions. Therefore excluding (10,4) requires coupling these moments to the residual cubic and rank-one/cube geometry, not just the first three trace moments.',
}
out=OUT/'nine_node_reflection_cubature.json'
with open(out,'w') as f: json.dump(results,f,indent=2)
print(json.dumps({
    'out':str(out),
    'sum_weights':results['sum_weights'],
    'linear_zero':results['B_linear_moment_zero'],
    'quadratic_K':results['B_quadratic_moment_K'],
    'rank':results['B_rank']
}, indent=2))
