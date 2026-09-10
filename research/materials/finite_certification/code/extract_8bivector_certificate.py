#!/usr/bin/env python3
"""Extract a compact Q(i) certificate for the transported Laderman m0<=8 witness."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp

SCRIPT_DIR=Path(__file__).resolve().parent
WS=SCRIPT_DIR.parent
OUT=WS/"data"/"transport_laderman_tau"
OUT.mkdir(parents=True,exist_ok=True)
I=sp.I

# Reuse exact data construction from transport_laderman_qi.py in a compact way.
src_path=SCRIPT_DIR/"laderman_tau_decomp.py"
src=src_path.read_text(); prefix=src.split('print(f"Sum matches T333')[0]
ns={"__file__":str(src_path),"__name__":"defs_only"}
exec(compile(prefix,str(src_path),"exec"),ns)
def M(A): return sp.Matrix([[sp.Integer(int(A[r,c])) for c in range(3)] for r in range(3)])
terms=[(M(a),M(b),M(c)) for a,b,c in ns['terms']]
pi12=M(ns['pi12']); eps1=M(ns['eps1']); eps2=M(ns['eps2']); I3=M(ns['I3'])
P=I3; Q=eps1*pi12; R=sp.diag(I,1,1); Qinv=Q.inv(); Rinv=R.inv()
def g(a,b,c): return (P*a*Qinv, Q*b*Rinv, R*c*P.inv())
transported=[g(a,b,c) for a,b,c in terms]
free_pairs=[(2,5),(3,6),(7,16),(8,18),(9,17),(11,14),(13,15),(20,22)]
rep=[i-1 for i,j in free_pairs]
WEDGE_PAIRS=[(a,b) for a in range(9) for b in range(a+1,9)]
SKEW_PAIRS=[(0,1),(0,2),(1,2)]
def vec9(A): return [sp.simplify(A[r,c]) for r in range(3) for c in range(3)]
def wedge(v,w): return [sp.simplify(v[i]*w[j]-v[j]*w[i]) for i,j in WEDGE_PAIRS]
def anti_target():
    def idx(i,k): return 3*i+k
    rows=[]
    for a,b in SKEW_PAIRS:
        M9=sp.zeros(9,9)
        for i0 in range(3):
            for j0 in range(3):
                Aij=0
                if (i0,j0)==(a,b): Aij=1
                elif (i0,j0)==(b,a): Aij=-1
                if not Aij: continue
                for k in range(3): M9[idx(j0,k),idx(i0,k)] += Aij
        rows.append([sp.simplify(M9[i,j]) for i,j in WEDGE_PAIRS])
    return sp.Matrix(rows)
B=sp.Matrix([wedge(vec9(transported[i][1]), vec9(transported[i][2].T)) for i in rep])
A=anti_target()
assert B.rank()==8 and B.col_join(A).rank()==8
# RREF pivots for nonzero 8x8 minor.
rref,piv=B.rref()
piv=list(piv[:8])
minor=B[:,piv]
det=sp.factor(minor.det())
assert det != 0
# coefficient matrix already known but recompute exactly.
coeff=[]
for r in range(3):
    sol=B.T.gauss_jordan_solve(A.row(r).T)[0]
    coeff.append([sp.simplify(sol[i,0]) for i in range(8)])
C=sp.Matrix(coeff)
assert C*B == A
# Seven deletion defects exactly.
seven=[]
for k in range(8):
    rows=[B.row(i) for i in range(8) if i!=k]
    S=sp.Matrix(rows)
    seven.append({"skip_pair": list(free_pairs[k]), "rank": int(S.rank()), "augmented_rank": int(S.col_join(A).rank())})
out={
    "field":"Q(i)",
    "free_pairs_1based":[list(x) for x in free_pairs],
    "wedge_coordinate_pairs": [list(x) for x in WEDGE_PAIRS],
    "eight_by_eight_minor_columns_0based": piv,
    "eight_by_eight_minor_wedge_pairs": [list(WEDGE_PAIRS[j]) for j in piv],
    "minor_determinant": str(det),
    "target_coefficients_rows_L01_L02_L12": [[str(x) for x in row] for row in coeff],
    "seven_subset_ranks": seven,
    "bivectors_restricted_to_minor_columns": [[str(sp.simplify(B[i,j])) for j in piv] for i in range(8)],
    "interpretation":"Compact certificate: the 8 transported Laderman free bivectors are independent by the displayed minor, and the coefficient matrix expresses the three L_anti target rows in their span over Q(i)."
}
json_path=OUT/"laderman_8bivector_certificate_Qi.json"
json_path.write_text(json.dumps(out,indent=2)+"\n")
md=OUT/"laderman_8bivector_certificate_Qi.md"
md.write_text("# Transported Laderman eight-bivector certificate over Q(i)\n\n"+
              f"Free pairs (1-based): {out['free_pairs_1based']}\n\n"+
              f"Minor columns (0-based): {piv}\n\n"+
              f"Minor wedge pairs: {out['eight_by_eight_minor_wedge_pairs']}\n\n"+
              f"Determinant: `{det}`\n\n"+
              "Target coefficient matrix rows for L01,L02,L12:\n\n"+
              "```\n"+"\n".join(str(row) for row in out['target_coefficients_rows_L01_L02_L12'])+"\n```\n\n"+
              "Every seven-subset of this eight-witness has augmented rank one larger than its rank; see JSON for the exact list.\n")
print(json.dumps({k:v for k,v in out.items() if k not in ['bivectors_restricted_to_minor_columns']},indent=2))
print(f"SAVED {json_path}")
print(f"SAVED {md}")
