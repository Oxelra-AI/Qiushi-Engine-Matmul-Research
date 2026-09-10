#!/usr/bin/env python3
"""
analysis: exact Q check of elementary internal-frame points that fooled a small
fixed scalar rank<=2 test over F_31.

The F_31 pilot found that moving a single BILR exterior-plane frame by the
unipotent coordinate map e_0 -> e_0 + e_2 (generator (2,0), t=1 in the script's
column convention) makes the five chosen fixed-pair scalar invariants vanish,
although the bounded-rank classification screen still fails.  This script checks
that phenomenon over Q and records it as a warning: fixed scalar identities are
cheap necessary conditions, but a small handful of pairs is not sufficient.
"""

from pathlib import Path
import json
import random
import sympy as sp

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "product_commutator"
OUT.mkdir(parents=True, exist_ok=True)

def E(i,j):
    M=sp.zeros(3,3); M[i,j]=1; return M
basis=[E(i,j) for i in range(3) for j in range(3)]
basis_names=[f"E{i}{j}" for i in range(3) for j in range(3)]

def mat_from_json(M):
    return sp.Matrix([[sp.Rational(M[i][j]) for j in range(3)] for i in range(3)])
def tracefree(M):
    return sp.simplify(M-sp.trace(M)/3*sp.eye(3))
def ell(A,X):
    return sp.trace(A*X)
def vec_to_mat(x):
    M=sp.zeros(3,3)
    for a,xa in enumerate(x): M += sp.Rational(xa)*basis[a]
    return M
def mat_to_vec(M):
    return sp.Matrix([sp.simplify(M[i,j]) for i in range(3) for j in range(3)])
def comm(A,B): return sp.simplify(A*B-B*A)
def flatten(M): return [sp.simplify(M[i,j]) for i in range(M.rows) for j in range(M.cols)]

def rank(M): return int(sp.Matrix(M).rank())

with open(WS/"data/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json") as f:
    scheme=json.load(f)
base=[]
for rep in scheme["free_orbit_representatives"]:
    tri=[]
    for key in ["U","V","W"]:
        tri.append(tracefree(mat_from_json(rep[key])).T) # trace-pairing gradient
    base.append(tri)

def apply_frame_to_plane(tri, F):
    out=[]
    for col in range(3):
        A=sp.zeros(3,3)
        for row in range(3):
            A += sp.Rational(F[row,col])*tri[row]
        out.append(sp.simplify(A))
    return out

def H2_product(x, triples):
    X=vec_to_mat(x)
    cols=[]
    for Y in basis:
        out=X*Y+Y*X
        for U,V,W in triples:
            uX,vX,wX=ell(U,X),ell(V,X),ell(W,X)
            uY,vY,wY=ell(U,Y),ell(V,Y),ell(W,Y)
            out -= (vX*wY+wX*vY)*U
            out -= (uX*wY+wX*uY)*V
            out -= (uX*vY+vX*uY)*W
        cols.append(mat_to_vec(out))
    return sp.Matrix.hstack(*cols)

def H_basis(triples):
    return [H2_product([1 if i==a else 0 for i in range(9)], triples) for a in range(9)]

def L_data(Hs):
    comms=[]; ranks=[]
    for a in range(9):
        for b in range(a+1,9):
            C=comm(Hs[a],Hs[b]); comms.append(C); ranks.append(rank(C))
    span_dim=rank(sp.Matrix([flatten(C) for C in comms]))
    common_image_dim=rank(sp.Matrix.hstack(*comms))
    common_kernel_dim=9-rank(sp.Matrix.vstack(*comms))
    return {"span_dim":span_dim,"common_image_dim":common_image_dim,"common_kernel_dim":common_kernel_dim,
            "max_basis_rank":max(ranks),"basis_rank_hist":{str(r):ranks.count(r) for r in sorted(set(ranks))},"comms":comms}

rank2_pairs=[
    ([3,0,1,3,-1,1,1,3,-2], [-1,3,-1,-1,1,0,-1,2,1]),
    ([1,0,0,0,0,0,0,0,-1], [0,1,2,0,-1,0,3,0,1]),
    ([0,1,0,2,0,1,-1,0,3], [2,0,-1,1,1,0,0,3,-2]),
    ([1,2,3,4,5,6,7,8,9], [2,-1,0,3,-2,1,4,0,-3]),
    ([0,0,1,0,1,0,1,0,0], [1,1,0,-1,0,2,0,-2,1]),
]

def scalar_values(Hs, pairs):
    vals=[]
    for x,y in pairs:
        Hx=sum((sp.Rational(x[a])*Hs[a] for a in range(9)), sp.zeros(9,9))
        Hy=sum((sp.Rational(y[a])*Hs[a] for a in range(9)), sp.zeros(9,9))
        C=comm(Hx,Hy); C2=C*C; C3=C2*C; C4=C2*C2
        vals.append({
            "rank":rank(C),
            "trC3":str(sp.factor(sp.trace(C3))),
            "rank2_quartic":str(sp.factor(2*sp.trace(C4)-sp.trace(C2)**2)),
        })
    return vals

# Random deterministic integer pairs for finding an escaping rank-4 witness.
def random_pair_values(Hs, trials=50, seed=5001):
    rng=random.Random(seed)
    out=[]
    for i in range(trials):
        x=[rng.randint(-3,3) for _ in range(9)]
        y=[rng.randint(-3,3) for _ in range(9)]
        Hx=sum((sp.Rational(x[a])*Hs[a] for a in range(9)), sp.zeros(9,9))
        Hy=sum((sp.Rational(y[a])*Hs[a] for a in range(9)), sp.zeros(9,9))
        C=comm(Hx,Hy); r=rank(C)
        if r>=3:
            C2=C*C; C4=C2*C2
            out.append({"trial":i,"x":x,"y":y,"rank":r,
                        "rank2_quartic":str(sp.factor(2*sp.trace(C4)-sp.trace(C2)**2))})
            break
    return out

results=[]
for plane in range(4):
    F=sp.eye(3)
    F[2,0]=1  # column 0 <- column0 + e2, matching modular generator (2,0), t=1
    triples=[list(tri) for tri in base]
    triples[plane]=apply_frame_to_plane(base[plane], F)
    Hs=H_basis(triples)
    D=L_data(Hs)
    fixed=scalar_values(Hs, rank2_pairs)
    fixed_pass=all(v["trC3"]=="0" and v["rank2_quartic"]=="0" for v in fixed)
    escape=random_pair_values(Hs)
    results.append({
        "plane":plane,
        "frame_matrix": [[str(F[i,j]) for j in range(3)] for i in range(3)],
        "fixed_five_scalar_filters_pass": fixed_pass,
        "fixed_five_values": fixed,
        "L_summary": {k:v for k,v in D.items() if k!="comms"},
        "classification_screen_passes": bool(D["span_dim"]<=3 or D["common_image_dim"]<=2 or D["common_kernel_dim"]>=7),
        "first_random_rank_ge3_pair": escape,
    })

out=OUT/"elementary_scalar_exception_exact.json"
with open(out,"w") as f: json.dump({
    "scope":"Exact Q check of elementary internal-frame points where the fixed five scalar rank<=2 invariants vanish but L is not a rank<=2 bounded matrix space.",
    "operator_scaling":"H2=2H; scalar quartic identities scale but zero/nonzero is unchanged.",
    "fixed_pairs": [{"x":x,"y":y} for x,y in rank2_pairs],
    "cases":results,
    "interpretation":"The selected scalar identities at finitely many X,Y can miss rank>2 commutators. Bounded-rank proof must impose all X,Y or use the compression/primitive classification on the full linear space L.",
}, f, indent=2)
print(json.dumps({
    "out":str(out),
    "fixed_pass_by_plane":[r["fixed_five_scalar_filters_pass"] for r in results],
    "classification_pass_by_plane":[r["classification_screen_passes"] for r in results],
    "L_summaries":[r["L_summary"] for r in results],
    "escape_ranks":[r["first_random_rank_ge3_pair"][0]["rank"] if r["first_random_rank_ge3_pair"] else None for r in results],
}, indent=2))
