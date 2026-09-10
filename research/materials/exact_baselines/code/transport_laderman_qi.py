#!/usr/bin/env python3
"""Exact Q(i) transport of Laderman Phi3*Phi4 to standard tau.

This is the characteristic-zero companion to transport_laderman_to_standard_tau.py.
It uses SymPy over QQ(i), with i^2=-1, and records the eight-free-bivector
anti-sector witness exactly.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "transport_laderman_tau"
OUT.mkdir(parents=True, exist_ok=True)

I = sp.I

# ---------- load integer Laderman terms from analysis ----------
src_path = SCRIPT_DIR / "laderman_tau_decomp.py"
src = src_path.read_text()
prefix = src.split('print(f"Sum matches T333')[0]
ns = {"__file__": str(src_path), "__name__": "defs_only"}
exec(compile(prefix, str(src_path), "exec"), ns)
terms_np = ns["terms"]
pi12_np, eps1_np, eps2_np, I3_np = ns["pi12"], ns["eps1"], ns["eps2"], ns["I3"]

def M_from_np(A):
    return sp.Matrix([[sp.Integer(int(A[r,c])) for c in range(A.shape[1])] for r in range(A.shape[0])])

terms = [(M_from_np(a), M_from_np(b), M_from_np(c)) for a,b,c in terms_np]
pi12 = M_from_np(pi12_np); eps1 = M_from_np(eps1_np); eps2 = M_from_np(eps2_np); I3 = M_from_np(I3_np)

fixed_1idx = [1, 4, 10, 12, 19, 21, 23]
two_cycles_1idx = [(2,5), (3,6), (7,16), (8,18), (9,17), (11,14), (13,15), (20,22)]
fixed = [i-1 for i in fixed_1idx]
two_cycles = [(i-1,j-1) for i,j in two_cycles_1idx]
perm = list(range(23))
for i,j in two_cycles:
    perm[i] = j; perm[j] = i

# ---------- sandwich transport ----------
P = I3
Q = eps1*pi12   # also pi12*eps2
R = sp.diag(I, 1, 1)
Qinv = Q.inv(); Rinv = R.inv(); Pinv = P.inv()

def Phi(a,b,c):
    a4 = eps1*c*pi12
    b4 = pi12*a*pi12*eps1
    c4 = eps1*pi12*b*eps1
    return (b4.T*eps2, eps2*a4.T, c4.T)

def tau(a,b,c):
    return (a.T, c.T, b.T)

def g(a,b,c):
    return (P*a*Qinv, Q*b*Rinv, R*c*Pinv)

# basis-level conjugacy check tau(g(x)) = g(Phi(x))
conj_ok = True
for comp in range(3):
    for pos in range(9):
        Z = sp.zeros(3,3)
        mats = [sp.zeros(3,3), sp.zeros(3,3), sp.zeros(3,3)]
        mats[comp][pos//3, pos%3] = 1
        lhs = tau(*g(*mats))
        rhs = g(*Phi(*mats))
        if any(sp.simplify(lhs[k]-rhs[k]) != sp.zeros(3,3) for k in range(3)):
            conj_ok = False

transported = [g(a,b,c) for a,b,c in terms]

# ---------- exact T333 replay ----------
def tensor_sum(term_list):
    T = [[[sp.Integer(0) for _ in range(9)] for __ in range(9)] for ___ in range(9)]
    for a,b,c in term_list:
        for r1 in range(3):
            for c1 in range(3):
                av = a[r1,c1]
                if av == 0: continue
                ia = 3*r1+c1
                for r2 in range(3):
                    for c2 in range(3):
                        bv = b[r2,c2]
                        if bv == 0: continue
                        ib = 3*r2+c2
                        for r3 in range(3):
                            for c3 in range(3):
                                cv = c[r3,c3]
                                if cv != 0:
                                    T[ia][ib][3*r3+c3] += av*bv*cv
    return T

def T333_tensor():
    T = [[[sp.Integer(0) for _ in range(9)] for __ in range(9)] for ___ in range(9)]
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j][3*j+k][3*k+i] = sp.Integer(1)
    return T

Tsum = tensor_sum(transported)
T333 = T333_tensor()
replay_ok = all(sp.simplify(Tsum[i][j][k] - T333[i][j][k]) == 0 for i in range(9) for j in range(9) for k in range(9))

# ---------- projective matching under standard tau ----------
def vec_entries(A):
    return [sp.simplify(A[r,c]) for r in range(3) for c in range(3)]

def prop_scalar(X,Y):
    xv = vec_entries(X); yv = vec_entries(Y)
    lam = None
    for x,y in zip(xv,yv):
        if y != 0:
            if lam is None:
                lam = sp.simplify(x/y)
            elif sp.simplify(x - lam*y) != 0:
                return None
        else:
            if x != 0:
                return None
    return sp.Integer(0) if lam is None else sp.simplify(lam)

def match_term(term, candidates):
    a,b,c = term
    for j,(aa,bb,cc) in enumerate(candidates):
        la = prop_scalar(a,aa); lb = prop_scalar(b,bb); lc = prop_scalar(c,cc)
        if la is None or lb is None or lc is None: continue
        if la == 0 or lb == 0 or lc == 0: continue
        if sp.simplify(la*lb*lc - 1) == 0:
            return j, (la,lb,lc)
    return None, None

std_matches = []
for i,t in enumerate(transported):
    j, scales = match_term(tau(*t), transported)
    std_matches.append((j, scales))
std_perm_ok = [j for j,_ in std_matches] == perm

# ---------- anti target and bivectors ----------
WEDGE_PAIRS = [(a,b) for a in range(9) for b in range(a+1,9)]
SKEW_PAIRS = [(0,1),(0,2),(1,2)]

def vec9(A):
    return [sp.simplify(A[r,c]) for r in range(3) for c in range(3)]

def wedge_vec(v,w):
    return [sp.simplify(v[i]*w[j] - v[j]*w[i]) for i,j in WEDGE_PAIRS]

def anti_target():
    def idx(i,k): return 3*i+k
    rows = []
    for a,b in SKEW_PAIRS:
        M = sp.zeros(9,9)
        for i0 in range(3):
            for j0 in range(3):
                Aij = 0
                if (i0,j0)==(a,b): Aij = 1
                elif (i0,j0)==(b,a): Aij = -1
                if Aij == 0: continue
                for k in range(3):
                    M[idx(j0,k), idx(i0,k)] += Aij
        rows.append([sp.simplify(M[i,j]) for i,j in WEDGE_PAIRS])
    return sp.Matrix(rows)

A_TARGET = anti_target()
all_bivectors = []
for a,b,c in transported:
    all_bivectors.append(wedge_vec(vec9(b), vec9(c.T)))
B_all = sp.Matrix(all_bivectors)

fixed_zero = [all(sp.simplify(x)==0 for x in B_all.row(i)) for i in fixed]
rep_indices = [i for i,j in two_cycles]
partner_indices = [j for i,j in two_cycles]
B_rep = sp.Matrix([all_bivectors[i] for i in rep_indices])
B_partner = sp.Matrix([all_bivectors[i] for i in partner_indices])
B_free = sp.Matrix([all_bivectors[i] for i in rep_indices+partner_indices])

def contains_target(B):
    return B.rank(), B.col_join(A_TARGET).rank(), B.rank() == B.col_join(A_TARGET).rank()

rep_rank, rep_aug_rank, rep_contains = contains_target(B_rep)
partner_rank, partner_aug_rank, partner_contains = contains_target(B_partner)
free_rank, free_aug_rank, free_contains = contains_target(B_free)

# solve coefficients C such that C*B_rep = A_TARGET
# SymPy gauss_jordan_solve solves B_rep.T * x = target.T for each row.
coeff_rows = []
for r in range(3):
    sol = B_rep.T.gauss_jordan_solve(A_TARGET.row(r).T)[0]
    coeff_rows.append([sp.simplify(sol[i,0]) for i in range(B_rep.rows)])

partner_rel = []
for i,j in two_cycles:
    # partner over rep scalar for bivectors
    eta_i = sp.Matrix([all_bivectors[i]])
    eta_j = sp.Matrix([all_bivectors[j]])
    lam = None
    for x,y in zip(list(eta_j), list(eta_i)):
        if y != 0:
            lam = sp.simplify(x/y) if lam is None else lam
            if sp.simplify(x-lam*y) != 0:
                lam = "not_proportional"; break
        elif x != 0:
            lam = "not_proportional"; break
    partner_rel.append({"pair":[i+1,j+1], "eta_partner_over_rep": str(lam)})

# compact term serialization in QQ(i) as strings for later exact reuse
terms_serialized = []
for a,b,c in transported:
    terms_serialized.append({
        "a": [[str(sp.simplify(a[row,col])) for col in range(3)] for row in range(3)],
        "b": [[str(sp.simplify(b[row,col])) for col in range(3)] for row in range(3)],
        "c": [[str(sp.simplify(c[row,col])) for col in range(3)] for row in range(3)],
    })

out = {
    "field": "Q(i)",
    "conjugacy_identity_tau_g_equals_g_Phi_on_basis": bool(conj_ok),
    "Q_equals_eps1_pi12_equals_pi12_eps2": bool(Q == pi12*eps2),
    "R_T_R_equals_eps1": bool(R.T*R == eps1),
    "transported_replay_T333_exact": bool(replay_ok),
    "standard_tau_perm_matches_phi_perm": bool(std_perm_ok),
    "fixed_terms": fixed_1idx,
    "fixed_bivectors_all_zero": bool(all(fixed_zero)),
    "fixed_bivectors_zero_by_term": {str(i+1): bool(fixed_zero[k]) for k,i in enumerate(fixed)},
    "free_pairs": [[i+1,j+1] for i,j in two_cycles],
    "partner_bivector_relations": partner_rel,
    "eight_rep_bivector_rank": int(rep_rank),
    "eight_rep_augmented_rank_with_Lanti": int(rep_aug_rank),
    "eight_rep_span_Lanti": bool(rep_contains),
    "eight_partner_bivector_rank": int(partner_rank),
    "eight_partner_augmented_rank_with_Lanti": int(partner_aug_rank),
    "eight_partner_span_Lanti": bool(partner_contains),
    "all_16_free_bivector_rank": int(free_rank),
    "all_16_free_augmented_rank_with_Lanti": int(free_aug_rank),
    "all_16_free_span_Lanti": bool(free_contains),
    "coefficients_A_TARGET_in_eight_rep_basis": [[str(x) for x in row] for row in coeff_rows],
    "sandwich_transport": {
        "P": [[str(P[r,c]) for c in range(3)] for r in range(3)],
        "Q": [[str(Q[r,c]) for c in range(3)] for r in range(3)],
        "R": [[str(R[r,c]) for c in range(3)] for r in range(3)],
        "formula": "g(A,B,C)=(P A Q^{-1}, Q B R^{-1}, R C P^{-1}); Phi=g^{-1} tau g"
    },
    "transported_terms_Qi": terms_serialized,
    "interpretation": (
        "Exact characteristic-zero Q(i) replay: after sandwich transport, Laderman is "
        "standard-tau invariant with skeleton (7,8), fixed terms have zero standard "
        "bivector, and the eight free-orbit bivectors span the standard L_anti. "
        "Thus the analysis m0=9 conclusion is false over algebraically closed/complex "
        "characteristic zero; m0 is 7 or 8 in characteristic not 2 where this standard "
        "tau class is realized over a field containing sqrt(-1)."
    )
}
path = OUT / "transported_laderman_standard_tau_Qi.json"
path.write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({k:v for k,v in out.items() if k != "transported_terms_Qi"}, indent=2))
print(f"SAVED {path}")
