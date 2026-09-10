#!/usr/bin/env python3
"""analysis: Extended (10,4) search with normalized objective and 300 restarts."""

import numpy as np, json, time
from scipy.linalg import expm
from scipy.optimize import minimize
from itertools import combinations
from pathlib import Path

OUT = Path("data/rank10_search")
OUT.mkdir(parents=True, exist_ok=True)

I3 = np.eye(3)
K9 = np.zeros((9,9))
for a in range(9):
    i,j = divmod(a,3); K9[a,3*j+i] = 1.0

SL3_GEN = []
for i in range(3):
    for j in range(3):
        if i != j:
            E = np.zeros((3,3)); E[i,j] = 1.0; SL3_GEN.append(E)
SL3_GEN.append(np.diag([1.,-1.,0.]))
SL3_GEN.append(np.diag([0.,1.,-1.]))

SUBS = np.array(list(combinations(range(9),4)),dtype=int)
SI1,SI2,SI3,SI4 = SUBS[:,0],SUBS[:,1],SUBS[:,2],SUBS[:,3]

with open("data/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json") as f:
    scheme = json.load(f)
PLANES = []
for rep in scheme["free_orbit_representatives"]:
    PLANES.append((np.array(rep["U"],dtype=float).T, np.array(rep["V"],dtype=float).T, np.array(rep["W"],dtype=float).T))

def precomp(planes):
    pd = []
    for A,B,C in planes:
        a,b,c = A.ravel(), B.ravel(), C.ravel()
        at,bt,ct = A.T.ravel(), B.T.ravel(), C.T.ravel()
        pd.append((at,bt,ct, np.outer(a,bt)+np.outer(b,at), np.outer(a,ct)+np.outer(c,at), np.outer(b,ct)+np.outer(c,bt)))
    return pd

def compute_6S(X, pd):
    J = np.kron(X,I3) + np.kron(I3,X.T)
    x = X.ravel()
    corr = np.zeros((9,9))
    for at,bt,ct,MAB,MAC,MBC in pd:
        corr += (ct@x)*MAB + (bt@x)*MAC + (at@x)*MBC
    return 3.0*(J - corr)

def obj_normalized(theta, planes, dirs):
    """Scale-invariant objective: sum of (Pf / ||Omega||^2)^2"""
    frames = [expm(sum(theta[8*j+k]*SL3_GEN[k] for k in range(8))) for j in range(4)]
    new_pl = [None]*4
    for j in range(4):
        A,B,C = planes[j]; M = frames[j]
        new_pl[j] = (M[0,0]*A+M[0,1]*B+M[0,2]*C, M[1,0]*A+M[1,1]*B+M[1,2]*C, M[2,0]*A+M[2,1]*B+M[2,2]*C)
    pd = precomp(new_pl)
    total = 0.0
    for X,Y in dirs:
        SX = compute_6S(X,pd); SY = compute_6S(Y,pd)
        C = SX@SY - SY@SX
        O = K9@C
        fnorm_sq = np.sum(O*O)
        if fnorm_sq < 1e-50:
            continue
        pf = O[SI1,SI2]*O[SI3,SI4] - O[SI1,SI3]*O[SI2,SI4] + O[SI1,SI4]*O[SI2,SI3]
        total += np.sum(pf*pf) / (fnorm_sq * fnorm_sq)
    return total

def obj_raw(theta, planes, dirs):
    """Raw Pfaffian sum (for comparison)."""
    frames = [expm(sum(theta[8*j+k]*SL3_GEN[k] for k in range(8))) for j in range(4)]
    new_pl = [None]*4
    for j in range(4):
        A,B,C = planes[j]; M = frames[j]
        new_pl[j] = (M[0,0]*A+M[0,1]*B+M[0,2]*C, M[1,0]*A+M[1,1]*B+M[1,2]*C, M[2,0]*A+M[2,1]*B+M[2,2]*C)
    pd = precomp(new_pl)
    total = 0.0
    for X,Y in dirs:
        SX = compute_6S(X,pd); SY = compute_6S(Y,pd)
        C = SX@SY - SY@SX
        O = K9@C
        pf = O[SI1,SI2]*O[SI3,SI4] - O[SI1,SI3]*O[SI2,SI4] + O[SI1,SI4]*O[SI2,SI3]
        total += np.sum(pf*pf)
    return total

def rank_at(theta, planes, dirs):
    frames = [expm(sum(theta[8*j+k]*SL3_GEN[k] for k in range(8))) for j in range(4)]
    new_pl = [None]*4
    for j in range(4):
        A,B,C = planes[j]; M = frames[j]
        new_pl[j] = (M[0,0]*A+M[0,1]*B+M[0,2]*C, M[1,0]*A+M[1,1]*B+M[1,2]*C, M[2,0]*A+M[2,1]*B+M[2,2]*C)
    pd = precomp(new_pl)
    ranks = []
    for X,Y in dirs:
        SX = compute_6S(X,pd); SY = compute_6S(Y,pd)
        C = SX@SY - SY@SX
        O = K9@C
        sv = np.linalg.svd(O, compute_uv=False)
        ranks.append(int(np.sum(sv > 1e-8*sv[0])))
    return ranks

rng_d = np.random.RandomState(42)
dirs = [(np.array([[3,0,1],[3,-1,1],[1,3,-2]],dtype=float), np.array([[-1,3,-1],[-1,1,0],[-1,2,1]],dtype=float))]
for _ in range(5):
    dirs.append((rng_d.randint(-5,6,(3,3)).astype(float), rng_d.randint(-5,6,(3,3)).astype(float)))

# Baselines
fn0 = obj_normalized(np.zeros(32), PLANES, dirs)
fr0 = obj_raw(np.zeros(32), PLANES, dirs)
rk0 = rank_at(np.zeros(32), PLANES, dirs)
print(f"BILR: norm_obj={fn0:.6e}, raw_obj={fr0:.6e}, ranks={rk0}")

# Main search: 300 restarts with normalized objective
rng = np.random.RandomState(31415)
results = []
t0 = time.time()
for trial in range(300):
    sigma = [0.3, 1.0, 2.0, 4.0][trial % 4]
    th0 = rng.randn(32) * sigma
    res = minimize(obj_normalized, th0, args=(PLANES, dirs),
                   method='Powell', options={'maxiter':200, 'maxfev':4000, 'ftol':1e-30})
    fn = float(res.fun)
    fr = float(obj_raw(res.x, PLANES, dirs))
    rk = rank_at(res.x, PLANES, dirs)
    results.append({"trial": trial, "norm_f": fn, "raw_f": fr, "ranks": rk, "nfev": res.nfev, "sigma": sigma, "param_norm": float(np.linalg.norm(res.x))})
    if fn < fn0 * 0.01:
        print(f"*** Trial {trial}: norm_f={fn:.4e}, raw_f={fr:.4e}, ranks={rk}")
    elif trial % 30 == 0:
        print(f"Trial {trial}/300: norm_f={fn:.4e}, raw_f={fr:.4e}, ranks={rk}, elapsed={time.time()-t0:.0f}s")

elapsed = time.time() - t0
results.sort(key=lambda r: r["norm_f"])
print(f"\nTotal: {elapsed:.0f}s for 300 restarts")
print(f"Best 10 normalized objectives:")
for r in results[:10]:
    print(f"  trial {r['trial']}: norm_f={r['norm_f']:.6e}, raw_f={r['raw_f']:.6e}, ranks={r['ranks']}, σ={r['sigma']}")

# Check rank distribution
rank_counts = {}
for r in results:
    key = str(sorted(set(r["ranks"])))
    rank_counts[key] = rank_counts.get(key, 0) + 1
print(f"\nRank distributions: {json.dumps(rank_counts, sort_keys=True)}")

min_rank_seen = min(min(r["ranks"]) for r in results)
print(f"Minimum rank seen across all 300 restarts: {min_rank_seen}")

output = {
    "scope": "Extended (10,4) rank-10 search with normalized Pfaffian objective, 300 restarts",
    "baseline": {"norm_f": fn0, "raw_f": fr0, "ranks": rk0},
    "n_restarts": 300,
    "elapsed_sec": elapsed,
    "best_10": results[:10],
    "rank_distribution": rank_counts,
    "min_rank_seen": min_rank_seen,
    "interpretation": (
        "Scale-invariant objective prevents the optimizer from reducing the objective "
        "merely by shrinking the commutator. If the normalized objective is robustly "
        "nonzero and the minimum rank is > 2, the (10,4) family has no rank-≤10 residual."
    ),
}
json.dump(output, open(str(OUT/"extended_search.json"), "w"), indent=2, default=str)
print(f"\nSaved to {OUT}/extended_search.json")
