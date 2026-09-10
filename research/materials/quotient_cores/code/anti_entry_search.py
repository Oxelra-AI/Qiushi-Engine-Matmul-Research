#!/usr/bin/env python3
"""Heuristic search for the tau-complement anti entry number m0.

Problem: for W=K^9 and L={A \otimes I_3 : A in Lambda^2 K^3} subset Lambda^2 W,
find m decomposable bivectors p_j wedge q_j whose span contains L.
Equivalently solve T_r = sum_j C_{rj} (p_j wedge q_j), r=1..3.

This script is numerical route-finding only. A zero-looking solution must be
exactified and checked over an exact field before it becomes evidence. Failure is
not a lower bound.
"""
from __future__ import annotations
import json, time
from pathlib import Path
import numpy as np
from scipy.optimize import least_squares

SESSION = Path(__file__).resolve().parents[1]
OUT = SESSION / "data" / "transpose_complement"
OUT.mkdir(parents=True, exist_ok=True)

WEDGE_PAIRS=[(i,j) for i in range(9) for j in range(i+1,9)]
SKEW_PAIRS=[(0,1),(0,2),(1,2)]
def idx(i,k): return 3*i+k

def wedge_vec(a,b):
    v=np.empty(36)
    for t,(i,j) in enumerate(WEDGE_PAIRS):
        v[t]=a[i]*b[j]-a[j]*b[i]
    return v

def anti_target():
    T=np.zeros((3,36))
    for r,(i,j) in enumerate(SKEW_PAIRS):
        for k in range(3):
            # target rows as in transpose_complement.py: - e_{i,k} wedge e_{j,k}
            pair=(idx(i,k),idx(j,k))
            if pair[0] < pair[1]:
                T[r,WEDGE_PAIRS.index(pair)] = -1
            else:
                T[r,WEDGE_PAIRS.index((pair[1],pair[0]))] = 1
    return T
TARGET=anti_target()

def unpack(x,m):
    off=0
    P=x[off:off+9*m].reshape(m,9); off+=9*m
    Q=x[off:off+9*m].reshape(m,9); off+=9*m
    C=x[off:off+3*m].reshape(3,m)
    return P,Q,C

def residual(x,m,reg=0.0):
    P,Q,C=unpack(x,m)
    K=np.array([wedge_vec(P[j],Q[j]) for j in range(m)])
    R=C@K-TARGET
    if reg:
        # very small norm stabilizer, not used for final residual.
        return np.concatenate([R.ravel(), reg*x])
    return R.ravel()

def canonical_x_m9():
    m=9
    P=np.zeros((m,9)); Q=np.zeros((m,9)); C=np.zeros((3,m))
    c=0
    for r,(i,j) in enumerate(SKEW_PAIRS):
        for k in range(3):
            P[c,idx(i,k)]=1
            Q[c,idx(j,k)]=1
            C[r,c]=-1
            c+=1
    return np.concatenate([P.ravel(),Q.ravel(),C.ravel()])

def run_for_m(m, restarts, max_nfev, seed):
    rng=np.random.default_rng(seed)
    best={"residual_norm": 1e99, "max_abs": 1e99, "var_norm": None, "restart": None, "status": None}
    success_path=None
    starts=[]
    if m==9:
        starts.append(canonical_x_m9())
    for t in range(restarts):
        # scaled Gaussian starts.  The C scale is smaller to avoid huge initial products.
        P=rng.normal(size=(m,9))
        Q=rng.normal(size=(m,9))
        C=rng.normal(scale=0.3, size=(3,m))
        starts.append(np.concatenate([P.ravel(),Q.ravel(),C.ravel()]))
    t0=time.time()
    for t,x0 in enumerate(starts):
        res=least_squares(lambda x: residual(x,m), x0, method='trf', max_nfev=max_nfev,
                          ftol=1e-11, xtol=1e-11, gtol=1e-11, x_scale='jac')
        r=residual(res.x,m)
        norm=float(np.linalg.norm(r)); mx=float(np.max(np.abs(r)))
        if norm < best["residual_norm"]:
            best={"residual_norm": norm, "max_abs": mx, "var_norm": float(np.linalg.norm(res.x)),
                  "restart": t, "status": int(res.status), "nfev": int(res.nfev), "message": res.message[:160]}
            pth=OUT/f"anti_entry_m{m}_best.npy"
            np.save(pth, res.x)
            best["best_path"] = str(pth.relative_to(SESSION))
        if norm < 1e-9 and success_path is None:
            pth=OUT/f"anti_entry_m{m}_success.npy"
            np.save(pth, res.x)
            success_path=str(pth.relative_to(SESSION))
            break
    best["success"] = success_path is not None
    if success_path: best["success_path"] = success_path
    best["elapsed_sec"] = round(time.time()-t0, 3)
    return best

def main():
    jobs=[(5,4,3000),(6,6,4000),(7,8,5000),(8,12,6000),(9,0,1000)]
    out={"warning":"heuristic numerical search only; nonzero residual is not a proof", "target_norm": float(np.linalg.norm(TARGET)), "results":{}}
    for m,restarts,maxn in jobs:
        print(f"m={m}: restarts={restarts}, max_nfev={maxn}", flush=True)
        out["results"][str(m)] = run_for_m(m,restarts,maxn, seed=61061+97*m)
        print(json.dumps(out["results"][str(m)], indent=2), flush=True)
    path=OUT/"anti_entry_numeric_search.json"
    path.write_text(json.dumps(out, indent=2)+"\n")
    print(f"SAVED {path}")

if __name__=='__main__':
    main()
