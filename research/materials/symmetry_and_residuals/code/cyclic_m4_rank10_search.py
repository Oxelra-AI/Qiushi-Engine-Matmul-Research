#!/usr/bin/env python3
"""
analysis: local construction pressure on the cyclic m=4 rank-22 problem.

Use the exact BILR Z4 x Z3 cyclic rank-23 scheme as a rank-4 exterior decomposition
of the Cartan trivector.  The four free cyclic orbits are kept in the same exterior
fiber by applying independent SL_3 basis changes to each 3-plane.  We then ask whether
tr(M^3) - 3 sum_j l_{U_j'} l_{V_j'} l_{W_j'} can be represented by 10 cubes.

This is a smaller diagonal/exterior system for the m=4 cyclic rank-22 question.  A zero
would give a cyclic rank-22 algorithm; nonzero local minima are evidence only.
"""
from __future__ import annotations
import argparse, itertools, json, time
from pathlib import Path
import numpy as np
from scipy.optimize import least_squares
from scipy.linalg import expm

WS = Path(__file__).resolve().parent.parent
OUT = WS/'data'/'cyclic_m4_rank10_search'
OUT.mkdir(parents=True, exist_ok=True)

MONOS = list(itertools.combinations_with_replacement(range(9),3))
MONO_IDX = {m:i for i,m in enumerate(MONOS)}
PERMS_BY_MONO = {m: sorted(set(itertools.permutations(m))) for m in MONOS}

# sl3 basis columns in gl coordinates, same as analysis/38.
def sl_to_gl():
    B=np.zeros((9,8))
    B[1,0]=1; B[2,1]=1; B[3,2]=1; B[5,3]=1; B[6,4]=1; B[7,5]=1
    B[0,6]=1; B[4,6]=-1; B[4,7]=1; B[8,7]=-1
    return B
B=sl_to_gl(); PINV=np.linalg.pinv(B)

# basis for traceless 3x3 generator acting on a term's three basis vectors.
GEN=[]
for i in range(3):
    for j in range(3):
        if i!=j:
            G=np.zeros((3,3)); G[i,j]=1; GEN.append(G)
G=np.diag([1,-1,0.]); GEN.append(G)
G=np.diag([0,1,-1.]); GEN.append(G)
GEN=np.array(GEN)
assert GEN.shape==(8,3,3)

def coeff_target():
    c=np.zeros(len(MONOS))
    for a,b,cidx in itertools.product(range(3), repeat=3):
        key=tuple(sorted([3*a+b,3*b+cidx,3*cidx+a]))
        c[MONO_IDX[key]] += 1.0
    return c
TARGET=coeff_target()

def cube_coeff(v):
    out=np.zeros(len(MONOS))
    for midx,m in enumerate(MONOS):
        s=0.0
        for p in PERMS_BY_MONO[m]:
            s += v[p[0]]*v[p[1]]*v[p[2]]
        out[midx]=s
    return out

def prod_coeff(u,v,w):
    out=np.zeros(len(MONOS))
    for midx,m in enumerate(MONOS):
        s=0.0
        for p in PERMS_BY_MONO[m]:
            s += u[p[0]]*v[p[1]]*w[p[2]]
        out[midx]=s
    return out

def load_bilr():
    p=WS/'data'/'ballard_z4_cyclic'/'ballard_z4_cyclic_scheme.json'
    if not p.exists():
        raise FileNotFoundError('Run ballard_z4_cyclic_scheme.py first')
    data=json.loads(p.read_text())
    cubes=[np.array(C,dtype=float).reshape(9) for C in data['cubes']]
    free=[]
    for rec in data['free_orbit_representatives']:
        U=np.array(rec['U'],dtype=float).reshape(9)
        V=np.array(rec['V'],dtype=float).reshape(9)
        W=np.array(rec['W'],dtype=float).reshape(9)
        free.append(np.array([PINV@U, PINV@V, PINV@W]))
    return np.array(cubes), np.array(free)

def transform_orbits(base_free, y):
    # y length 32, four traceless 3x3 generators
    out=[]
    for j in range(4):
        A=sum(y[8*j+k]*GEN[k] for k in range(8))
        S=expm(A)
        out.append(S @ base_free[j])
    return np.array(out)

def orbit_coeff(base_free, y):
    free=transform_orbits(base_free,y)
    out=np.zeros(len(MONOS))
    for j in range(4):
        u=B@free[j,0]; v=B@free[j,1]; w=B@free[j,2]
        out += 3.0*prod_coeff(u,v,w)
    return out

def residual_vec(x, base_free):
    y=x[:32]
    cube_vars=x[32:].reshape(10,9)
    res=TARGET - orbit_coeff(base_free,y)
    for c in cube_vars:
        res -= cube_coeff(c)
    return res

def initial_vector(cubes, drop, noise, rng):
    keep=[i for i in range(11) if i!=drop]
    cv=np.array([cubes[i] for i in keep], dtype=float)
    if noise:
        cv = cv + noise*rng.standard_normal(cv.shape)
    y=np.zeros(32)
    if noise:
        y += (noise*0.15)*rng.standard_normal(32)
    return np.concatenate([y, cv.reshape(-1)])

def run_trial(cubes, base_free, drop, noise, seed, max_nfev):
    rng=np.random.default_rng(seed)
    x0=initial_vector(cubes, drop, noise, rng)
    r0=residual_vec(x0, base_free)
    t0=time.time()
    sol=least_squares(lambda x: residual_vec(x,base_free), x0, method='trf', max_nfev=max_nfev,
                      ftol=1e-12, xtol=1e-12, gtol=1e-12, x_scale='jac', verbose=0)
    sec=time.time()-t0
    r=residual_vec(sol.x,base_free)
    y_norm=float(np.linalg.norm(sol.x[:32]))
    cube_norm=float(np.linalg.norm(sol.x[32:]))
    return {
        'drop': int(drop), 'noise': float(noise), 'seed': int(seed), 'max_nfev': int(max_nfev),
        'initial_norm': float(np.linalg.norm(r0)), 'initial_max_abs': float(np.max(np.abs(r0))),
        'final_norm': float(np.linalg.norm(r)), 'final_max_abs': float(np.max(np.abs(r))),
        'cost': float(sol.cost), 'optimality': float(sol.optimality), 'nfev': int(sol.nfev),
        'status': int(sol.status), 'message': sol.message, 'sec': sec,
        'sl3_param_norm': y_norm, 'cube_param_norm': cube_norm,
        'success_exact_threshold_1e-8': bool(np.linalg.norm(r)<1e-8),
    }

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--drops', default='all', help='all or comma-separated 0..10')
    ap.add_argument('--noises', default='0,0.05', help='comma-separated noise scales')
    ap.add_argument('--max-nfev', type=int, default=1500)
    ap.add_argument('--seed', type=int, default=3838)
    args=ap.parse_args()
    cubes,base_free=load_bilr()
    drops=list(range(11)) if args.drops=='all' else [int(x) for x in args.drops.split(',') if x]
    noises=[float(x) for x in args.noises.split(',') if x!='']
    records=[]
    for drop in drops:
        for ni,noise in enumerate(noises):
            rec=run_trial(cubes,base_free,drop,noise,args.seed+1000*drop+ni,args.max_nfev)
            print(rec, flush=True)
            records.append(rec)
            out=OUT/'rank10_search_partial.json'
            out.write_text(json.dumps({'records':records},indent=2)+'\n')
    summary={
        'interpretation':'local nonlinear search in the BILR m=4 exterior component; success would be a cyclic rank-22 candidate, failure is not a proof',
        'records':records,
        'best_final_norm': min(r['final_norm'] for r in records) if records else None,
        'best_record': min(records, key=lambda r:r['final_norm']) if records else None,
    }
    out=OUT/'rank10_search_results.json'
    out.write_text(json.dumps(summary,indent=2)+'\n')
    print('Saved',out)

if __name__=='__main__':
    main()
