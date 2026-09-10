#!/usr/bin/env python3
"""Build and optimize rank-22 candidates from a near pair-rank defect on a rank-23 path.

If a rank-23 decomposition T=sum_i u_i⊗v_i⊗w_i has an exact linear relation among
one two-factor pairing, e.g. sum_i gamma_i (u_i⊗v_i)=0, then one term can be removed
by absorbing its third factor into the others.  This script takes a numerically near
rank-defect point, performs that shortening, and then uses nonlinear least squares on
the full rank-22 Brent equations.  It reports whether the near-boundary signal is only
an approximate/border phenomenon or yields a genuine exact-looking rank-22 point.
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np
from scipy.optimize import least_squares

SCRIPT_DIR=Path(__file__).resolve().parent
sys.path.insert(0,str(SCRIPT_DIR))
from formal_lift_pairing import parse_qmm, terms_to_vec, tensor_value, projective_pairing_stats  # noqa: E402


def blocks(x,i):
    cb=27*i
    return x[cb:cb+9], x[cb+9:cb+18], x[cb+18:cb+27]


def target_from_scheme(scheme):
    S=parse_qmm(scheme)
    x0=terms_to_vec(S['terms'])
    return tensor_value(x0,S['rank']), S['rank']


def pairing_matrix(x,r,pair,normalized=True):
    off={'u':0,'v':9,'w':18}
    a,b=pair[0],pair[1]
    cols=[]; norms=[]
    for i in range(r):
        fi=x[27*i+off[a]:27*i+off[a]+9]
        gi=x[27*i+off[b]:27*i+off[b]+9]
        col=np.outer(fi,gi).reshape(-1)
        norm=np.linalg.norm(col)
        norms.append(norm)
        if normalized and norm>1e-14:
            col=col/norm
        cols.append(col)
    return np.array(cols).T, np.array(norms)


def shorten_from_relation(x23,r,pair,beta,norms,remove=None):
    # beta is relation for normalized pair columns; gamma is relation for raw pair columns.
    gamma=beta/np.maximum(norms,1e-300)
    if remove is None:
        remove=int(np.argmax(np.abs(gamma)))
    if abs(gamma[remove])<1e-14:
        raise ValueError('chosen removal coefficient too small')
    terms=[]
    for i in range(r):
        if i==remove:
            continue
        u,v,w=[arr.copy() for arr in blocks(x23,i)]
        uj,vj,wj=blocks(x23,remove)
        coeff=gamma[i]/gamma[remove]
        if pair=='uv':
            w = w - coeff*wj
        elif pair=='uw':
            v = v - coeff*vj
        elif pair=='vw':
            u = u - coeff*uj
        else:
            raise ValueError(pair)
        terms.extend([u,v,w])
    return np.concatenate(terms), remove, gamma


def residual_rank22(y,target):
    return tensor_value(y,22)-target


def jacobian_rank22(y):
    r=22; n=9
    J=np.zeros((729,27*r),dtype=float)
    for i in range(r):
        u,v,w=blocks(y,i)
        cb=27*i
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    row=a*81+b*9+c
                    J[row,cb+a]+=v[b]*w[c]
                    J[row,cb+9+b]+=u[a]*w[c]
                    J[row,cb+18+c]+=u[a]*v[b]
    return J


def normalize_terms(y):
    # A light conditioning normalization: make ||u|| and ||v|| near 1 and absorb into w.
    z=y.copy(); r=len(y)//27
    for i in range(r):
        u,v,w=blocks(z,i)
        nu=np.linalg.norm(u); nv=np.linalg.norm(v)
        if nu>1e-12:
            u[:]=u/nu; w[:]=w*nu
        if nv>1e-12:
            v[:]=v/nv; w[:]=w*nv
        z[27*i:27*i+9]=u; z[27*i+9:27*i+18]=v; z[27*i+18:27*i+27]=w
    return z


def load_point(cont_json, t_value=None):
    d=json.loads(Path(cont_json).read_text())
    rows=d['continuation_results']
    rows=[r for r in rows if 'x' in r]
    if not rows:
        raise ValueError('continuation JSON has no stored x points; rerun with --store-points')
    if t_value is None:
        # choose successful row with smallest min pairing singular.
        rows=[r for r in rows if r['solve']['brent_residual_norm']<1e-8]
        return min(rows,key=lambda r:r['solve']['min_projective_pairing_singular'])
    return min(rows,key=lambda r:abs(r['t']-t_value))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('scheme')
    ap.add_argument('continuation_json')
    ap.add_argument('--t',type=float,default=None)
    ap.add_argument('--json-out',required=True)
    ap.add_argument('--npy-out')
    ap.add_argument('--pairs',nargs='+',default=['uv','uw','vw'])
    ap.add_argument('--max-nfev',type=int,default=2000)
    ap.add_argument('--top-removals',type=int,default=2)
    args=ap.parse_args()
    target,r=target_from_scheme(args.scheme)
    row=load_point(args.continuation_json,args.t)
    x23=np.array(row['x'],dtype=float)
    print(f'loaded t={row["t"]} rank23 residual={row["solve"]["brent_residual_norm"]:.3e} minpair={row["solve"]["min_projective_pairing_singular"]:.3e}')
    candidates=[]
    for pair in args.pairs:
        M,norms=pairing_matrix(x23,r,pair,normalized=True)
        U,S,Vt=np.linalg.svd(M,full_matrices=False)
        beta=Vt[-1,:]
        gamma=beta/np.maximum(norms,1e-300)
        order=np.argsort(-np.abs(gamma))[:args.top_removals]
        for rem in order:
            y,remove,gamma=shorten_from_relation(x23,r,pair,beta,norms,remove=int(rem))
            y=normalize_terms(y)
            init_res=residual_rank22(y,target)
            rec={'pair':pair,'remove':int(remove),'sigma_min_normalized_pairing':float(S[-1]),
                 'gamma_abs_removed':float(abs(gamma[remove])),
                 'initial_residual_norm':float(np.linalg.norm(init_res)),
                 'initial_residual_maxabs':float(np.max(np.abs(init_res))),
                 'initial_var_norm':float(np.linalg.norm(y))}
            print('candidate',rec)
            candidates.append((rec,y))
    results=[]; best=None
    for ci,(rec,y0) in enumerate(candidates):
        res=least_squares(lambda y: residual_rank22(y,target), y0, jac=jacobian_rank22,
                          method='trf', x_scale='jac', ftol=1e-13, xtol=1e-13, gtol=1e-13,
                          max_nfev=args.max_nfev, verbose=0)
        y=res.x
        final=residual_rank22(y,target)
        out=dict(rec)
        out.update({'candidate_index':ci,'success':bool(res.success),'status':int(res.status),'message':res.message,
                    'nfev':int(res.nfev),'cost':float(res.cost),
                    'final_residual_norm':float(np.linalg.norm(final)),
                    'final_residual_maxabs':float(np.max(np.abs(final))),
                    'final_var_norm':float(np.linalg.norm(y))})
        print('optimized',out)
        results.append(out)
        if best is None or out['final_residual_norm']<best[0]['final_residual_norm']:
            best=(out,y)
    if args.npy_out and best is not None:
        np.save(args.npy_out,best[1])
    summary={'scheme':args.scheme,'continuation_json':args.continuation_json,'source_t':row['t'],
             'source_rank23_residual_norm':row['solve']['brent_residual_norm'],
             'source_min_projective_pairing_singular':row['solve']['min_projective_pairing_singular'],
             'results':sorted(results,key=lambda x:x['final_residual_norm']),
             'best_npy':args.npy_out if args.npy_out else None,
             'interpretation':'A final residual near zero would be a candidate rank-22 decomposition requiring independent exactification and QMM verification. Nonzero residual indicates the near pair-defect path has not yet produced an exact rank-22 algorithm.'}
    Path(args.json_out).write_text(json.dumps(summary,indent=2)+'\n')
    print(f'wrote {args.json_out}')

if __name__=='__main__':
    main()
