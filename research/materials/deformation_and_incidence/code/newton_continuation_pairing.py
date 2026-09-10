#!/usr/bin/env python3
"""Gauge-fixed numerical continuation of exact rank-23 decompositions near a known scheme.

Starting from a second-order/formally liftable residual tangent direction saved by
scan_liftable_directions.py, solve the full Brent equations F(x)=T together with a
local slice:
  * orthogonality to the 70-dimensional rescaling+isotropy symmetry subspace;
  * one arclength/projection condition <x-x0, x1>=t.

This distinguishes actual nearby decomposition points from formal second-order zeros.
Pairing proximity is measured by singular values of column-normalized two-factor
pairing matrices, so term rescaling cannot fake rank loss.
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np
from scipy.optimize import least_squares

SCRIPT_DIR=Path(__file__).resolve().parent
sys.path.insert(0,str(SCRIPT_DIR))
from formal_lift_pairing import (  # noqa: E402
    parse_qmm, terms_to_vec, tensor_value, build_jacobian, build_rescalings,
    build_stabilizer_pullback, matrix_rank_svd, projective_pairing_stats,
    eval_truncated_path, formal_lift, bilinear_Q
)


def setup_local(scheme):
    Sobj=parse_qmm(scheme)
    r=Sobj['rank']; x0=terms_to_vec(Sobj['terms']); target=tensor_value(x0,r)
    J0=build_jacobian(x0,r)
    U,S,Vt=np.linalg.svd(J0,full_matrices=True)
    jrank=int(np.sum(S>1e-10)); kernel=Vt[jrank:].T; left_null=U[:,jrank:]
    R=build_rescalings(x0,r); G=build_stabilizer_pullback(x0,r)
    sym=np.hstack([R,G])
    Usym,Ssym,Vtsym=np.linalg.svd(sym,full_matrices=False)
    srank=int(np.sum(Ssym>1e-10)); sym_basis=Usym[:,:srank]
    sym_in_kernel=kernel.T@sym
    Uc,Sc,Vtc=np.linalg.svd(sym_in_kernel,full_matrices=True)
    qrank=int(np.sum(Sc>1e-10)); residual_dirs=kernel@Uc[:,qrank:]
    return Sobj,r,x0,target,J0,U,S,Vt,jrank,kernel,left_null,sym_basis,residual_dirs,{
        'jacobian_rank':jrank,'kernel_dim':kernel.shape[1],'cokernel_dim':left_null.shape[1],
        'symmetry_rank':srank,'residual_dim':residual_dirs.shape[1]
    }


def load_direction(scan_json, selector, residual_dirs):
    d=json.loads(Path(scan_json).read_text())
    if selector.startswith('ranked:'):
        k=int(selector.split(':',1)[1])
        rec=d['liftable_sorted_by_pairing_motion'][k]
    elif selector.startswith('index:'):
        idx=int(selector.split(':',1)[1])
        rows=d.get('all_tested_sorted',[]) + d.get('liftable_sorted_by_pairing_motion',[])
        hits=[r for r in rows if r.get('index')==idx]
        if not hits:
            raise ValueError(f'index {idx} not found in {scan_json}')
        rec=hits[0]
    else:
        raise ValueError('selector must be ranked:k or index:k')
    coords=np.array(rec['residual_coordinates'],dtype=float)
    # Coordinates were saved as residual_dirs.T @ x1 after sign orientation.
    x1=residual_dirs@coords
    x1=x1/np.linalg.norm(x1)
    return rec,x1,coords/np.linalg.norm(coords)


def residual_and_jac_builder(x0,target,r,sym_basis,x1,gauge_weight=1.0,arc_weight=10.0):
    nvar=len(x0)
    def fun(x,t):
        F=tensor_value(x,r)-target
        gauge=sym_basis.T@(x-x0)
        arc=np.array([np.dot(x-x0,x1)-t])
        return np.concatenate([F,gauge_weight*gauge,arc_weight*arc])
    def jac(x,t):
        J=build_jacobian(x,r)
        rows=[J, gauge_weight*sym_basis.T, arc_weight*x1.reshape(1,nvar)]
        return np.vstack(rows)
    return fun,jac


def summarize_point(x,x0,target,r,sym_basis,x1,t):
    F=tensor_value(x,r)-target
    gauge=sym_basis.T@(x-x0)
    arc=float(np.dot(x-x0,x1)-t)
    pair={p:projective_pairing_stats(x,r,p) for p in ['uv','uw','vw']}
    return {
        't':float(t),
        'brent_residual_norm':float(np.linalg.norm(F)),
        'brent_residual_maxabs':float(np.max(np.abs(F))),
        'gauge_norm':float(np.linalg.norm(gauge)),
        'arc_residual':arc,
        'step_norm_from_base':float(np.linalg.norm(x-x0)),
        'pairing':pair,
        'min_projective_pairing_singular':float(min(pair[p]['min_singular_col_normalized'] for p in pair)),
        'min_pair':min(pair.keys(), key=lambda p: pair[p]['min_singular_col_normalized']),
    }


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('scheme')
    ap.add_argument('scan_json')
    ap.add_argument('--selector',default='ranked:0')
    ap.add_argument('--json-out',required=True)
    ap.add_argument('--t-values',nargs='+',type=float,default=[0.001,0.003,0.01,0.03,0.1,0.2,0.4,0.7,1.0])
    ap.add_argument('--max-order-init',type=int,default=12)
    ap.add_argument('--max-nfev',type=int,default=300)
    ap.add_argument('--store-points', action='store_true', help='Store full 621-coordinate solution vectors in the JSON output')
    args=ap.parse_args()

    Sobj,r,x0,target,J0,U,S,Vt,jrank,kernel,left_null,sym_basis,residual_dirs,meta=setup_local(args.scheme)
    rec,x1,coords=load_direction(args.scan_json,args.selector,residual_dirs)
    coeffs,lift_info=formal_lift(x0,x1,J0,U,S,Vt,jrank,residual_dirs,kernel,left_null,r,args.max_order_init)
    print('meta',json.dumps(meta),'selected',{'selector':args.selector,'source_index':rec.get('index'),'source_status':rec.get('status'),'source_min_deriv':rec.get('most_negative_pairing_derivative')})
    fun,jac=residual_and_jac_builder(x0,target,r,sym_basis,x1)
    results=[]
    x_prev=x0.copy()
    success_prefix=True
    for t in args.t_values:
        # Use the formal truncated point if available and reasonably small; otherwise extrapolate from previous.
        x_init=eval_truncated_path(coeffs,t) if lift_info['status'].startswith('lifted') else x0+t*x1
        if results and results[-1]['solve']['brent_residual_norm']<1e-8:
            # previous exact point is usually the best continuation seed; add arclength delta along x1.
            x_init=x_prev+(t-results[-1]['t'])*x1
        res=least_squares(lambda x: fun(x,t), x_init, jac=lambda x: jac(x,t), method='trf',
                          x_scale='jac', ftol=1e-13, xtol=1e-13, gtol=1e-13,
                          max_nfev=args.max_nfev, verbose=0)
        x=res.x
        summ=summarize_point(x,x0,target,r,sym_basis,x1,t)
        x_prev=x.copy()
        solve={'success':bool(res.success),'status':int(res.status),'message':res.message,
               'nfev':int(res.nfev),'cost':float(res.cost),**summ}
        point_record={'t':float(t),'solve':solve}
        if args.store_points:
            point_record['x']=x.tolist()
        results.append(point_record)
        print(f't={t:g} success={res.success} brent={solve["brent_residual_norm"]:.3e} max={solve["brent_residual_maxabs"]:.3e} gauge={solve["gauge_norm"]:.3e} arc={solve["arc_residual"]:.3e} minpair={solve["min_projective_pairing_singular"]:.6g} {solve["min_pair"]} nfev={res.nfev}')
        if solve['brent_residual_norm']>1e-7 or solve['gauge_norm']>1e-7 or abs(solve['arc_residual'])>1e-7:
            success_prefix=False
            # continue one more may be unhelpful; break to avoid wandering in non-solution space.
            break
    out={'scheme':args.scheme,'scan_json':args.scan_json,'selector':args.selector,
         'selected_source_record':{k:v for k,v in rec.items() if k not in ('formal_order_rows','samples_if_lifted','residual_coordinates')},
         'meta':meta,'formal_lift_initialization':lift_info,
         'base_pairing':{p:projective_pairing_stats(x0,r,p) for p in ['uv','uw','vw']},
         'continuation_results':results,
         'success_prefix_all_requested':success_prefix,
         'interpretation':'A small-residual gauge-fixed path is numerical evidence for nearby exact decomposition points in this local slice. Pairing singulars are column-normalized; exact rank defect would still require algebraic reconstruction/verification.'}
    Path(args.json_out).write_text(json.dumps(out,indent=2)+'\n')
    print(f'wrote {args.json_out}')

if __name__=='__main__':
    main()
