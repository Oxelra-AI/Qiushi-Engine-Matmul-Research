#!/usr/bin/env python3
"""Scan second-order Kuranishi zeros for higher-order liftability and projective pairing motion.

This is a summary-oriented companion to formal_lift_pairing.py.  It searches many
second-order zeros, tests whether the recursive formal lift succeeds to a chosen order
using only residual (non-gauge) kernel freedom, and ranks liftable directions by their
scale-insensitive movement toward two-factor pairing dependence.
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np

SCRIPT_DIR=Path(__file__).resolve().parent
sys.path.insert(0,str(SCRIPT_DIR))
from formal_lift_pairing import (  # noqa: E402
    parse_qmm, terms_to_vec, tensor_value, build_jacobian, build_rescalings,
    build_stabilizer_pullback, bilinear_Q, matrix_rank_svd, find_second_order_directions,
    formal_lift, projective_pairing_stats, eval_truncated_path
)


def setup(scheme):
    Sobj=parse_qmm(scheme)
    r=Sobj['rank']; x0=terms_to_vec(Sobj['terms'])
    J=build_jacobian(x0,r)
    U,S,Vt=np.linalg.svd(J,full_matrices=True)
    jrank=int(np.sum(S>1e-10)); kernel=Vt[jrank:].T; left_null=U[:,jrank:]
    R=build_rescalings(x0,r); G=build_stabilizer_pullback(x0,r)
    sym=np.hstack([R,G])
    sym_in_kernel=kernel.T@sym
    sym_rank=matrix_rank_svd(sym_in_kernel)
    Uc,Sc,Vtc=np.linalg.svd(sym_in_kernel,full_matrices=True)
    residual_dirs=kernel@Uc[:,sym_rank:]
    m=residual_dirs.shape[1]
    C=np.zeros((left_null.shape[1],m,m))
    for j in range(m):
        for k in range(j,m):
            val=left_null.T@bilinear_Q(residual_dirs[:,j],residual_dirs[:,k],x0,r)
            C[:,j,k]=val; C[:,k,j]=val
    Cmat=C.reshape(left_null.shape[1],m*m)
    Ueq,Seq,Vteq=np.linalg.svd(Cmat,full_matrices=False)
    eff=int(np.sum(Seq>1e-10))
    H=np.einsum('il,ijk->ljk',Ueq[:,:eff],C)
    return Sobj,r,x0,J,U,S,Vt,jrank,kernel,left_null,residual_dirs,H,{
        'jacobian_rank':jrank,'kernel_dim':kernel.shape[1],'cokernel_dim':left_null.shape[1],
        'rescaling_rank':matrix_rank_svd(R),'stabilizer_rank':matrix_rank_svd(G),
        'rescaling_J_rank':matrix_rank_svd(J@R),'stabilizer_J_rank':matrix_rank_svd(J@G),
        'combined_symmetry_rank':sym_rank,'residual_dim_corrected':m,
        'effective_second_order_quadrics':eff,
    }


def pairing_derivatives(x0,x1,r,eps=1e-5):
    out={}
    for pair in ['uv','uw','vw']:
        sp=projective_pairing_stats(x0+eps*x1,r,pair)['min_singular_col_normalized']
        sm=projective_pairing_stats(x0-eps*x1,r,pair)['min_singular_col_normalized']
        out[pair]=float((sp-sm)/(2*eps))
    return out


def orient_for_pairing_decrease(x0,x1,r):
    d=pairing_derivatives(x0,x1,r)
    if min((-v for v in d.values())) < min(d.values()):
        return x1, d
    else:
        return -x1, {k:-v for k,v in d.items()}


def summarize_lift(coeffs, target, r):
    samples=[]
    for t in [1e-3,3e-3,1e-2,3e-2,1e-1,2e-1]:
        xp=eval_truncated_path(coeffs,t)
        br=float(np.linalg.norm(tensor_value(xp,r)-target))
        pstats={p:projective_pairing_stats(xp,r,p)['min_singular_col_normalized'] for p in ['uv','uw','vw']}
        samples.append({'t':t,'brent_residual_norm':br,'min_pairing_singulars':pstats,
                        'min_over_pairs':float(min(pstats.values()))})
    return samples


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('scheme')
    ap.add_argument('--json-out',required=True)
    ap.add_argument('--starts',type=int,default=300)
    ap.add_argument('--max-order',type=int,default=12)
    ap.add_argument('--max-test',type=int,default=120)
    ap.add_argument('--seed',type=int,default=91023)
    args=ap.parse_args()
    Sobj,r,x0,J,U,S,Vt,jrank,kernel,left_null,residual_dirs,H,meta=setup(args.scheme)
    target=tensor_value(x0,r)
    print('setup',json.dumps(meta,indent=2))
    sols,records=find_second_order_directions(H,meta['residual_dim_corrected'],args.starts,args.seed)
    print(f'found {len(sols)} distinct second-order zeros from {args.starts} starts; best loss={records[0]["loss"]:.3e}')
    all_results=[]; liftable=[]
    for idx,coef in enumerate(sols[:args.max_test]):
        x1=residual_dirs@coef
        x1,deriv=orient_for_pairing_decrease(x0,x1,r)
        coeffs,info=formal_lift(x0,x1,J,U,S,Vt,jrank,residual_dirs,kernel,left_null,r,args.max_order)
        last_order=2
        max_post=info.get('order2_cokernel_norm',None)
        for row in info.get('orders',[]):
            if row['post_cokernel_norm']<1e-7 and row['linear_solve_residual_norm']<1e-7:
                last_order=row['order']
            max_post=max(max_post,row['post_cokernel_norm']) if max_post is not None else row['post_cokernel_norm']
        samples=summarize_lift(coeffs,target,r) if info['status'].startswith('lifted') else []
        min_deriv=min(deriv.values())
        rec={'index':idx,'status':info['status'],'last_good_order':last_order,
             'order2_cokernel_norm':info['order2_cokernel_norm'],
             'kernel_obstruction_map_rank':info.get('kernel_obstruction_map_rank'),
             'pairing_derivatives':deriv,'most_negative_pairing_derivative':float(min_deriv),
             'formal_order_rows':info.get('orders',[]),'samples_if_lifted':samples,
             'residual_coordinates':(residual_dirs.T@x1).tolist()}
        all_results.append(rec)
        if info['status'].startswith('lifted'):
            liftable.append(rec)
        print(f'{idx:03d}: {info["status"]:>18s} last={last_order:2d} min_dsigma={min_deriv:+.3e}')
    liftable_sorted=sorted(liftable,key=lambda z:z['most_negative_pairing_derivative'])
    all_sorted=sorted(all_results,key=lambda z:(-z['last_good_order'], z['most_negative_pairing_derivative']))
    out={'scheme':args.scheme,'search':{'starts':args.starts,'distinct_second_order_zeros':len(sols),
          'tested':min(len(sols),args.max_test),'best_second_order_records':records[:10]},
         'meta':meta,
         'base_projective_pairing':{p:projective_pairing_stats(x0,r,p) for p in ['uv','uw','vw']},
         'liftable_count':len(liftable),
         'liftable_sorted_by_pairing_motion':liftable_sorted[:20],
         'all_tested_sorted':all_sorted[:30],
         'interpretation':'A lifted finite-order series is only computational evidence. Pairing motion uses column-normalized projective columns, not raw rescaling-sensitive column norms.'}
    Path(args.json_out).write_text(json.dumps(out,indent=2)+'\n')
    print(f'liftable_count={len(liftable)} wrote {args.json_out}')

if __name__=='__main__':
    main()
