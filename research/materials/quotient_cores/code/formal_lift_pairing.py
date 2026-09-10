#!/usr/bin/env python3
"""Gauge-corrected deformation and pairing-rank experiments for 3x3 rank-23 schemes.

This script corrects the analysis stabilizer convention and treats the Kuranishi
quadratic computation only as a formal/numerical experiment, not as a proof of a
positive-dimensional exact component.

Main outputs for one QMM scheme:
  * Jacobian/kernel/cokernel dimensions.
  * Correct GL_3^3 pullback stabilizer subspace in the kernel.
  * Residual tangent space modulo term rescaling and tensor isotropy.
  * Unit-sphere search for second-order-unobstructed residual directions.
  * Recursive formal lift test to a chosen order using kernel freedom at each order.
  * Scale-insensitive two-factor pairing conditioning (column-normalized singulars)
    along the truncated formal path.

The formal recursion writes x(t)=x0 + t x1 + t^2 x2 + ... and solves coefficient
conditions for F(x(t))=F(x0) order by order.  For n>=3, if x1 is fixed, the kernel
component of x_{n-1} is chosen to kill the order-n cokernel obstruction, then x_n
is solved in an orthogonal complement using the numerical SVD pseudoinverse of J.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize


def parse_qmm(path: str):
    dims=None; rank=None; domain=None; terms=[]; cur=None
    for raw in Path(path).read_text().splitlines():
        line=raw.strip()
        if not line or line.startswith('#'):
            continue
        p=line.split()
        if p[0]=='dimensions': dims=tuple(map(int,p[1:4]))
        elif p[0]=='rank': rank=int(p[1])
        elif p[0]=='domain': domain=p[1]
        elif p[0]=='term':
            if cur is not None: terms.append(cur)
            cur={'index':int(p[1])}
        elif p[0] in ('u','v','w'):
            cur[p[0]]=np.array([float(x) for x in p[1:]], dtype=float)
    if cur is not None: terms.append(cur)
    if dims is None or rank is None or len(terms)!=rank:
        raise ValueError(f'bad QMM file {path}')
    return {'dimensions':dims,'rank':rank,'domain':domain,'terms':terms}


def terms_to_vec(terms):
    xs=[]
    for t in terms:
        xs.extend([t['u'],t['v'],t['w']])
    return np.concatenate(xs).astype(float)


def vec_term_blocks(x, i):
    cb=27*i
    return x[cb:cb+9], x[cb+9:cb+18], x[cb+18:cb+27]


def tensor_value(x, r, n=9):
    out=np.zeros(n**3)
    for i in range(r):
        u,v,w=vec_term_blocks(x,i)
        out += np.einsum('a,b,c->abc',u,v,w).reshape(-1)
    return out


def build_jacobian(x0, r, n=9):
    J=np.zeros((n**3,3*n*r), dtype=float)
    for i in range(r):
        u,v,w=vec_term_blocks(x0,i)
        cb=27*i
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    row=a*81+b*9+c
                    J[row,cb+a]+=v[b]*w[c]
                    J[row,cb+9+b]+=u[a]*w[c]
                    J[row,cb+18+c]+=u[a]*v[b]
    return J


def build_rescalings(x0, r):
    cols=[]
    for i in range(r):
        u,v,w=vec_term_blocks(x0,i)
        d1=np.zeros_like(x0); d1[27*i:27*i+9]=u; d1[27*i+18:27*i+27]=-w
        d2=np.zeros_like(x0); d2[27*i+9:27*i+18]=v; d2[27*i+18:27*i+27]=-w
        cols.extend([d1,d2])
    return np.array(cols).T


def build_stabilizer_pullback(x0, r, n=3):
    """Correct infinitesimal tensor-isotropy action for row-major coefficient covectors.

    If A -> P A Q^{-1}, B -> Q B R^{-1}, C -> P C R^{-1}, coefficient covectors
    transform contragrediently.  One exact kernel formula in QMM row-major coordinates is
       dU = p^T U - U q^T,
       dV = q^T V - V r^T,
       dW = -p W + W r.
    The 27 generated columns have rank 26; together with the 46 term rescalings they
    span rank 70 for cn122 (matching research_record exact modular computation).
    """
    cols=[]
    for gen in ['p','q','r']:
        for jj in range(n):
            for kk in range(n):
                E=np.zeros((n,n)); E[jj,kk]=1.0
                d=np.zeros_like(x0)
                for i in range(r):
                    u,v,w=vec_term_blocks(x0,i)
                    U=u.reshape(n,n); V=v.reshape(n,n); W=w.reshape(n,n)
                    dU=np.zeros((n,n)); dV=np.zeros((n,n)); dW=np.zeros((n,n))
                    if gen=='p':
                        dU=E.T@U
                        dW=-(E@W)
                    elif gen=='q':
                        dU=-(U@E.T)
                        dV=E.T@V
                    else:
                        dV=-(V@E.T)
                        dW=W@E
                    d[27*i:27*i+9]+=dU.reshape(9)
                    d[27*i+9:27*i+18]+=dV.reshape(9)
                    d[27*i+18:27*i+27]+=dW.reshape(9)
                cols.append(d)
    return np.array(cols).T


def bilinear_Q(x, y, base, r, n=9):
    """Coefficient of order st in F(base+s*x+t*y), symmetrized bilinear."""
    out=np.zeros(n**3)
    for i in range(r):
        u0,v0,w0=vec_term_blocks(base,i)
        ux,vx,wx=vec_term_blocks(x,i)
        uy,vy,wy=vec_term_blocks(y,i)
        out += 0.5*np.einsum('a,b,c->abc',ux,vy,w0).reshape(-1)
        out += 0.5*np.einsum('a,b,c->abc',uy,vx,w0).reshape(-1)
        out += 0.5*np.einsum('a,b,c->abc',ux,v0,wy).reshape(-1)
        out += 0.5*np.einsum('a,b,c->abc',uy,v0,wx).reshape(-1)
        out += 0.5*np.einsum('a,b,c->abc',u0,vx,wy).reshape(-1)
        out += 0.5*np.einsum('a,b,c->abc',u0,vy,wx).reshape(-1)
    return out


def coeff_source(coeffs, order, r, n=9):
    """Tensor coefficient at t^order using available coeffs[0..order-1].

    coeffs[0] is x0.  Since coeffs[order] is absent, this excludes the linear
    J*x_order part automatically.
    """
    out=np.zeros(n**3)
    maxidx=len(coeffs)-1
    for i in range(r):
        u=[None]*(maxidx+1); v=[None]*(maxidx+1); w=[None]*(maxidx+1)
        for k,cx in enumerate(coeffs):
            u[k],v[k],w[k]=vec_term_blocks(cx,i)
        for a in range(maxidx+1):
            for b in range(maxidx+1):
                c=order-a-b
                if c<0 or c>maxidx:
                    continue
                out += np.einsum('p,q,r->pqr',u[a],v[b],w[c]).reshape(-1)
    return out


def pinv_solve_from_svd(U,S,Vt,rank,b):
    return Vt[:rank].T @ ((U[:,:rank].T @ b) / S[:rank])


def matrix_rank_svd(A,tol=1e-10):
    if min(A.shape)==0:
        return 0
    return int(np.sum(np.linalg.svd(A,compute_uv=False)>tol))


def projective_pairing_stats(x, r, pair):
    offsets={'u':0,'v':9,'w':18}
    a,b=pair[0],pair[1]
    cols=[]; raw_norms=[]
    for i in range(r):
        fi=x[27*i+offsets[a]:27*i+offsets[a]+9]
        gi=x[27*i+offsets[b]:27*i+offsets[b]+9]
        col=np.outer(fi,gi).reshape(-1)
        norm=np.linalg.norm(col)
        raw_norms.append(float(norm))
        if norm>1e-14:
            col=col/norm
        cols.append(col)
    M=np.array(cols).T
    s=np.linalg.svd(M,compute_uv=False)
    return {
        'min_singular_col_normalized':float(s[-1]),
        'max_singular_col_normalized':float(s[0]),
        'condition_col_normalized':float(s[0]/max(s[-1],1e-300)),
        'min_pair_column_norm':float(min(raw_norms)),
        'max_pair_column_norm':float(max(raw_norms)),
    }


def find_second_order_directions(H, m, n_starts, seed):
    def vals(x):
        return np.einsum('ijk,j,k->i',H,x,x)
    def loss(x):
        f=vals(x)
        return 0.5*float(np.dot(f,f))
    def grad(x):
        f=vals(x)
        return 2*np.einsum('ijk,i,k->j',H,f,x)
    cons={'type':'eq','fun':lambda x: float(np.dot(x,x)-1.0), 'jac':lambda x: 2*x}
    rng=np.random.default_rng(seed)
    sols=[]; records=[]
    for t in range(n_starts):
        x0=rng.normal(size=m); x0/=np.linalg.norm(x0)
        res=minimize(loss,x0,jac=grad,constraints=[cons],method='SLSQP',
                     options={'maxiter':1000,'ftol':1e-14,'disp':False})
        x=res.x/np.linalg.norm(res.x)
        f=vals(x); val=0.5*float(np.dot(f,f))
        records.append({'trial':t,'success':bool(res.success),'loss':val,'nit':int(getattr(res,'nit',-1))})
        if val<1e-20:
            if all(abs(float(np.dot(x,y)))<0.999 for y in sols):
                sols.append(x)
    records.sort(key=lambda z:z['loss'])
    return sols, records


def formal_lift(x0, x1, J, U, S, Vt, jrank, allowed_kernel, obstruction_kernel, left_null, r, max_order):
    coeffs=[x0.copy(), x1.copy()]
    # order 2 solvability and particular x2
    R2=coeff_source(coeffs,2,r)
    c2=left_null.T@R2
    out={'order2_cokernel_norm':float(np.linalg.norm(c2)), 'orders':[]}
    if np.linalg.norm(c2)>1e-8:
        out['status']='fails_order2'
        return coeffs,out
    x2=-pinv_solve_from_svd(U,S,Vt,jrank,R2)
    coeffs.append(x2)
    # A maps allowed kernel correction to x_{n-1} to the order-n cokernel obstruction.
    # Term rescaling and tensor-isotropy directions are included in the raw kernel but do not
    # change the order-n obstruction from the fixed x1; using the residual quotient basis avoids
    # enormous coefficient corrections from nearly-null gauge columns.
    A=np.column_stack([left_null.T@(2.0*bilinear_Q(x1,allowed_kernel[:,j],x0,r)) for j in range(allowed_kernel.shape[1])])
    out['kernel_obstruction_map_rank']=matrix_rank_svd(A)
    out['allowed_kernel_dim']=int(allowed_kernel.shape[1])
    out['obstruction_kernel_dim']=int(obstruction_kernel.shape[1])
    out['cokernel_dim']=int(left_null.shape[1])
    for n in range(3,max_order+1):
        Rn0=coeff_source(coeffs,n,r)
        g=left_null.T@Rn0
        y, residuals, _, _ = np.linalg.lstsq(A, -g, rcond=1e-12)
        coeffs[n-1]=coeffs[n-1]+allowed_kernel@y
        Rn=coeff_source(coeffs,n,r)
        cn=left_null.T@Rn
        xn=-pinv_solve_from_svd(U,S,Vt,jrank,Rn)
        coeffs.append(xn)
        equation_res=J@xn+Rn
        out['orders'].append({
            'order':n,
            'pre_cokernel_norm':float(np.linalg.norm(g)),
            'post_cokernel_norm':float(np.linalg.norm(cn)),
            'linear_solve_residual_norm':float(np.linalg.norm(equation_res)),
            'allowed_kernel_correction_norm':float(np.linalg.norm(allowed_kernel@y)),
            'coefficient_norm':float(np.linalg.norm(coeffs[n-1])),
            'next_particular_norm':float(np.linalg.norm(xn)),
        })
        if np.linalg.norm(cn)>1e-7 or np.linalg.norm(equation_res)>1e-7:
            out['status']='fails_order_%d'%n
            return coeffs,out
    out['status']='lifted_to_order_%d'%max_order
    return coeffs,out


def eval_truncated_path(coeffs,t):
    x=np.zeros_like(coeffs[0])
    powt=1.0
    for c in coeffs:
        x += powt*c
        powt *= t
    return x


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('scheme')
    ap.add_argument('--json-out',required=True)
    ap.add_argument('--starts',type=int,default=120)
    ap.add_argument('--directions',type=int,default=5)
    ap.add_argument('--max-order',type=int,default=8)
    ap.add_argument('--seed',type=int,default=90402)
    args=ap.parse_args()

    Sobj=parse_qmm(args.scheme)
    r=Sobj['rank']; x0=terms_to_vec(Sobj['terms']); target=tensor_value(x0,r)
    J=build_jacobian(x0,r)
    U,S,Vt=np.linalg.svd(J,full_matrices=True)
    jrank=int(np.sum(S>1e-10)); kernel=Vt[jrank:].T; left_null=U[:,jrank:]
    print(f'J rank={jrank}, kernel={kernel.shape[1]}, coker={left_null.shape[1]}')

    R=build_rescalings(x0,r); G=build_stabilizer_pullback(x0,r)
    print(f'rescaling rank={matrix_rank_svd(R)}, J*R rank={matrix_rank_svd(J@R)}')
    print(f'stabilizer rank={matrix_rank_svd(G)}, J*G rank={matrix_rank_svd(J@G)}, max|JG|={np.max(np.abs(J@G)):.2e}')
    sym=np.hstack([R,G])
    sym_rank_param=matrix_rank_svd(sym)
    sym_in_kernel=kernel.T@sym
    sym_rank=matrix_rank_svd(sym_in_kernel)
    print(f'combined symmetry rank in parameter space={sym_rank_param}, in kernel coordinates={sym_rank}')
    Uc,Sc,Vtc=np.linalg.svd(sym_in_kernel,full_matrices=True)
    residual_dirs=kernel@Uc[:,sym_rank:]
    m=residual_dirs.shape[1]
    print(f'residual tangent dim modulo scaling+isotropy={m}')

    # Kuranishi quadratic tensor on residual directions.
    C=np.zeros((left_null.shape[1],m,m))
    for j in range(m):
        for k in range(j,m):
            val=left_null.T@bilinear_Q(residual_dirs[:,j],residual_dirs[:,k],x0,r)
            C[:,j,k]=val; C[:,k,j]=val
    Cmat=C.reshape(left_null.shape[1],m*m)
    Ueq,Seq,Vteq=np.linalg.svd(Cmat,full_matrices=False)
    eff=int(np.sum(Seq>1e-10))
    H=np.einsum('il,ijk->ljk',Ueq[:,:eff],C)
    print(f'effective second-order quadrics={eff} in residual variables={m}')

    sols, opt_records=find_second_order_directions(H,m,args.starts,args.seed)
    print(f'sphere search found {len(sols)} distinct second-order zeros; best losses:', [rec['loss'] for rec in opt_records[:5]])

    base_pair={pair:projective_pairing_stats(x0,r,pair) for pair in ['uv','uw','vw']}
    direction_results=[]
    for idx,coef in enumerate(sols[:args.directions]):
        x1=residual_dirs@coef
        # orient x1 by whichever sign gives a lower minimum normalized pairing singular at t=0.05.
        def score(sign):
            xp=x0+0.05*sign*x1
            return min(projective_pairing_stats(xp,r,p)['min_singular_col_normalized'] for p in ['uv','uw','vw'])
        if score(-1)<score(+1):
            coef=-coef; x1=-x1
        coeffs,lift_info=formal_lift(x0,x1,J,U,S,Vt,jrank,residual_dirs,kernel,left_null,r,args.max_order)
        path_samples=[]
        for t in [1e-3,3e-3,1e-2,3e-2,1e-1]:
            xp=eval_truncated_path(coeffs,t)
            residual=float(np.linalg.norm(tensor_value(xp,r)-target))
            pairs={pair:projective_pairing_stats(xp,r,pair) for pair in ['uv','uw','vw']}
            path_samples.append({'t':t,'brent_residual_norm':residual,'pairing':pairs})
        # first-order projective-singular tendency by symmetric finite difference.
        tend={}
        eps=1e-4
        for pair in ['uv','uw','vw']:
            sp=projective_pairing_stats(x0+eps*x1,r,pair)['min_singular_col_normalized']
            sm=projective_pairing_stats(x0-eps*x1,r,pair)['min_singular_col_normalized']
            tend[pair]=float((sp-sm)/(2*eps))
        direction_results.append({
            'index':idx,
            'residual_coordinates':coef.tolist(),
            'second_order_cokernel_norm':float(np.linalg.norm(np.einsum('ijk,j,k->i',H,coef,coef))),
            'formal_lift':lift_info,
            'pairing_min_singular_derivative_at_0':tend,
            'path_samples':path_samples,
        })
        print(f'direction {idx}: {lift_info["status"]}, order2 coker={lift_info["order2_cokernel_norm"]:.2e}, A_rank={lift_info.get("kernel_obstruction_map_rank")}, min sample sigmas={[min(s["pairing"][p]["min_singular_col_normalized"] for p in ["uv","uw","vw"]) for s in path_samples]}')

    results={
        'scheme':args.scheme,
        'rank':r,
        'jacobian_rank':jrank,
        'kernel_dim':int(kernel.shape[1]),
        'cokernel_dim':int(left_null.shape[1]),
        'rescaling_rank':matrix_rank_svd(R),
        'rescaling_J_rank':matrix_rank_svd(J@R),
        'stabilizer_pullback_rank':matrix_rank_svd(G),
        'stabilizer_pullback_J_rank':matrix_rank_svd(J@G),
        'combined_symmetry_rank':int(sym_rank),
        'residual_dim_corrected':int(m),
        'effective_second_order_quadrics':int(eff),
        'sphere_search':{
            'starts':args.starts,
            'n_distinct_zeros':len(sols),
            'best_records':opt_records[:10],
        },
        'base_projective_pairing':base_pair,
        'directions':direction_results,
        'interpretation_warning':'Numerical formal lifts to finite order are evidence for higher-order compatibility only; they are not exact algebraic proof of a positive-dimensional component or of rank-22.',
    }
    Path(args.json_out).write_text(json.dumps(results,indent=2)+'\n')
    print(f'wrote {args.json_out}')

if __name__=='__main__':
    main()
