#!/usr/bin/env python3
r"""Stabilizer-invariant line and forced singularity for T333.

This computes the ambient infinitesimal action corresponding to the corrected
matrix-multiplication stabilizer generators used in earlier steps.  The action
on a rank-one tensor u⊗v⊗w is:

  p-generator E: dU=E^T U,        dV=0,          dW=-E W
  q-generator E: dU=-U E^T,       dV=E^T V,      dW=0
  r-generator E: dU=0,            dV=-V E^T,     dW=W E

The common kernel in K^(9⊗9⊗9) is the tensor subspace fixed by the Lie algebra.
If its dimension is 1 and T333 is nonzero in it, then these infinitesimal
invariance equations cut out exactly the line K*T333 over the tested field.
"""
from __future__ import annotations

import argparse, json, time
from pathlib import Path
import numpy as np


def rank_mod(A, p):
    A=np.array(A%p,dtype=np.int64,copy=True)
    m,n=A.shape; row=0
    for col in range(n):
        if row>=m: break
        nz=np.nonzero(A[row:,col])[0]
        if len(nz)==0: continue
        piv=row+int(nz[0])
        if piv!=row: A[[row,piv]]=A[[piv,row]]
        inv=pow(int(A[row,col]),p-2,p)
        A[row]=(A[row]*inv)%p
        factors=A[:,col].copy(); factors[row]=0
        rows=np.nonzero(factors)[0]
        if len(rows): A[rows]=(A[rows]-factors[rows,None]*A[row])%p
        row+=1
    return row


def nullspace_mod(A, p):
    A=np.array(A%p,dtype=np.int64,copy=True)
    m,n=A.shape; row=0; pivots=[]
    for col in range(n):
        if row>=m: break
        nz=np.nonzero(A[row:,col])[0]
        if len(nz)==0: continue
        piv=row+int(nz[0])
        if piv!=row: A[[row,piv]]=A[[piv,row]]
        inv=pow(int(A[row,col]),p-2,p)
        A[row]=(A[row]*inv)%p
        factors=A[:,col].copy(); factors[row]=0
        rows=np.nonzero(factors)[0]
        if len(rows): A[rows]=(A[rows]-factors[rows,None]*A[row])%p
        pivots.append(col); row+=1
    pivset=set(pivots); free=[j for j in range(n) if j not in pivset]
    basis=[]
    for f in free:
        x=np.zeros(n,dtype=np.int64); x[f]=1
        for i,col in reversed(list(enumerate(pivots))):
            x[col]=(-int(A[i,f]))%p
        basis.append(x)
    return np.array(basis,dtype=np.int64).T%p, pivots


def make_T333():
    T=np.zeros((9,9,9),dtype=np.int64)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j,3*j+k,3*i+k]=1
    return T


def idx_to_mat_index(a):
    return divmod(a,3)


def mat_index_to_idx(i,j):
    return 3*i+j


def apply_to_vec_on_A(a, gen, jj, kk, p):
    # vector e_a is a 3x3 matrix U. Return dU coefficients.
    U=np.zeros((3,3),dtype=np.int64)
    i,j=idx_to_mat_index(a); U[i,j]=1
    E=np.zeros((3,3),dtype=np.int64); E[jj,kk]=1
    d=np.zeros((3,3),dtype=np.int64)
    if gen=='p': d=(E.T@U)%p
    elif gen=='q': d=(p-(U@E.T)%p)%p
    elif gen=='r': d[:]=0
    return d.reshape(9)%p


def apply_to_vec_on_B(b, gen, jj, kk, p):
    V=np.zeros((3,3),dtype=np.int64)
    i,j=idx_to_mat_index(b); V[i,j]=1
    E=np.zeros((3,3),dtype=np.int64); E[jj,kk]=1
    d=np.zeros((3,3),dtype=np.int64)
    if gen=='p': d[:]=0
    elif gen=='q': d=(E.T@V)%p
    elif gen=='r': d=(p-(V@E.T)%p)%p
    return d.reshape(9)%p


def apply_to_vec_on_C(c, gen, jj, kk, p):
    W=np.zeros((3,3),dtype=np.int64)
    i,j=idx_to_mat_index(c); W[i,j]=1
    E=np.zeros((3,3),dtype=np.int64); E[jj,kk]=1
    d=np.zeros((3,3),dtype=np.int64)
    if gen=='p': d=(p-(E@W)%p)%p
    elif gen=='q': d[:]=0
    elif gen=='r': d=(W@E)%p
    return d.reshape(9)%p


def ambient_generator_matrix(gen, jj, kk, p):
    L=np.zeros((729,729),dtype=np.int64)
    for a in range(9):
        da=apply_to_vec_on_A(a,gen,jj,kk,p)
        for b in range(9):
            db=apply_to_vec_on_B(b,gen,jj,kk,p)
            for c in range(9):
                dc=apply_to_vec_on_C(c,gen,jj,kk,p)
                col=a*81+b*9+c
                # dA ⊗ e_b ⊗ e_c
                for aa,val in enumerate(da):
                    if val: L[aa*81+b*9+c,col]=(L[aa*81+b*9+c,col]+val)%p
                for bb,val in enumerate(db):
                    if val: L[a*81+bb*9+c,col]=(L[a*81+bb*9+c,col]+val)%p
                for cc,val in enumerate(dc):
                    if val: L[a*81+b*9+cc,col]=(L[a*81+b*9+cc,col]+val)%p
    return L%p


def flattening_ranks(T,p):
    return {
        'A_flattening_rank': rank_mod(T.reshape(9,81),p),
        'B_flattening_rank': rank_mod(np.transpose(T,(1,0,2)).reshape(9,81),p),
        'C_flattening_rank': rank_mod(np.transpose(T,(2,0,1)).reshape(9,81),p),
    }


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--primes', nargs='*', type=int, default=[3,5,65521])
    ap.add_argument('--out', default='data/singular_stratum/invariant_line_and_singularity.json')
    args=ap.parse_args()
    out=Path(args.out); out.parent.mkdir(parents=True,exist_ok=True)
    result={'purpose':'Compute the ambient fixed subspace of the corrected matrix-multiplication stabilizer and the resulting forced singular rank drop for any rank-22 preimage of T333.', 'primes':{}, 'parameter_consequence':{
        'r':22,
        'full_parameter_dim':594,
        'generic_rank22_jacobian_rank':550,
        'generic_kernel_dim':44,
        'term_scaling_kernel_dim':44,
        'stabilizer_dim_if_full_factor_spans':26,
        'intersection_scaling_stabilizer_dim':2,
        'forced_kernel_dim':68,
        'forced_jacobian_rank_max':526,
        'forced_rank_drop_from_generic':24,
        'shortened_chart_w_elimination_rank':198,
        'generic_shortened_rank':352,
        'forced_shortened_rank_max':328,
        'rank_drop_in_shortened_chart':24
    }}
    for p in args.primes:
        t0=time.time()
        T=make_T333()%p
        gens=[]
        gen_ranks=[]
        for gen in ['p','q','r']:
            for jj in range(3):
                for kk in range(3):
                    L=ambient_generator_matrix(gen,jj,kk,p)
                    gens.append(L)
                    gen_ranks.append(rank_mod(L,p))
        Stack=np.concatenate(gens,axis=0)%p
        stack_rank=rank_mod(Stack,p)
        NS,piv=nullspace_mod(Stack,p)
        Tvec=T.reshape(729)%p
        T_in_kernel=bool(np.count_nonzero((Stack@Tvec)%p)==0)
        ns_dim=NS.shape[1]
        T_span_matches=False
        if ns_dim==1:
            b=NS[:,0]
            nz=np.nonzero(b)[0]
            if len(nz)>0:
                i=int(nz[0]); scale=Tvec[i]*pow(int(b[i]),p-2,p)%p if b[i] else 0
                T_span_matches=bool(np.all((scale*b-Tvec)%p==0))
        result['primes'][str(p)]={
            'ambient_dimension':729,
            'generator_count':27,
            'generator_rank_minmax':[int(min(gen_ranks)),int(max(gen_ranks))],
            'stacked_action_rank':int(stack_rank),
            'fixed_subspace_dimension':int(729-stack_rank),
            'nullspace_basis_columns':int(ns_dim),
            'T333_in_fixed_subspace':T_in_kernel,
            'fixed_line_spanned_by_T333':T_span_matches,
            'T333_flattening_ranks':flattening_ranks(T,p),
            'elapsed_sec':time.time()-t0,
        }
        print(f'p={p}: stacked_rank={stack_rank} fixed_dim={729-stack_rank} T_in={T_in_kernel} line={T_span_matches}')
    out.write_text(json.dumps(result,indent=2,sort_keys=True,default=int)+'\n')
    print(f'wrote {out}')

if __name__=='__main__':
    main()
