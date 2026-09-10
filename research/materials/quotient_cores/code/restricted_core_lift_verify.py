#!/usr/bin/env python3
"""Rebuild Wang codimension-one cores and verify the core-to-full lift over F2.

For a mask m with pivot p=msb(m), A-side restriction in the existing related analysis/related analysis
convention is

    T_restr[i] = T[i] + m_i T[p] for i != p,  T_restr[p]=0.

Thus

    T = T_restr + m \otimes T[p,:,:].

If an 8x9x9 core has a rank-r CPD, embedding its A-factors in the complement
of p and adding a rank-3 CPD of the removed A-slice gives a rank-(r+3) CPD of
T_<3,3,3>.  This script independently rebuilds the cores from the standard
T333 tensor, compares them coordinatewise to research_record's .npy files, and runs a
positive-control lift using an existing E11 rank-21 flip-cpd row.
"""
from __future__ import annotations

import argparse, json
from pathlib import Path
from typing import Iterable

import numpy as np


def build_t333_f2() -> np.ndarray:
    T=np.zeros((9,9,9),dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a=3*i+j
                b=3*j+k
                c=3*i+k
                T[a,b,c]=1
    return T


def apply_constraint(T:np.ndarray, mask:int):
    pivot=mask.bit_length()-1
    result=T.copy()
    free=mask^(1<<pivot)
    for i in range(9):
        if (free>>i)&1:
            result[i]^=result[pivot]
    result[pivot]=0
    comp=[i for i in range(9) if i!=pivot]
    return result[comp].copy(), result, pivot, comp


def vec_from_mask(mask:int, n:int) -> np.ndarray:
    return np.array([(int(mask)>>i)&1 for i in range(n)],dtype=np.uint8)


def mask_from_vec(vec:Iterable[int]) -> int:
    out=0
    for i,b in enumerate(vec):
        if int(b)&1:
            out |= 1<<i
    return out


def row_to_terms(row:np.ndarray, rank:int):
    vals=[int(x) for x in row.tolist()]
    if len(vals)!=3*rank:
        raise ValueError(f'row length {len(vals)} != {3*rank}')
    return [tuple(vals[3*i:3*i+3]) for i in range(rank)]


def embed_core_u(u_mask:int, comp:list[int]) -> int:
    full=0
    for k,bit in enumerate(comp):
        if (int(u_mask)>>k)&1:
            full |= 1<<bit
    return full


def removed_slice_terms(mask:int, pivot:int):
    """Three rank-one terms for mask ⊗ T[pivot,:,:]."""
    i,j=divmod(pivot,3)   # A coordinate A_{i,j}
    terms=[]
    for k in range(3):
        b=3*j+k           # B coordinate B_{j,k}
        c=3*i+k           # C coordinate C_{i,k}
        terms.append((mask,1<<b,1<<c))
    return terms


def reconstruct(terms:list[tuple[int,int,int]], shape=(9,9,9)) -> np.ndarray:
    na,nb,nc=shape
    T=np.zeros(shape,dtype=np.uint8)
    for u,v,w in terms:
        for a in range(na):
            if not ((int(u)>>a)&1):
                continue
            for b in range(nb):
                if not ((int(v)>>b)&1):
                    continue
                for c in range(nc):
                    if (int(w)>>c)&1:
                        T[a,b,c]^=1
    return T


def verify_terms_against_tensor(terms, T):
    R=reconstruct(terms, T.shape)
    diff=R^T
    return bool(not diff.any()), int(diff.sum())


def save_npz(path:Path, terms:list[tuple[int,int,int]], dims=(9,9,9)):
    U=np.zeros((len(terms),dims[0]),dtype=np.uint8)
    V=np.zeros((len(terms),dims[1]),dtype=np.uint8)
    W=np.zeros((len(terms),dims[2]),dtype=np.uint8)
    for t,(u,v,w) in enumerate(terms):
        U[t]=vec_from_mask(u,dims[0])
        V[t]=vec_from_mask(v,dims[1])
        W[t]=vec_from_mask(w,dims[2])
    path.parent.mkdir(parents=True,exist_ok=True)
    np.savez(path,U=U,V=V,W=W)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--outdir',default='data/lift_verify')
    ap.add_argument('--e11-pool',default='data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy')
    ap.add_argument('--pool-row',type=int,default=0)
    args=ap.parse_args()
    outdir=Path(args.outdir); outdir.mkdir(parents=True,exist_ok=True)

    T=build_t333_f2()
    masks={
        'E11':('data/restricted_cores/mask_001_E11_core.npy',1),
        'E12_E21':('data/restricted_cores/mask_010_E12_E21_core.npy',10),
        'E13_E22_E31':('data/restricted_cores/mask_084_E13_E22_E31_core.npy',84),
    }
    core_checks={}
    for name,(path,mask) in masks.items():
        rebuilt, full_restr, pivot, comp=apply_constraint(T,mask)
        peer=np.load(path).astype(np.uint8)&1
        eq=bool(np.array_equal(rebuilt,peer))
        diff=int(np.sum(rebuilt^peer))
        mask_vec=vec_from_mask(mask,9)
        recon=full_restr ^ np.einsum('a,bc->abc',mask_vec,T[pivot]).astype(np.uint8)
        rec_eq=bool(np.array_equal(recon,T))
        rem_terms=removed_slice_terms(mask,pivot)
        rem_ok,rem_diff=verify_terms_against_tensor(rem_terms, np.einsum('a,bc->abc',mask_vec,T[pivot]).astype(np.uint8))
        core_checks[name]={
            'mask':mask,'pivot':pivot,'complement':comp,
            'peer_core_path':path,'rebuilt_equals_peer':eq,'coordinate_diff_count':diff,
            'full_reconstruction_identity_verified':rec_eq,
            'removed_slice_terms':rem_terms,'removed_slice_rank_terms':len(rem_terms),
            'removed_slice_term_verification':rem_ok,'removed_slice_diff_count':rem_diff,
            'core_shape':list(rebuilt.shape),'core_nnz':int(rebuilt.sum())
        }
        print(name, core_checks[name])
        if not eq or not rec_eq or not rem_ok:
            raise SystemExit(f'core/lift identity check failed for {name}')

    # Positive-control lift: take an existing exact E11 rank-21 core CPD row and lift to full rank 24.
    pool=np.load(args.e11_pool)
    row=pool[args.pool_row]
    rank=len(row)//3
    e11_path,e11_mask=masks['E11']
    core, full_restr, pivot, comp=apply_constraint(T,e11_mask)
    core_terms=row_to_terms(row,rank)
    # Verify core row in 8x9x9 coordinates first.
    core_recon=np.zeros_like(core)
    for u,v,w in core_terms:
        uu=vec_from_mask(u,8).reshape(8,1,1)
        vv=vec_from_mask(v,9).reshape(1,9,1)
        ww=vec_from_mask(w,9).reshape(1,1,9)
        core_recon ^= (uu*vv*ww).astype(np.uint8)
    core_ok=bool(np.array_equal(core_recon,core))
    core_diff=int(np.sum(core_recon^core))
    full_terms=[(embed_core_u(u,comp),v,w) for (u,v,w) in core_terms] + removed_slice_terms(e11_mask,pivot)
    full_ok,full_diff=verify_terms_against_tensor(full_terms,T)
    npz_path=outdir/'e11_rank21_poolrow0_lift_rank24_full_t333.npz'
    save_npz(npz_path, full_terms)
    lift_record={
        'statement':'Any rank-r CPD of the E11 core in the A-complement lifts over F2 to a rank-(r+3) CPD of T333 by embedding A-factors with a00=0 and adding the three elementary products for the removed A00 slice.',
        'positive_control':{
            'core':'E11','pool':args.e11_pool,'pool_row':args.pool_row,'core_rank':rank,
            'core_cpd_verified':core_ok,'core_diff_count':core_diff,
            'full_rank_after_lift':len(full_terms),'full_t333_verified':full_ok,'full_diff_count':full_diff,
            'full_npz':str(npz_path),
            'added_removed_slice_terms':removed_slice_terms(e11_mask,pivot)
        },
        'all_core_coordinate_checks':core_checks,
    }
    (outdir/'lift_verification.json').write_text(json.dumps(lift_record,indent=2)+'\n')
    print(json.dumps(lift_record['positive_control'],indent=2))
    print(f'wrote {outdir/"lift_verification.json"}')
    if not core_ok or not full_ok:
        raise SystemExit('positive control lift failed')

if __name__=='__main__':
    main()
