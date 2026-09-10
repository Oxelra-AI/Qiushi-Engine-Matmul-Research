#!/usr/bin/env python3
r"""analysis: pilot computations for symmetry-quotient gauge charts.

This script is not a rank-22 search.  It builds the linear algebra needed for
full-span, full-UV-rank gauge charts of the shortened 22-term incidence

    F(U,V) = T_{333,\bar R} - P_{\bar R}(U,V) M(U,V)^{-1} T_{333,R} = 0.

At a hypothetical full-span rank-22 solution for T333, the shortened Jacobian
has a 68-dimensional gauge kernel: 44 term scalings plus 24 effective
noncentral matrix-multiplication stabilizer directions.  A transverse quotient
chart fixes 68 independent coordinates along this gauge tangent, so a smooth
point of the residual system becomes isolated.

The script verifies the dimension and coordinate-slice mechanics on:
  * random full-span rank-22 controls (only term scalings are true kernel for
    their own random tensor, but the combined 68-dimensional gauge tangent is
    available as a slice model);
  * cn122 rank-23, where the same gauge construction removes the known
    70-dimensional rank-23 scaling+stabilizer tangent but leaves cn122's extra
    24 local deformation directions;
  * the natural 27-term decomposition, which has enlarged stabilizer/scaling
    intersection and illustrates the termwise-aligned exceptional stratum.

All arithmetic is modular over an odd prime.  The corrected row-major
stabilizer convention from analysis is used:
    dU = P0^T U - U Q0^T,
    dV = Q0^T V - V R0^T.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
import rank22_singular_stratum_v2 as s19  # noqa: E402


def vec9(M: np.ndarray) -> np.ndarray:
    return np.asarray(M, dtype=np.int64).reshape(9)


def natural_27() -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    U=[]; V=[]; W=[]
    for i in range(3):
        for j in range(3):
            for k in range(3):
                u=np.zeros((3,3), dtype=np.int64); u[i,j]=1
                v=np.zeros((3,3), dtype=np.int64); v[j,k]=1
                w=np.zeros((3,3), dtype=np.int64); w[i,k]=1
                U.append(vec9(u)); V.append(vec9(v)); W.append(vec9(w))
    return np.array(U,dtype=np.int64), np.array(V,dtype=np.int64), np.array(W,dtype=np.int64)


def gauge_uv_columns(U: np.ndarray, V: np.ndarray, p: int) -> Dict[str, np.ndarray]:
    """Return scaling, stabilizer, and combined UV-variable gauge columns.

    Variables are ordered termwise as (u_i[0:9], v_i[0:9]), i=0..r-1.
    The stabilizer columns use the corrected QMM row-major convention.
    """
    r=U.shape[0]
    scale=[]
    for i in range(r):
        col=np.zeros(18*r,dtype=np.int64)
        col[18*i:18*i+9]=U[i]%p
        scale.append(col)
        col=np.zeros(18*r,dtype=np.int64)
        col[18*i+9:18*i+18]=V[i]%p
        scale.append(col)
    stab=[]
    for gen in ['P','Q','R']:
        for a in range(3):
            for b in range(3):
                E=np.zeros((3,3),dtype=np.int64); E[a,b]=1
                col=np.zeros(18*r,dtype=np.int64)
                for i in range(r):
                    Ui=(U[i]%p).reshape(3,3)
                    Vi=(V[i]%p).reshape(3,3)
                    dU=np.zeros((3,3),dtype=np.int64)
                    dV=np.zeros((3,3),dtype=np.int64)
                    if gen=='P':
                        dU=(E.T @ Ui) % p
                    elif gen=='Q':
                        dU=(p - (Ui @ E.T) % p) % p
                        dV=(E.T @ Vi) % p
                    else:
                        dV=(p - (Vi @ E.T) % p) % p
                    col[18*i:18*i+9]=vec9(dU)
                    col[18*i+9:18*i+18]=vec9(dV)
                stab.append(col%p)
    S=np.array(scale,dtype=np.int64).T%p if scale else np.zeros((18*r,0),dtype=np.int64)
    H=np.array(stab,dtype=np.int64).T%p if stab else np.zeros((18*r,0),dtype=np.int64)
    C=np.concatenate([S,H],axis=1)%p
    return {'scale':S, 'stab':H, 'combined':C}


def coordinate_pivots_for_column_space(G: np.ndarray, p: int) -> List[int]:
    """Select variable coordinates whose restrictions separate col(G)."""
    rank=s19.rank_mod(G,p)
    piv=s19.pivot_columns_rref(G.T,p)
    if len(piv) != rank:
        raise RuntimeError(f'pivot length {len(piv)} != rank {rank}')
    if s19.rank_mod(G[piv,:],p) != rank:
        raise RuntimeError('selected coordinate rows do not have full gauge rank')
    return [int(x) for x in piv]


def coord_row_matrix(nvars: int, coords: List[int], p: int) -> np.ndarray:
    E=np.zeros((len(coords), nvars), dtype=np.int64)
    for j,c in enumerate(coords):
        E[j,c]=1
    return E%p


def gauge_summary(U: np.ndarray, V: np.ndarray, p: int) -> Dict:
    cols=gauge_uv_columns(U,V,p)
    sr=s19.rank_mod(cols['scale'],p)
    hr=s19.rank_mod(cols['stab'],p)
    cr=s19.rank_mod(cols['combined'],p)
    piv=coordinate_pivots_for_column_space(cols['combined'],p) if cr>0 else []
    spiv=coordinate_pivots_for_column_space(cols['scale'],p) if sr>0 else []
    return {
        'r': int(U.shape[0]),
        'uv_variable_dim': int(18*U.shape[0]),
        'u_span': int(s19.rank_mod(U.T,p)),
        'v_span': int(s19.rank_mod(V.T,p)),
        'uv_pairing_rank': int(s19.rank_mod(s19.pairing_matrix(U,V,p),p)),
        'term_scaling_rank': int(sr),
        'stabilizer_uv_rank': int(hr),
        'combined_gauge_rank': int(cr),
        'stabilizer_scaling_intersection_dim': int(sr+hr-cr),
        'combined_coordinate_pivot_count': int(len(piv)),
        'combined_coordinate_pivots_first20': piv[:20],
        'scaling_coordinate_pivot_count': int(len(spiv)),
        'scaling_coordinate_pivots_first20': spiv[:20],
    }


def choose_chart_and_short_jac(U: np.ndarray, V: np.ndarray, T: np.ndarray, p: int, rng: np.random.Generator) -> Tuple[np.ndarray, np.ndarray, List[int], int, int]:
    P=s19.pairing_matrix(U,V,p)
    Tuv=s19.tensor_uv_matrix(T)%p
    rows=s19.choose_rows_with_T_rank(P,Tuv,p,target_rows=U.shape[0],require_T_rank=9,rng=rng)
    if rows is None:
        raise RuntimeError('could not choose full W-span row minor')
    W=s19.solve_W_from_chart(U,V,rows,T,p)
    SJac, full_rank, short_rank, wblock_rank=s19.shortened_jacobian(U,V,W,rows,p)
    return W, SJac, rows, full_rank, short_rank


def random_full_span_rank22_chart_trial(p: int, rng: np.random.Generator, trial: int) -> Dict:
    while True:
        U=rng.integers(0,p,size=(22,9),dtype=np.int64)
        V=rng.integers(0,p,size=(22,9),dtype=np.int64)
        W=rng.integers(0,p,size=(22,9),dtype=np.int64)
        if s19.rank_mod(U.T,p)==9 and s19.rank_mod(V.T,p)==9 and s19.rank_mod(W.T,p)==9 and s19.rank_mod(s19.pairing_matrix(U,V,p),p)==22:
            break
    T=s19.tensor_from_factors(U,V,W,p)
    Wsol,SJ,rows,full_rank,short_rank=choose_chart_and_short_jac(U,V,T,p,rng)
    gsum=gauge_summary(U,V,p)
    cols=gauge_uv_columns(U,V,p)
    scale_piv=coordinate_pivots_for_column_space(cols['scale'],p)
    comb_piv=coordinate_pivots_for_column_space(cols['combined'],p)
    nvars=18*22
    aug_scale=s19.rank_mod(np.vstack([SJ, coord_row_matrix(nvars,scale_piv,p)]),p)
    aug_comb=s19.rank_mod(np.vstack([SJ, coord_row_matrix(nvars,comb_piv,p)]),p)
    return {
        'trial': int(trial),
        'chart_row_T_rank': int(s19.rank_mod(s19.tensor_uv_matrix(T)[rows,:],p)),
        'shortened_jacobian_rank': int(short_rank),
        'full_brent_jacobian_rank': int(full_rank),
        'scaling_gauge_augmented_rank': int(aug_scale),
        'combined_gauge_augmented_rank': int(aug_comb),
        'gauge_summary': gsum,
    }


def cn122_rank23_chart(p: int, rng: np.random.Generator, scheme_path: Path) -> Dict:
    U,V,W=s19.load_qmm(scheme_path)
    T=s19.make_T333()%p
    Wsol,SJ,rows,full_rank,short_rank=choose_chart_and_short_jac(U%p,V%p,T,p,rng)
    resid=s19.brent_residual(U%p,V%p,Wsol,T,p)
    gsum=gauge_summary(U%p,V%p,p)
    cols=gauge_uv_columns(U%p,V%p,p)
    comb_piv=coordinate_pivots_for_column_space(cols['combined'],p)
    nvars=18*U.shape[0]
    aug_comb=s19.rank_mod(np.vstack([SJ, coord_row_matrix(nvars,comb_piv,p)]),p)
    return {
        'rank': int(U.shape[0]),
        'residual_nnz_after_W_elimination': int(np.count_nonzero(resid%p)),
        'shortened_jacobian_rank': int(short_rank),
        'full_brent_jacobian_rank': int(full_rank),
        'combined_gauge_augmented_rank': int(aug_comb),
        'post_gauge_kernel_dim': int(nvars-aug_comb),
        'expected_cn122_extra_kernel_after_scaling_stabilizer': 24,
        'gauge_summary': gsum,
    }


def semisimple_generic_coordinate_bound() -> Dict:
    T=s19.make_T333()
    support=[]
    for a in range(9):
        for b in range(9):
            for c in range(9):
                if T[a,b,c] != 0:
                    support.append((a,b,c))
    return {
        'assumption': 'A noncentral semisimple stabilizer element has three difference operators with nine distinct eigenspaces in each factor, so every termwise-aligned summand is a single coordinate tensor in the corresponding eigenbasis.',
        'T333_nonzero_coordinate_count_in_eigenbasis': len(support),
        'first10_support_coordinates': support[:10],
        'rank22_consequence_under_assumption': 'impossible: one coordinate tensor summand covers only one nonzero support coordinate, while T333 has 27 nonzero coordinates.',
        'remaining_semisimple_exception': 'repeated difference eigenvalues give larger eigenspaces; these form separate equality-pattern charts rather than the transverse gauge chart.',
    }


def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('--prime',type=int,default=65521)
    ap.add_argument('--trials',type=int,default=3)
    ap.add_argument('--out',default='data/gauge_quotient/gauge_quotient_pilot.json')
    args=ap.parse_args()
    p=args.prime
    rng=np.random.default_rng(2026090521)
    t0=time.time()
    out=Path(args.out); out.parent.mkdir(parents=True,exist_ok=True)
    ws=Path('research/research_record/workspace')

    records=[]
    for trial in range(args.trials):
        rec=random_full_span_rank22_chart_trial(p,rng,trial)
        records.append(rec)
        print(f"random rank22 trial {trial}: short={rec['shortened_jacobian_rank']} scale+J={rec['scaling_gauge_augmented_rank']} combined+J={rec['combined_gauge_augmented_rank']} gauge_rank={rec['gauge_summary']['combined_gauge_rank']} intersection={rec['gauge_summary']['stabilizer_scaling_intersection_dim']}")

    cnrec=cn122_rank23_chart(p,rng,ws/'data/cn122_r23_reproduce/scheme.qmm')
    print(f"cn122 r23: short={cnrec['shortened_jacobian_rank']} combined+J={cnrec['combined_gauge_augmented_rank']} post_gauge_kernel={cnrec['post_gauge_kernel_dim']} intersection={cnrec['gauge_summary']['stabilizer_scaling_intersection_dim']}")

    U27,V27,W27=natural_27()
    nat_uv=gauge_summary(U27%p,V27%p,p)
    nat_full=s19.stabilizer_and_scaling_uv(U27%p,V27%p,W27%p,p)
    print(f"natural 27: uv combined={nat_uv['combined_gauge_rank']} intersection={nat_uv['stabilizer_scaling_intersection_dim']} (exceptional aligned control)")

    result={
        'purpose':'Pilot linear algebra for symmetry-quotient gauge charts of the full-span shortened rank-22 incidence.',
        'prime': int(p),
        'transverse_rank22_prediction': {
            'shortened_variable_dim': 396,
            'term_scaling_dim': 44,
            'effective_noncentral_stabilizer_dim_after_scaling_overlap': 24,
            'combined_gauge_dim': 68,
            'quotient_variable_dim': 328,
            'expected_shortened_jacobian_rank_at_smooth_T333_solution_before_gauge': 328,
            'expected_augmented_rank_after_68_coordinate_gauge': 396,
            'use': 'Over an odd prime, solve a square subsystem of 328 residual equations plus 68 gauge equations, then verify all 531 shortened residual equations and open conditions.'
        },
        'random_full_span_rank22_controls': records,
        'random_controls_summary': {
            'combined_gauge_ranks': sorted(set(r['gauge_summary']['combined_gauge_rank'] for r in records)),
            'intersections': sorted(set(r['gauge_summary']['stabilizer_scaling_intersection_dim'] for r in records)),
            'shortened_ranks': sorted(set(r['shortened_jacobian_rank'] for r in records)),
            'scaling_augmented_ranks': sorted(set(r['scaling_gauge_augmented_rank'] for r in records)),
            'combined_augmented_ranks': sorted(set(r['combined_gauge_augmented_rank'] for r in records)),
        },
        'cn122_rank23_control': cnrec,
        'natural_27_exceptional_aligned_control': {
            'uv_gauge_summary': nat_uv,
            'full_style_summary': nat_full,
            'interpretation': 'The natural decomposition has stabilizer-scaling intersection 8, not 2, so it lies in the termwise-aligned/nontransverse family; it is a control showing why such strata must be separated.'
        },
        'generic_semisimple_termwise_aligned_bound': semisimple_generic_coordinate_bound(),
        'separate_strata': [
            'lower UV-pairing rank: rank(P(U,V)) < 22, where W-elimination chart is invalid or incomplete',
            'gauge-nontransverse full-span charts: stabilizer-scaling intersection > 2; by Jordan analysis nonsemisimple projective actions are incompatible with full spans, while semisimple repeated-difference patterns require separate support/eigenspace charts',
            'transverse full-span full-UV-rank charts: combined UV gauge rank 68 and coordinate slice exists'
        ],
        'elapsed_sec': time.time()-t0,
    }
    out.write_text(json.dumps(result,indent=2,sort_keys=True,default=int)+'\n')
    print(f'wrote {out}')


if __name__=='__main__':
    main()
