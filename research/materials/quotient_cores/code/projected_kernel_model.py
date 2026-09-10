#!/usr/bin/env python3
r"""Projected Segre--MinRank kernel model for rank-22 matrix multiplication.

Let E=K^9\otimes K^9 and let L be the 9-dimensional image of T333 as an
81 x 9 UV/W flattening matrix.  For a full-UV-rank r-term decomposition with
X=[u_i\otimes v_i] (81 x r), existence of W with T333=XW is equivalent to
L subset span(X).  If rank(X)=r, then this is equivalent to

    rank(pi X) = r-9

where pi:E -> E/L.  For r=22 this becomes rank(pi X)=13.

On a column chart where 13 selected term columns of pi X are independent,
write the remaining 9 columns as linear combinations:

    (pi X)_J = (pi X)_I C,  C in K^{13 x 9}.

For T333 we use a sparse quotient pi: 54 zero-support UV rows plus 18
differences among the three support rows in each W-slice.  Thus pi has 72 rows
and row weight <=2.  The chart equations are 72*9=648 sparse cubic equations
in U,V,C (quadratic in U,V and linear in C).  This complements the 531 Schur
shortened equations: fewer variables in the Schur form, lower degree and sparse
structure in this projected kernel form.
"""
from __future__ import annotations
import argparse, itertools, json, sys, time
from pathlib import Path
from typing import List, Tuple, Optional
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
import rank22_singular_stratum_v2 as s19  # noqa: E402


def nullspace_mod(A: np.ndarray, p: int) -> np.ndarray:
    A=np.array(A%p,dtype=np.int64,copy=True)
    m,n=A.shape; row=0; piv=[]
    for col in range(n):
        if row>=m: break
        nz=np.nonzero(A[row:,col])[0]
        if len(nz)==0: continue
        pr=row+int(nz[0])
        if pr!=row: A[[row,pr]]=A[[pr,row]]
        inv=pow(int(A[row,col]),p-2,p)
        A[row]=(A[row]*inv)%p
        fac=A[:,col].copy(); fac[row]=0
        rows=np.nonzero(fac)[0]
        if len(rows): A[rows]=(A[rows]-fac[rows,None]*A[row])%p
        piv.append(col); row+=1
    pivset=set(piv); free=[j for j in range(n) if j not in pivset]
    basis=[]
    for f in free:
        x=np.zeros(n,dtype=np.int64); x[f]=1
        for i,col in reversed(list(enumerate(piv))):
            x[col]=(-int(A[i,f]))%p
        basis.append(x)
    return np.array(basis,dtype=np.int64).T%p if basis else np.zeros((n,0),dtype=np.int64)


def t333_support_rows() -> dict:
    by_c={c:[] for c in range(9)}
    support=[]
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a=3*i+j; b=3*j+k; c=3*i+k
                uv=a*9+b
                by_c[c].append(uv)
                support.append((uv,c,a,b))
    for c in by_c:
        by_c[c]=sorted(by_c[c])
    return {'by_c':by_c,'support':support,'support_rows':sorted(set(uv for uv,c,a,b in support))}


def sparse_t333_quotient_matrix(p: int) -> np.ndarray:
    info=t333_support_rows(); support_set=set(info['support_rows'])
    rows=[]
    # 54 rows where Tuv is zero: coordinate functional e_r.
    for uv in range(81):
        if uv not in support_set:
            e=np.zeros(81,dtype=np.int64); e[uv]=1; rows.append(e)
    # For each W-coordinate c, the three support rows have identical image in L;
    # use two differences against the first anchor row.
    for c in range(9):
        anchor=info['by_c'][c][0]
        for uv in info['by_c'][c][1:]:
            e=np.zeros(81,dtype=np.int64); e[uv]=1; e[anchor]=(p-1)%p; rows.append(e)
    Q=np.array(rows,dtype=np.int64)%p
    assert Q.shape==(72,81)
    return Q


def quotient_matrix_for_T(T: np.ndarray, p: int, prefer_sparse_t333: bool=True) -> np.ndarray:
    Tuv=s19.tensor_uv_matrix(T)%p
    if prefer_sparse_t333 and np.array_equal(Tuv, s19.tensor_uv_matrix(s19.make_T333())%p):
        Q=sparse_t333_quotient_matrix(p)
        assert np.count_nonzero((Q @ Tuv)%p)==0
        assert s19.rank_mod(Q,p)==72
        return Q
    N=nullspace_mod(Tuv.T,p).T%p
    assert N.shape[0]==81-s19.rank_mod(Tuv,p)
    return N


def X_from_UV(U: np.ndarray, V: np.ndarray, p: int) -> np.ndarray:
    return s19.pairing_matrix(U%p,V%p,p)


def find_independent_columns(A: np.ndarray, k: int, p: int) -> Optional[List[int]]:
    piv=s19.pivot_columns_rref(A,p)
    if len(piv)<k: return None
    return [int(x) for x in piv[:k]]


def solve_left_rect(A: np.ndarray, B: np.ndarray, p: int) -> Tuple[np.ndarray, List[int], int]:
    """Solve A C = B for A m x k full column rank via k independent rows."""
    k=A.shape[1]
    row_piv=s19.pivot_columns_rref(A.T,p)[:k]
    if len(row_piv)!=k or s19.rank_mod(A[row_piv,:],p)!=k:
        raise RuntimeError('no independent row pivot set')
    C=s19.solve_mod(A[row_piv,:], B[row_piv,:], p)
    resid=(B-(A@C)%p)%p
    return C,[int(x) for x in row_piv],int(np.count_nonzero(resid))


def chart_residual_for_pivots(QX: np.ndarray, pivots: List[int], p: int) -> dict:
    r=QX.shape[1]; rem=[j for j in range(r) if j not in set(pivots)]
    A=QX[:,pivots]%p; B=QX[:,rem]%p
    if s19.rank_mod(A,p)!=len(pivots):
        return {'usable':False,'pivot_rank':int(s19.rank_mod(A,p)),'remaining_count':len(rem)}
    C,row_piv,nnz=solve_left_rect(A,B,p)
    return {
        'usable':True,
        'pivot_terms':[int(x) for x in pivots],
        'remaining_terms':[int(x) for x in rem],
        'pivot_rank':int(s19.rank_mod(A,p)),
        'row_pivots_first20':row_piv[:20],
        'C_shape':[int(C.shape[0]),int(C.shape[1])],
        'residual_nnz':int(nnz),
        'residual_zero':bool(nnz==0),
    }


def analyze_UV_against_T(U: np.ndarray, V: np.ndarray, T: np.ndarray, p: int, pivot_count: int) -> dict:
    Q=quotient_matrix_for_T(T,p)
    X=X_from_UV(U,V,p)
    QX=(Q@X)%p
    qrank=s19.rank_mod(QX,p)
    piv=find_independent_columns(QX,pivot_count,p) if qrank>=pivot_count else None
    rec={
        'r':int(U.shape[0]),
        'X_rank':int(s19.rank_mod(X,p)),
        'quotient_rows':int(Q.shape[0]),
        'quotient_row_rank':int(s19.rank_mod(Q,p)),
        'quotient_row_weight_max':int(max(np.count_nonzero(row) for row in Q)),
        'rank_pi_X':int(qrank),
        'target_rank_pi_X_for_solution':int(U.shape[0]-9),
        'rank_condition_satisfied':bool(qrank<=U.shape[0]-9),
    }
    if piv is not None:
        rec['chart']=chart_residual_for_pivots(QX,piv,p)
    else:
        rec['chart']={'usable':False,'reason':'rank(pi X) below pivot count or no pivots'}
    return rec


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--prime',type=int,default=65521)
    ap.add_argument('--trials',type=int,default=3)
    ap.add_argument('--out',default='data/projected_kernel_model/projected_kernel_model.json')
    args=ap.parse_args()
    p=args.prime; rng=np.random.default_rng(2026090522); t0=time.time()
    ws=Path('research/research_record/workspace')
    T333=s19.make_T333()%p
    result={
        'purpose':'Build and calibrate the projected Segre--MinRank kernel model L subset span{u_i tensor v_i} for rank-22 T333.',
        'prime':p,
        'model_counts_r22':{
            'UV_projective_variables_after_term_scaling':16*22,
            'C_variables_for_rank_piX_13_chart':13*9,
            'raw_sparse_cubic_equations':72*9,
            'effective_PGL3xPGL3xPGL3_gauge_directions':24,
            'quotient_dimension_after_projective_and_stabilizer_gauge':16*22+13*9-24,
            'Schur_shortened_variables_after_full_68_gauge':328,
            'comment':'The 445-variable sparse cubic model and the 328-variable Schur model are complementary charts; both require finite open-chart coverage and final Brent verification.'
        },
        't333_sparse_quotient':{},
        'random_rank22_solution_controls':[],
        'random_UV_against_T333_controls':[],
        'cn122_rank23':{},
        'cn122_deletions_summary':{},
        'serendipitous_deletions_summary':{},
    }
    Q=sparse_t333_quotient_matrix(p)
    result['t333_sparse_quotient']={
        'shape':[72,81],
        'rank':int(s19.rank_mod(Q,p)),
        'annihilates_Tuv':bool(np.count_nonzero((Q@s19.tensor_uv_matrix(T333))%p)==0),
        'row_weight_hist':{str(k):int(sum(1 for row in Q if np.count_nonzero(row)==k)) for k in sorted(set(np.count_nonzero(row) for row in Q))},
        'support_rows_by_w':{str(k):v for k,v in t333_support_rows()['by_c'].items()},
    }

    for trial in range(args.trials):
        while True:
            U=rng.integers(0,p,size=(22,9),dtype=np.int64)
            V=rng.integers(0,p,size=(22,9),dtype=np.int64)
            W=rng.integers(0,p,size=(22,9),dtype=np.int64)
            if s19.rank_mod(U.T,p)==9 and s19.rank_mod(V.T,p)==9 and s19.rank_mod(W.T,p)==9 and s19.rank_mod(X_from_UV(U,V,p),p)==22:
                break
        T=s19.tensor_from_factors(U,V,W,p)
        rec=analyze_UV_against_T(U,V,T,p,pivot_count=13)
        rec['trial']=trial
        result['random_rank22_solution_controls'].append(rec)
        print(f'random rank22 solution {trial}: rank piX={rec["rank_pi_X"]} residual_zero={rec["chart"].get("residual_zero")}')
    for trial in range(args.trials):
        while True:
            U=rng.integers(0,p,size=(22,9),dtype=np.int64)
            V=rng.integers(0,p,size=(22,9),dtype=np.int64)
            if s19.rank_mod(U.T,p)==9 and s19.rank_mod(V.T,p)==9 and s19.rank_mod(X_from_UV(U,V,p),p)==22:
                break
        rec=analyze_UV_against_T(U,V,T333,p,pivot_count=13)
        rec['trial']=trial
        result['random_UV_against_T333_controls'].append(rec)
        print(f'random UV vs T333 {trial}: rank piX={rec["rank_pi_X"]} residual_zero={rec["chart"].get("residual_zero")}')

    cnU,cnV,cnW=s19.load_qmm(ws/'data/cn122_r23_reproduce/scheme.qmm')
    seU,seV,seW=s19.load_qmm(ws/'data/fmm_r23_schemes/serendipitous_8d34.qmm')
    result['cn122_rank23']=analyze_UV_against_T(cnU%p,cnV%p,T333,p,pivot_count=14)
    print(f'cn122 rank23: rank piX={result["cn122_rank23"]["rank_pi_X"]} target={result["cn122_rank23"]["target_rank_pi_X_for_solution"]}')

    for name,U23,V23,key in [('cn122',cnU,cnV,'cn122_deletions_summary'),('serendipitous',seU,seV,'serendipitous_deletions_summary')]:
        recs=[]
        for drop in range(23):
            keep=[i for i in range(23) if i!=drop]
            rec=analyze_UV_against_T(U23[keep]%p,V23[keep]%p,T333,p,pivot_count=13)
            rec['drop_term']=drop
            recs.append({'drop_term':drop,'X_rank':rec['X_rank'],'rank_pi_X':rec['rank_pi_X'],'rank_condition_satisfied':rec['rank_condition_satisfied'],'chart_residual_zero':rec['chart'].get('residual_zero'), 'chart_residual_nnz':rec['chart'].get('residual_nnz')})
        result[key]={
            'records':recs,
            'rank_pi_X_hist':{str(v):sum(1 for r in recs if r['rank_pi_X']==v) for v in sorted(set(r['rank_pi_X'] for r in recs))},
            'rank_condition_satisfied_count':sum(1 for r in recs if r['rank_condition_satisfied']),
            'chart_residual_zero_count':sum(1 for r in recs if r.get('chart_residual_zero')),
        }
        print(f'{name} deletions: rank_pi hist {result[key]["rank_pi_X_hist"]}, condition count {result[key]["rank_condition_satisfied_count"]}')

    result['random_rank22_controls_summary']={
        'rank_pi_X_values':sorted(set(r['rank_pi_X'] for r in result['random_rank22_solution_controls'])),
        'residual_zero_count':sum(1 for r in result['random_rank22_solution_controls'] if r['chart'].get('residual_zero')),
    }
    result['random_UV_T333_summary']={
        'rank_pi_X_values':sorted(set(r['rank_pi_X'] for r in result['random_UV_against_T333_controls'])),
        'residual_zero_count':sum(1 for r in result['random_UV_against_T333_controls'] if r['chart'].get('residual_zero')),
    }
    result['elapsed_sec']=time.time()-t0
    out=Path(args.out); out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2,sort_keys=True,default=int)+'\n')
    print(f'wrote {out}')

if __name__=='__main__':
    main()
