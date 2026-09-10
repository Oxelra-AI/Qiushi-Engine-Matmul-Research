#!/usr/bin/env python3
r"""analysis v2: actual shortened rank-22 charts and the singular-stratum consequence.

This repairs the geometry of analysis and of the first analysis attempt.

We work with the 22-term chart obtained from a full-column-rank UV pairing
matrix P(U,V).  Choose 22 UV rows R so that M=P_R is invertible.  Then solve
W=M^{-1}T_R and impose the remaining rows

    F_R(U,V) = T_{\bar R} - P_{\bar R} M^{-1} T_R = 0.

For T=T_{333}, a genuine rank-22 solution must have all three factor spans
9-dimensional, because each tensor flattening has rank 9.  In such a full-span
solution, the infinitesimal stabilizer of T333 in GL_3^3 has dimension 26 in
parameter space, the term scaling kernel has dimension 2r=44, and their
intersection is 2-dimensional (the scalar redundancies in GL_3^3).  Therefore
the full Brent Jacobian kernel has dimension at least 68 and rank at most
594-68=526.  In a full-UV-rank shortened chart the eliminated W block has rank
198, so the shortened Jacobian rank is at most 328.  Generic rank-22 tensors
instead have full Jacobian rank 550 and shortened rank 352.  Thus any full-span
rank-22 preimage of T333 would lie in a codimension-at-least-24 singular stratum
of the rank-22 parameterization.

The script computes:
  * generic rank-22 tensor controls: full rank 550, shortened rank 352;
  * T333 random full-W charts: chooses R with rank(T_R)=9 and measures F/J;
  * cn122 and serendipitous one-term deletion charts using rank(T_R)=9 rows,
    testing whether the shortened residual is in the shortened Jacobian image;
  * the corrected symmetry/scaling dimensions, independent of any false tangent
    cone interpretation at a full-column-rank pairing point.
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import List, Tuple, Optional

import numpy as np

RANK = 22
N = 9
P_DEFAULT = 65521


def make_T333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T


def tensor_from_factors(U: np.ndarray, V: np.ndarray, W: np.ndarray, p: int) -> np.ndarray:
    T = np.zeros((9,9,9), dtype=np.int64)
    for i in range(U.shape[0]):
        T = (T + np.einsum('a,b,c->abc', U[i] % p, V[i] % p, W[i] % p)) % p
    return T % p


def load_qmm(path: Path) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    Us, Vs, Ws = [], [], []
    for raw in path.read_text().splitlines():
        s = raw.strip()
        if not s or s.startswith('#'):
            continue
        parts = s.split()
        if parts[0] == 'u':
            Us.append([int(x) for x in parts[1:]])
        elif parts[0] == 'v':
            Vs.append([int(x) for x in parts[1:]])
        elif parts[0] == 'w':
            Ws.append([int(x) for x in parts[1:]])
    return np.array(Us, dtype=np.int64), np.array(Vs, dtype=np.int64), np.array(Ws, dtype=np.int64)


def rank_mod(A: np.ndarray, p: int) -> int:
    A = np.array(A % p, dtype=np.int64, copy=True)
    m, n = A.shape
    row = 0
    for col in range(n):
        if row >= m:
            break
        nz = np.nonzero(A[row:, col])[0]
        if len(nz) == 0:
            continue
        piv = row + int(nz[0])
        if piv != row:
            A[[row, piv]] = A[[piv, row]]
        inv = pow(int(A[row, col]), p-2, p)
        A[row] = (A[row] * inv) % p
        factors = A[:, col].copy(); factors[row] = 0
        rows = np.nonzero(factors)[0]
        if len(rows):
            A[rows] = (A[rows] - factors[rows, None] * A[row]) % p
        row += 1
    return row


def solve_mod(A: np.ndarray, B: np.ndarray, p: int) -> np.ndarray:
    A = np.array(A % p, dtype=np.int64, copy=True)
    B = np.array(B % p, dtype=np.int64, copy=True)
    n = A.shape[0]
    Aug = np.concatenate([A, B], axis=1) % p
    row = 0
    for col in range(n):
        nz = np.nonzero(Aug[row:, col])[0]
        if len(nz) == 0:
            raise ValueError('singular')
        piv = row + int(nz[0])
        if piv != row:
            Aug[[row, piv]] = Aug[[piv, row]]
        inv = pow(int(Aug[row, col]), p-2, p)
        Aug[row] = (Aug[row] * inv) % p
        factors = Aug[:, col].copy(); factors[row] = 0
        rows = np.nonzero(factors)[0]
        if len(rows):
            Aug[rows] = (Aug[rows] - factors[rows, None] * Aug[row]) % p
        row += 1
    return Aug[:, n:] % p


def pivot_columns_rref(A: np.ndarray, p: int) -> List[int]:
    A = np.array(A % p, dtype=np.int64, copy=True)
    m, n = A.shape
    row = 0; pivots = []
    for col in range(n):
        if row >= m:
            break
        nz = np.nonzero(A[row:, col])[0]
        if len(nz) == 0:
            continue
        piv = row + int(nz[0])
        if piv != row:
            A[[row, piv]] = A[[piv, row]]
        inv = pow(int(A[row, col]), p-2, p)
        A[row] = (A[row] * inv) % p
        factors = A[:, col].copy(); factors[row] = 0
        rows = np.nonzero(factors)[0]
        if len(rows):
            A[rows] = (A[rows] - factors[rows, None] * A[row]) % p
        pivots.append(col)
        row += 1
    return pivots


def pairing_matrix(U: np.ndarray, V: np.ndarray, p: int) -> np.ndarray:
    return np.array([np.outer(U[i] % p, V[i] % p).reshape(81) for i in range(U.shape[0])], dtype=np.int64).T % p


def brent_jacobian(U: np.ndarray, V: np.ndarray, W: np.ndarray, p: int) -> np.ndarray:
    r = U.shape[0]
    J = np.zeros((729, 27*r), dtype=np.int64)
    abc = np.arange(729, dtype=np.int64)
    a_idx = abc // 81
    b_idx = (abc % 81) // 9
    c_idx = abc % 9
    for i in range(r):
        base = 27*i
        u = U[i] % p; v = V[i] % p; w = W[i] % p
        vw = (v[b_idx] * w[c_idx]) % p
        uw = (u[a_idx] * w[c_idx]) % p
        uv = (u[a_idx] * v[b_idx]) % p
        for a in range(9):
            mask = (a_idx == a)
            J[mask, base+a] = (p - vw[mask]) % p
        for b in range(9):
            mask = (b_idx == b)
            J[mask, base+9+b] = (p - uw[mask]) % p
        for c in range(9):
            mask = (c_idx == c)
            J[mask, base+18+c] = (p - uv[mask]) % p
    return J % p


def brent_residual(U: np.ndarray, V: np.ndarray, W: np.ndarray, T: np.ndarray, p: int) -> np.ndarray:
    return (T.reshape(729) % p - tensor_from_factors(U,V,W,p).reshape(729)) % p


def tensor_uv_matrix(T: np.ndarray) -> np.ndarray:
    return T.reshape(81, 9)


def choose_rows_with_T_rank(Pmat: np.ndarray, Tuv: np.ndarray, p: int, target_rows: int = 22, require_T_rank: int = 9, rng: Optional[np.random.Generator] = None, attempts: int = 2000) -> Optional[List[int]]:
    """Choose target_rows rows with rank(P_R)=target_rows and rank(T_R)>=require_T_rank.

    The T-rank condition is essential for T333 full-W charts: rank(W)=rank(T_R).
    """
    if rng is None:
        rng = np.random.default_rng(1)
    all_rows = list(range(Pmat.shape[0]))
    nonzero_rows = [i for i in all_rows if np.any(Tuv[i] % p)]
    by_c = {c: [i for i in nonzero_rows if Tuv[i, c] % p != 0] for c in range(9)}

    def try_order(seed_rows: List[int], fill_order: List[int]) -> Optional[List[int]]:
        sel: List[int] = []
        for i in seed_rows + fill_order:
            if i in sel:
                continue
            if rank_mod(Pmat[sel + [i], :], p) > rank_mod(Pmat[sel, :], p):
                sel.append(i)
                if len(sel) == target_rows:
                    break
        if len(sel) == target_rows and rank_mod(Pmat[sel, :], p) == target_rows and rank_mod(Tuv[sel, :], p) >= require_T_rank:
            return sel
        return None

    # Deterministic first: one row per C-coordinate, then all rows.
    seed = []
    for c in range(9):
        for i in by_c[c]:
            if rank_mod(Tuv[seed + [i], :], p) > rank_mod(Tuv[seed, :], p):
                seed.append(i); break
    ans = try_order(seed, all_rows)
    if ans is not None:
        return ans

    # Randomized attempts mix the seed and fill order.
    for _ in range(attempts):
        seed = []
        cs = list(range(9)); rng.shuffle(cs)
        for c in cs:
            cand = by_c[c].copy(); rng.shuffle(cand)
            for i in cand:
                if rank_mod(Tuv[seed + [i], :], p) > rank_mod(Tuv[seed, :], p):
                    seed.append(i); break
        fill = all_rows.copy(); rng.shuffle(fill)
        ans = try_order(seed, fill)
        if ans is not None:
            return ans
    return None


def tensor_rows_from_uv_rows(uv_rows: List[int]) -> List[int]:
    return [uv*9+c for uv in uv_rows for c in range(9)]


def solve_W_from_chart(U: np.ndarray, V: np.ndarray, uv_rows: List[int], T: np.ndarray, p: int) -> np.ndarray:
    Pmat = pairing_matrix(U,V,p)
    M = Pmat[uv_rows, :] % p
    if rank_mod(M,p) != U.shape[0]:
        raise ValueError('bad row minor')
    Tuv = tensor_uv_matrix(T) % p
    return solve_mod(M, Tuv[uv_rows, :], p)


def shortened_jacobian(U: np.ndarray, V: np.ndarray, W: np.ndarray, uv_rows: List[int], p: int) -> Tuple[np.ndarray, int, int, int]:
    r = U.shape[0]
    J = brent_jacobian(U,V,W,p)
    Rrows = tensor_rows_from_uv_rows(uv_rows)
    Rset = set(Rrows)
    Crows = [i for i in range(729) if i not in Rset]
    uv_cols = [] ; w_cols = []
    for i in range(r):
        uv_cols.extend(range(27*i, 27*i+18))
        w_cols.extend(range(27*i+18, 27*i+27))
    B = J[np.ix_(Rrows, w_cols)] % p
    A = J[np.ix_(Rrows, uv_cols)] % p
    Brank = rank_mod(B,p)
    if Brank != 9*r:
        raise ValueError(f'W block rank {Brank}, expected {9*r}')
    X = solve_mod(B, A, p)
    S = (J[np.ix_(Crows, uv_cols)] - (J[np.ix_(Crows, w_cols)] @ X) % p) % p
    return S, rank_mod(J,p), rank_mod(S,p), Brank


def mat_vec(M: np.ndarray) -> np.ndarray:
    return np.asarray(M, dtype=np.int64).reshape(9)


def stabilizer_and_scaling_uv(U: np.ndarray, V: np.ndarray, W: np.ndarray, p: int) -> dict:
    r = U.shape[0]
    stab_full=[]; stab_uv=[]
    for gen in ['p','q','r']:
        for jj in range(3):
            for kk in range(3):
                E = np.zeros((3,3), dtype=np.int64); E[jj,kk]=1
                full=np.zeros(27*r,dtype=np.int64); uv=np.zeros(18*r,dtype=np.int64)
                for i in range(r):
                    Ui=(U[i]%p).reshape(3,3); Vi=(V[i]%p).reshape(3,3); Wi=(W[i]%p).reshape(3,3)
                    dU=np.zeros((3,3),dtype=np.int64); dV=np.zeros((3,3),dtype=np.int64); dW=np.zeros((3,3),dtype=np.int64)
                    if gen=='p':
                        dU=(E.T@Ui)%p; dW=(p-(E@Wi)%p)%p
                    elif gen=='q':
                        dU=(p-(Ui@E.T)%p)%p; dV=(E.T@Vi)%p
                    else:
                        dV=(p-(Vi@E.T)%p)%p; dW=(Wi@E)%p
                    full[27*i:27*i+9]=mat_vec(dU); full[27*i+9:27*i+18]=mat_vec(dV); full[27*i+18:27*i+27]=mat_vec(dW)
                    uv[18*i:18*i+9]=mat_vec(dU); uv[18*i+9:18*i+18]=mat_vec(dV)
                stab_full.append(full%p); stab_uv.append(uv%p)
    scale_full=[]; scale_uv=[]
    for i in range(r):
        u=U[i]%p; v=V[i]%p; w=W[i]%p
        full=np.zeros(27*r,dtype=np.int64); uv=np.zeros(18*r,dtype=np.int64)
        full[27*i:27*i+9]=u; full[27*i+18:27*i+27]=(p-w)%p; uv[18*i:18*i+9]=u
        scale_full.append(full); scale_uv.append(uv)
        full=np.zeros(27*r,dtype=np.int64); uv=np.zeros(18*r,dtype=np.int64)
        full[27*i+9:27*i+18]=v; full[27*i+18:27*i+27]=(p-w)%p; uv[18*i+9:18*i+18]=v
        scale_full.append(full); scale_uv.append(uv)
    SF=np.array(stab_full,dtype=np.int64).T%p; SU=np.array(stab_uv,dtype=np.int64).T%p
    RF=np.array(scale_full,dtype=np.int64).T%p; RU=np.array(scale_uv,dtype=np.int64).T%p
    return {
        'u_span': rank_mod(U.T,p), 'v_span': rank_mod(V.T,p), 'w_span': rank_mod(W.T,p),
        'stabilizer_full_rank': rank_mod(SF,p), 'stabilizer_uv_rank': rank_mod(SU,p),
        'scaling_full_rank': rank_mod(RF,p), 'scaling_uv_rank': rank_mod(RU,p),
        'combined_full_rank': rank_mod(np.concatenate([SF,RF],axis=1),p),
        'combined_uv_rank': rank_mod(np.concatenate([SU,RU],axis=1),p),
        'intersection_full_dim': rank_mod(SF,p)+rank_mod(RF,p)-rank_mod(np.concatenate([SF,RF],axis=1),p),
        'intersection_uv_dim': rank_mod(SU,p)+rank_mod(RU,p)-rank_mod(np.concatenate([SU,RU],axis=1),p),
    }


def chart_probe(U: np.ndarray, V: np.ndarray, T: np.ndarray, p: int, rng: np.random.Generator, require_T_rank9: bool = True) -> dict:
    Pmat = pairing_matrix(U,V,p)
    prank = rank_mod(Pmat,p)
    Tuv = tensor_uv_matrix(T) % p
    if prank != U.shape[0]:
        return {'usable': False, 'pairing_rank': prank, 'reason': 'pairing rank not full'}
    rows = choose_rows_with_T_rank(Pmat, Tuv, p, target_rows=U.shape[0], require_T_rank=(9 if require_T_rank9 else 0), rng=rng)
    if rows is None:
        return {'usable': False, 'pairing_rank': prank, 'reason': 'no row minor with requested T_R rank'}
    W = solve_W_from_chart(U,V,rows,T,p)
    residual = brent_residual(U,V,W,T,p)
    Rrows = tensor_rows_from_uv_rows(rows)
    Crows = [i for i in range(729) if i not in set(Rrows)]
    SJac, full_rank, short_rank, wblock_rank = shortened_jacobian(U,V,W,rows,p)
    complement = residual[Crows] % p
    aug_rank = rank_mod(np.concatenate([SJac, ((p-complement)%p).reshape(-1,1)],axis=1),p)
    sym = stabilizer_and_scaling_uv(U,V,W,p)
    return {
        'usable': True,
        'pairing_rank': prank,
        'row_minor_T_rank': rank_mod(Tuv[rows,:],p),
        'row_minor_first_12_uv': rows[:12],
        'row_minor_count_nonzero_T_rows': int(sum(1 for rr in rows if np.any(Tuv[rr]%p))),
        'selected_residual_nnz': int(np.count_nonzero(residual[Rrows]%p)),
        'shortened_residual_nnz': int(np.count_nonzero(complement)),
        'shortened_residual_zero': bool(np.count_nonzero(complement)==0),
        'full_brent_jacobian_rank': full_rank,
        'shortened_jacobian_rank': short_rank,
        'wblock_rank': wblock_rank,
        'shortened_augmented_rank_with_residual': aug_rank,
        'shortened_residual_in_jacobian_image': bool(aug_rank == short_rank),
        'symmetry_scaling_variable_space_dims': sym,
    }


def summarize(records: List[dict]) -> dict:
    usable=[r for r in records if r.get('usable')]
    def mm(key):
        vals=[r[key] for r in usable if key in r]
        return [int(min(vals)), int(max(vals))] if vals else None
    return {
        'total': len(records), 'usable': len(usable),
        'shortened_rank_minmax': mm('shortened_jacobian_rank'),
        'full_rank_minmax': mm('full_brent_jacobian_rank'),
        'residual_nnz_minmax': mm('shortened_residual_nnz'),
        'residual_zero_count': int(sum(1 for r in usable if r.get('shortened_residual_zero'))),
        'residual_in_short_image_count': int(sum(1 for r in usable if r.get('shortened_residual_in_jacobian_image'))),
        'row_minor_T_rank_values': sorted(set(int(r.get('row_minor_T_rank')) for r in usable)),
    }


def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('--prime',type=int,default=P_DEFAULT)
    ap.add_argument('--trials',type=int,default=5)
    ap.add_argument('--out',default='data/singular_stratum/singular_stratum_v2.json')
    args=ap.parse_args()
    p=args.prime; rng=np.random.default_rng(2026090519)
    out=Path(args.out); out.parent.mkdir(parents=True,exist_ok=True)
    ws=Path('research/research_record/workspace')
    T333=make_T333()%p
    cnU,cnV,cnW=load_qmm(ws/'data/cn122_r23_reproduce/scheme.qmm')
    seU,seV,seW=load_qmm(ws/'data/fmm_r23_schemes/serendipitous_8d34.qmm')
    t0=time.time()

    result={
        'purpose':'Actual shortened rank-22 charts with T_R rank 9, plus the exact symmetry/scaling singular-stratum consequence.',
        'prime':p,
        'singular_stratum_consequence':{
            'r':22,
            'generic_full_rank22_jacobian_rank':550,
            'generic_shortened_rank22_chart_rank':352,
            'term_scaling_kernel_dim_2r':44,
            'mm_tensor_stabilizer_parameter_rank_full_span':26,
            'intersection_dim_scaling_with_stabilizer':2,
            'forced_kernel_dim_at_T333_full_span_rank22_solution':68,
            'forced_full_jacobian_rank_max':526,
            'forced_shortened_jacobian_rank_max':328,
            'rank_drop_from_generic_full':24,
            'rank_drop_from_generic_shortened':24,
            'interpretation':'If T333 has a full-span rank-22 decomposition in a full-UV-rank chart, the point is not generic on sigma_22; it lies in the rank<=526 full-Jacobian / rank<=328 shortened-Jacobian stratum. This follows from f=T333 and stabilizer/scaling tangents, not from the invalid N dP tangent-cone count.'
        },
        'scheme_checks':{
            'cn122_residual_nnz':int(np.count_nonzero(brent_residual(cnU,cnV,cnW,T333,p))),
            'serendipitous_residual_nnz':int(np.count_nonzero(brent_residual(seU,seV,seW,T333,p))),
            'cn122_rank23_symmetry_scaling_dims':stabilizer_and_scaling_uv(cnU%p,cnV%p,cnW%p,p),
        },
        'generic_rank22_tensor_chart_controls':[],
        't333_random_fullW_chart_samples':[],
        'cn122_deletion_fullW_charts':[],
        'serendipitous_deletion_fullW_charts':[],
    }

    # Positive controls: when T is the random rank-22 tensor itself, the shortened chart has rank 352.
    for trial in range(args.trials):
        while True:
            U=rng.integers(0,p,size=(22,9),dtype=np.int64)
            V=rng.integers(0,p,size=(22,9),dtype=np.int64)
            W=rng.integers(0,p,size=(22,9),dtype=np.int64)
            if rank_mod(U.T,p)==9 and rank_mod(V.T,p)==9 and rank_mod(W.T,p)==9 and rank_mod(pairing_matrix(U,V,p),p)==22:
                break
        T=tensor_from_factors(U,V,W,p)
        rec=chart_probe(U,V,T,p,rng,require_T_rank9=True)
        rec['trial']=trial
        result['generic_rank22_tensor_chart_controls'].append(rec)
        print(f"generic rank22 tensor trial {trial}: full={rec.get('full_brent_jacobian_rank')} short={rec.get('shortened_jacobian_rank')} resid={rec.get('shortened_residual_nnz')} T_R_rank={rec.get('row_minor_T_rank')}")

    # Random U,V with W solved against the fixed T333 in charts capable of full W span.
    for trial in range(args.trials):
        while True:
            U=rng.integers(0,p,size=(22,9),dtype=np.int64)
            V=rng.integers(0,p,size=(22,9),dtype=np.int64)
            if rank_mod(U.T,p)==9 and rank_mod(V.T,p)==9 and rank_mod(pairing_matrix(U,V,p),p)==22:
                break
        rec=chart_probe(U,V,T333,p,rng,require_T_rank9=True)
        rec['trial']=trial
        result['t333_random_fullW_chart_samples'].append(rec)
        print(f"T333 random chart {trial}: full={rec.get('full_brent_jacobian_rank')} short={rec.get('shortened_jacobian_rank')} resid={rec.get('shortened_residual_nnz')} Wspan={rec.get('symmetry_scaling_variable_space_dims',{}).get('w_span')}")

    for name,U23,V23 in [('cn122',cnU,cnV),('serendipitous',seU,seV)]:
        dest=[]
        for drop in range(23):
            keep=[i for i in range(23) if i!=drop]
            rec=chart_probe(U23[keep]%p,V23[keep]%p,T333,p,rng,require_T_rank9=True)
            rec['drop_term']=drop
            dest.append(rec)
            print(f"{name} drop {drop:2d}: usable={rec.get('usable')} full={rec.get('full_brent_jacobian_rank')} short={rec.get('shortened_jacobian_rank')} resid={rec.get('shortened_residual_nnz')} in_image={rec.get('shortened_residual_in_jacobian_image')} Wspan={rec.get('symmetry_scaling_variable_space_dims',{}).get('w_span')}")
        if name=='cn122': result['cn122_deletion_fullW_charts']=dest
        else: result['serendipitous_deletion_fullW_charts']=dest

    for key in ['generic_rank22_tensor_chart_controls','t333_random_fullW_chart_samples','cn122_deletion_fullW_charts','serendipitous_deletion_fullW_charts']:
        result[key+'_summary']=summarize(result[key])
    result['elapsed_sec']=time.time()-t0
    out.write_text(json.dumps(result,indent=2,sort_keys=True,default=int)+'\n')
    print(f"wrote {out}")


if __name__=='__main__':
    main()
