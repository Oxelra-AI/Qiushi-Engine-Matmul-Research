#!/usr/bin/env python3
"""analysis: shortened rank-22 incidence and forced singular stratum.

This script repairs the analysis local geometry interpretation.  It does not use
N dP at a full-column-rank pairing matrix as a tangent cone.  Instead it works
with the actual rank-22 chart obtained by eliminating W from a 22-term UV
configuration P=[u_i \otimes v_i].

For rank r=22 and an invertible 22x22 row minor M of P, solve W from the
198 equations P_R W = T_R and impose only the remaining 531 equations

    F(U,V) = T_{bar R} - P_{bar R} M^{-1} T_R = 0.

At a genuine rank-22 decomposition of T_{333}, all three factor spans are full
because the three tensor flattenings of T_{333} have rank 9.  Therefore the
26-dimensional matrix-multiplication tensor stabilizer and the 2r term-scaling
vectors lie in the fiber tangent.  Their intersection is the two scalar
redundancies, so the full Brent Jacobian kernel has dimension at least
26 + 2r - 2 = 68.  In a full-UV-rank shortened chart, the projected UV kernel
has the same forced dimension, hence the shortened Jacobian rank is at most
18r - 68 = 328.  The generic shortened rank is 352.

Outputs:
  data/singular_stratum/singular_stratum.json
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import List, Tuple

import numpy as np


R = 22
N = 9
P_DEFAULT = 65521


def make_T333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T


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
        A[row, :] = (A[row, :] * inv) % p
        factors = A[:, col].copy()
        factors[row] = 0
        rows = np.nonzero(factors)[0]
        if len(rows):
            A[rows, :] = (A[rows, :] - factors[rows, None] * A[row, :]) % p
        row += 1
    return row


def pivot_columns_rref(A: np.ndarray, p: int) -> List[int]:
    """Pivot columns of A over F_p."""
    A = np.array(A % p, dtype=np.int64, copy=True)
    m, n = A.shape
    row = 0
    pivots = []
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
        A[row, :] = (A[row, :] * inv) % p
        factors = A[:, col].copy()
        factors[row] = 0
        rows = np.nonzero(factors)[0]
        if len(rows):
            A[rows, :] = (A[rows, :] - factors[rows, None] * A[row, :]) % p
        pivots.append(col)
        row += 1
    return pivots


def solve_mod(A: np.ndarray, B: np.ndarray, p: int) -> np.ndarray:
    """Solve A X = B over F_p for square nonsingular A."""
    A = np.array(A % p, dtype=np.int64, copy=True)
    B = np.array(B % p, dtype=np.int64, copy=True)
    n = A.shape[0]
    assert A.shape == (n, n)
    assert B.shape[0] == n
    Aug = np.concatenate([A, B], axis=1) % p
    row = 0
    for col in range(n):
        nz = np.nonzero(Aug[row:, col])[0]
        if len(nz) == 0:
            raise ValueError('singular solve_mod')
        piv = row + int(nz[0])
        if piv != row:
            Aug[[row, piv]] = Aug[[piv, row]]
        inv = pow(int(Aug[row, col]), p-2, p)
        Aug[row, :] = (Aug[row, :] * inv) % p
        factors = Aug[:, col].copy()
        factors[row] = 0
        rows = np.nonzero(factors)[0]
        if len(rows):
            Aug[rows, :] = (Aug[rows, :] - factors[rows, None] * Aug[row, :]) % p
        row += 1
    return Aug[:, n:] % p


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


def pairing_matrix(U: np.ndarray, V: np.ndarray, p: int) -> np.ndarray:
    return np.array([np.outer(U[i] % p, V[i] % p).reshape(81) for i in range(U.shape[0])], dtype=np.int64).T % p


def tensor_rows_from_uv_rows(uv_rows: List[int]) -> List[int]:
    return [uv*9 + c for uv in uv_rows for c in range(9)]


def choose_uv_rows(P: np.ndarray, p: int) -> List[int]:
    # independent rows of P are pivot columns of P^T
    rows = pivot_columns_rref(P.T, p)
    if len(rows) < P.shape[1]:
        raise ValueError('pairing matrix does not have full column rank')
    return rows[:P.shape[1]]


def solve_W_from_chart(U: np.ndarray, V: np.ndarray, uv_rows: List[int], T: np.ndarray, p: int) -> np.ndarray:
    Pmat = pairing_matrix(U, V, p)
    M = Pmat[uv_rows, :] % p  # 22 x 22
    if rank_mod(M, p) != U.shape[0]:
        raise ValueError('chosen minor singular')
    W = np.zeros((U.shape[0], 9), dtype=np.int64)
    Tflat = T.reshape(729) % p
    for c in range(9):
        rhs = np.array([Tflat[uv*9 + c] for uv in uv_rows], dtype=np.int64).reshape(-1, 1) % p
        sol = solve_mod(M, rhs, p).reshape(-1)
        W[:, c] = sol
    return W % p


def brent_residual(U: np.ndarray, V: np.ndarray, W: np.ndarray, T: np.ndarray, p: int) -> np.ndarray:
    S = np.zeros((9,9,9), dtype=np.int64)
    for i in range(U.shape[0]):
        # product entries may be negative if input from QMM; reduce first
        S = (S + np.einsum('a,b,c->abc', U[i] % p, V[i] % p, W[i] % p)) % p
    return (T.reshape(729) % p - S.reshape(729)) % p


def shortened_jacobian(U: np.ndarray, V: np.ndarray, W: np.ndarray, uv_rows: List[int], p: int) -> Tuple[np.ndarray, int, int]:
    r = U.shape[0]
    J = brent_jacobian(U, V, W, p)
    Rrows = tensor_rows_from_uv_rows(uv_rows)
    Rset = set(Rrows)
    Crows = [i for i in range(729) if i not in Rset]
    uv_cols = []
    w_cols = []
    for i in range(r):
        uv_cols.extend(range(27*i, 27*i+18))
        w_cols.extend(range(27*i+18, 27*i+27))
    B = J[np.ix_(Rrows, w_cols)] % p
    if rank_mod(B, p) != 9*r:
        raise ValueError('selected W block is singular')
    A = J[np.ix_(Rrows, uv_cols)] % p
    X = solve_mod(B, A, p)  # B^{-1} A
    Cuv = J[np.ix_(Crows, uv_cols)] % p
    Cw = J[np.ix_(Crows, w_cols)] % p
    SJac = (Cuv - (Cw @ X) % p) % p
    return SJac, rank_mod(J, p), rank_mod(SJac, p)


def matrix_flat_rank(mask: int) -> int:
    # only used for F2 mask support summaries if needed
    rows = [[(mask >> (3*i+j)) & 1 for j in range(3)] for i in range(3)]
    A = np.array(rows, dtype=np.int64)
    return rank_mod(A, 2)


def mat_vec(M: np.ndarray) -> np.ndarray:
    return np.asarray(M, dtype=np.int64).reshape(9)


def stabilizer_uv_cols(U: np.ndarray, V: np.ndarray, W: np.ndarray, p: int, variant: str = 'pullback') -> Tuple[np.ndarray, np.ndarray]:
    """Return full and UV-projected global stabilizer tangent columns.

    This is the corrected covector pullback formula used in earlier steps:
      dU = E^T U, dW = -E W for p-generator;
      dU = -U E^T, dV = E^T V for q-generator;
      dV = -V E^T, dW = W E for r-generator.
    """
    r = U.shape[0]
    full_cols = []
    uv_cols = []
    for gen in ['p', 'q', 'r']:
        for jj in range(3):
            for kk in range(3):
                E = np.zeros((3,3), dtype=np.int64); E[jj,kk] = 1
                full = np.zeros(27*r, dtype=np.int64)
                uv = np.zeros(18*r, dtype=np.int64)
                for i in range(r):
                    Ui = (U[i] % p).reshape(3,3)
                    Vi = (V[i] % p).reshape(3,3)
                    Wi = (W[i] % p).reshape(3,3)
                    dU = np.zeros((3,3), dtype=np.int64)
                    dV = np.zeros((3,3), dtype=np.int64)
                    dW = np.zeros((3,3), dtype=np.int64)
                    if gen == 'p':
                        dU = (E.T @ Ui) % p
                        dW = (p - (E @ Wi) % p) % p
                    elif gen == 'q':
                        dU = (p - (Ui @ E.T) % p) % p
                        dV = (E.T @ Vi) % p
                    else:
                        dV = (p - (Vi @ E.T) % p) % p
                        dW = (Wi @ E) % p
                    full[27*i:27*i+9] = mat_vec(dU) % p
                    full[27*i+9:27*i+18] = mat_vec(dV) % p
                    full[27*i+18:27*i+27] = mat_vec(dW) % p
                    uv[18*i:18*i+9] = mat_vec(dU) % p
                    uv[18*i+9:18*i+18] = mat_vec(dV) % p
                full_cols.append(full % p)
                uv_cols.append(uv % p)
    return np.array(full_cols, dtype=np.int64).T % p, np.array(uv_cols, dtype=np.int64).T % p


def scaling_cols(U: np.ndarray, V: np.ndarray, W: np.ndarray, p: int) -> Tuple[np.ndarray, np.ndarray]:
    r = U.shape[0]
    full_cols = []
    uv_cols = []
    for i in range(r):
        u = U[i] % p; v = V[i] % p; w = W[i] % p
        # scale u and compensate w
        full = np.zeros(27*r, dtype=np.int64); uv = np.zeros(18*r, dtype=np.int64)
        full[27*i:27*i+9] = u
        full[27*i+18:27*i+27] = (p - w) % p
        uv[18*i:18*i+9] = u
        full_cols.append(full); uv_cols.append(uv)
        # scale v and compensate w
        full = np.zeros(27*r, dtype=np.int64); uv = np.zeros(18*r, dtype=np.int64)
        full[27*i+9:27*i+18] = v
        full[27*i+18:27*i+27] = (p - w) % p
        uv[18*i+9:18*i+18] = v
        full_cols.append(full); uv_cols.append(uv)
    return np.array(full_cols, dtype=np.int64).T % p, np.array(uv_cols, dtype=np.int64).T % p


def symmetry_dimension_sample(U: np.ndarray, V: np.ndarray, W: np.ndarray, p: int) -> dict:
    Sfull, Suv = stabilizer_uv_cols(U, V, W, p)
    Rfull, Ruv = scaling_cols(U, V, W, p)
    full_comb = np.concatenate([Rfull, Sfull], axis=1) % p
    uv_comb = np.concatenate([Ruv, Suv], axis=1) % p
    return {
        'u_span': rank_mod(U.T, p),
        'v_span': rank_mod(V.T, p),
        'w_span': rank_mod(W.T, p),
        'scaling_full_rank': rank_mod(Rfull, p),
        'stabilizer_full_rank': rank_mod(Sfull, p),
        'combined_full_rank': rank_mod(full_comb, p),
        'scaling_uv_rank': rank_mod(Ruv, p),
        'stabilizer_uv_rank': rank_mod(Suv, p),
        'combined_uv_rank': rank_mod(uv_comb, p),
        'intersection_full_dim': rank_mod(Rfull, p) + rank_mod(Sfull, p) - rank_mod(full_comb, p),
        'intersection_uv_dim': rank_mod(Ruv, p) + rank_mod(Suv, p) - rank_mod(uv_comb, p),
    }


def chart_probe(U: np.ndarray, V: np.ndarray, T: np.ndarray, p: int) -> dict:
    Pmat = pairing_matrix(U, V, p)
    prank = rank_mod(Pmat, p)
    if prank != U.shape[0]:
        return {'pairing_rank': prank, 'usable': False}
    uv_rows = choose_uv_rows(Pmat, p)
    W = solve_W_from_chart(U, V, uv_rows, T, p)
    residual = brent_residual(U, V, W, T, p)
    Rrows = tensor_rows_from_uv_rows(uv_rows)
    Crows = [i for i in range(729) if i not in set(Rrows)]
    selected_nnz = int(np.count_nonzero(residual[Rrows] % p))
    complement = residual[Crows] % p
    residual_nnz = int(np.count_nonzero(complement))
    residual_rank_aug = None
    SJac, full_rank, short_rank = shortened_jacobian(U, V, W, uv_rows, p)
    aug_rank = rank_mod(np.concatenate([SJac, ((p - complement) % p).reshape(-1,1)], axis=1), p)
    residual_in_short_image = (aug_rank == short_rank)
    sym = symmetry_dimension_sample(U, V, W, p)
    return {
        'usable': True,
        'pairing_rank': prank,
        'uv_rows_head': uv_rows[:10],
        'uv_rows': uv_rows,
        'selected_residual_nnz_should_be_0': selected_nnz,
        'shortened_residual_nnz': residual_nnz,
        'shortened_residual_zero': residual_nnz == 0,
        'full_brent_jacobian_rank_at_chart_point': full_rank,
        'shortened_jacobian_rank': short_rank,
        'shortened_augmented_rank_with_residual': aug_rank,
        'shortened_residual_in_jacobian_image': residual_in_short_image,
        'forced_solution_short_rank_max': 18*U.shape[0] - 68,
        'forced_solution_full_rank_max': 27*U.shape[0] - 68,
        'satisfies_forced_short_singular_rank_bound': short_rank <= 18*U.shape[0] - 68,
        'satisfies_forced_full_singular_rank_bound': full_rank <= 27*U.shape[0] - 68,
        'symmetry_scaling_dimensions_at_chart_point': sym,
    }


def verify_scheme(U: np.ndarray, V: np.ndarray, W: np.ndarray, T: np.ndarray, p: int) -> int:
    return int(np.count_nonzero(brent_residual(U, V, W, T, p)))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--prime', type=int, default=P_DEFAULT)
    ap.add_argument('--random-trials', type=int, default=5)
    ap.add_argument('--out', default='data/singular_stratum/singular_stratum.json')
    args = ap.parse_args()

    p = args.prime
    T = make_T333()
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    ws = Path('research/research_record/workspace')
    cn_path = ws/'data/cn122_r23_reproduce/scheme.qmm'
    se_path = ws/'data/fmm_r23_schemes/serendipitous_8d34.qmm'
    U23, V23, W23 = load_qmm(cn_path)
    Us23, Vs23, Ws23 = load_qmm(se_path)

    t0 = time.time()
    result = {
        'purpose': 'Repair analysis geometry using the actual shortened rank-22 chart and the global symmetry-forced singular stratum.',
        'prime': p,
        'rank22_parameter_counts': {
            'r': 22,
            'full_variables_27r': 594,
            'shortened_uv_variables_18r': 396,
            'w_variables_eliminated_9r': 198,
            'generic_full_jacobian_rank': 550,
            'generic_shortened_jacobian_rank': 352,
            'generic_scaling_kernel_dim': 44,
            'mm_tensor_stabilizer_rank': 26,
            'scaling_stabilizer_intersection_dim_full_span': 2,
            'forced_kernel_dim_at_any_T333_rank22_full_span_solution': 68,
            'forced_full_jacobian_rank_max': 526,
            'forced_shortened_jacobian_rank_max_in_full_uv_rank_chart': 328,
            'flattening_reason_for_full_spans': 'Each mode flattening of T333 has rank 9, so any rank-22 decomposition must span all 9 factor coordinates in U,V,W.'
        },
        'scheme_verification_mod_p': {
            'cn122_residual_nnz': verify_scheme(U23, V23, W23, T, p),
            'serendipitous_8d34_residual_nnz': verify_scheme(Us23, Vs23, Ws23, T, p),
        },
        'random_full_span_symmetry_samples': [],
        'random_shortened_chart_samples': [],
        'cn122_deletion_shortened_chart': [],
        'serendipitous_deletion_shortened_chart': [],
    }

    rng = np.random.default_rng(20260905)
    for trial in range(args.random_trials):
        while True:
            U = rng.integers(0, p, size=(22,9), dtype=np.int64)
            V = rng.integers(0, p, size=(22,9), dtype=np.int64)
            W = rng.integers(0, p, size=(22,9), dtype=np.int64)
            if rank_mod(U.T,p) == 9 and rank_mod(V.T,p) == 9 and rank_mod(W.T,p) == 9 and rank_mod(pairing_matrix(U,V,p),p) == 22:
                break
        sym = symmetry_dimension_sample(U,V,W,p)
        result['random_full_span_symmetry_samples'].append({'trial': trial, **sym})

        # Actual shortened chart with W solved from T for the same U,V.
        cp = chart_probe(U, V, T, p)
        result['random_shortened_chart_samples'].append({'trial': trial, **{k:v for k,v in cp.items() if k != 'uv_rows'}})
        print(f"random trial {trial}: short_rank={cp.get('shortened_jacobian_rank')} residual_nnz={cp.get('shortened_residual_nnz')} sym_uv={sym['combined_uv_rank']}")

    for name, UU, VV in [('cn122', U23, V23), ('serendipitous_8d34', Us23, Vs23)]:
        records = []
        for drop in range(23):
            keep = [i for i in range(23) if i != drop]
            rec = chart_probe(UU[keep] % p, VV[keep] % p, T, p)
            rec['drop_term'] = drop
            # suppress long uv_rows but keep head and exact row hash-like list if needed
            rec.pop('uv_rows', None)
            records.append(rec)
            print(f"{name} drop {drop:2d}: usable={rec['usable']} short_rank={rec.get('shortened_jacobian_rank')} resid={rec.get('shortened_residual_nnz')} in_image={rec.get('shortened_residual_in_jacobian_image')}")
        if name == 'cn122':
            result['cn122_deletion_shortened_chart'] = records
        else:
            result['serendipitous_deletion_shortened_chart'] = records

    for key in ['random_shortened_chart_samples','cn122_deletion_shortened_chart','serendipitous_deletion_shortened_chart']:
        ranks = [x.get('shortened_jacobian_rank') for x in result[key] if x.get('usable')]
        resid = [x.get('shortened_residual_nnz') for x in result[key] if x.get('usable')]
        inimg = [x.get('shortened_residual_in_jacobian_image') for x in result[key] if x.get('usable')]
        result[key + '_summary'] = {
            'count': len(ranks),
            'short_rank_minmax': [int(min(ranks)), int(max(ranks))] if ranks else None,
            'residual_nnz_minmax': [int(min(resid)), int(max(resid))] if resid else None,
            'residual_in_short_image_count': int(sum(bool(z) for z in inimg)),
            'forced_short_rank_max': 328,
            'short_rank_le_forced_count': int(sum(int(r <= 328) for r in ranks)),
        }

    result['elapsed_sec'] = time.time() - t0
    out.write_text(json.dumps(result, indent=2, sort_keys=True, default=int) + '\n')
    print(f"wrote {out}")


if __name__ == '__main__':
    main()
