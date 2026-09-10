#!/usr/bin/env python3
r"""
analysis: exact cn122 relation-space data for the projected-kernel model.

For a rank-r decomposition with X=[u_i \otimes v_i] and Tuv=X W^T,
QX relations correspond to elements of L=im(Tuv).  At cn122 (r=23),
rank(QX)=14 and ker(QX) is 9-dimensional; the nine W-coordinate columns
W^T e_c give an exact basis of this relation space.

For any one-term deletion d, the old cn122 terms can still represent the
8-dimensional hyperplane {y in L : <w_d,y>=0}; the missing direction is governed
by the dropped W-factor.  This script records those ranks and exact identities.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import List, Tuple

import sympy as sp


def load_qmm(path: Path) -> Tuple[sp.Matrix, sp.Matrix, sp.Matrix]:
    U: List[List[int]] = []
    V: List[List[int]] = []
    W: List[List[int]] = []
    for line in path.read_text().splitlines():
        p = line.strip().split()
        if len(p) >= 10 and p[0] in ("u", "v", "w"):
            {"u": U, "v": V, "w": W}[p[0]].append([int(x) for x in p[1:10]])
    # Return 9 x r matrices.
    return sp.Matrix(U).T, sp.Matrix(V).T, sp.Matrix(W).T


def t333_uv_flat() -> sp.Matrix:
    Tuv = sp.zeros(81, 9)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a = 3 * i + j
                b = 3 * j + k
                c = 3 * i + k
                Tuv[a * 9 + b, c] = 1
    return Tuv


def sparse_quotient_Q() -> sp.Matrix:
    support_by_c = {c: [] for c in range(9)}
    support_rows = set()
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a = 3 * i + j
                b = 3 * j + k
                c = 3 * i + k
                uv = a * 9 + b
                support_by_c[c].append(uv)
                support_rows.add(uv)
    rows = []
    for uv in range(81):
        if uv not in support_rows:
            row = [0] * 81
            row[uv] = 1
            rows.append(row)
    for c in range(9):
        supp = sorted(support_by_c[c])
        anchor = supp[0]
        for uv in supp[1:]:
            row = [0] * 81
            row[uv] = 1
            row[anchor] = -1
            rows.append(row)
    Q = sp.Matrix(rows)
    assert Q.shape == (72, 81)
    return Q


def pairing_X(U: sp.Matrix, V: sp.Matrix) -> sp.Matrix:
    r = U.shape[1]
    X = sp.zeros(81, r)
    for t in range(r):
        for a in range(9):
            for b in range(9):
                X[a * 9 + b, t] = U[a, t] * V[b, t]
    return X


def mat3_rank_from_vec(v: List[int]) -> int:
    return int(sp.Matrix(3, 3, v).rank())


def vec_gcd(v: List[int]) -> int:
    g = 0
    for x in v:
        g = sp.igcd(g, int(x))
    return abs(int(g))


def primitive(v: List[int]) -> List[int]:
    g = vec_gcd(v)
    if g == 0:
        return v
    vv = [int(x // g) for x in v]
    for x in vv:
        if x != 0:
            if x < 0:
                vv = [-y for y in vv]
            break
    return vv


def rank_mod_int_matrix(M: sp.Matrix, p: int) -> int:
    A = [[int(M[i, j]) % p for j in range(M.shape[1])] for i in range(M.shape[0])]
    m, n = len(A), len(A[0]) if A else 0
    row = 0
    for col in range(n):
        piv = None
        for rr in range(row, m):
            if A[rr][col] % p:
                piv = rr; break
        if piv is None:
            continue
        if piv != row:
            A[row], A[piv] = A[piv], A[row]
        inv = pow(A[row][col] % p, p - 2, p)
        A[row] = [(x * inv) % p for x in A[row]]
        for rr in range(m):
            if rr != row and A[rr][col] % p:
                f = A[rr][col] % p
                A[rr] = [(A[rr][cc] - f * A[row][cc]) % p for cc in range(n)]
        row += 1
        if row == m:
            break
    return row


def main() -> None:
    ws = Path("research/research_record/workspace")
    outdir = ws / "data/projected_relations"
    outdir.mkdir(parents=True, exist_ok=True)
    U, V, W = load_qmm(ws / "data/cn122_r23_reproduce/scheme.qmm")
    Q = sparse_quotient_Q()
    Tuv = t333_uv_flat()
    X = pairing_X(U, V)
    QX = Q * X
    err_QT = Q * Tuv
    err_T = X * W.T - Tuv
    Wt = W.T  # 23 x 9; columns are relation vectors in term coefficient space.
    qxw = QX * Wt
    ranks_mod = {str(p): rank_mod_int_matrix(QX, p) for p in [3, 5, 7, 11, 65521]}
    Wt_ranks_mod = {str(p): rank_mod_int_matrix(Wt, p) for p in [3, 5, 7, 11, 65521]}
    # Sympy exact rank is cheap at 72x23.
    rank_QX_Q = int(QX.rank())
    rank_X_Q = int(X.rank())
    rank_Wt_Q = int(Wt.rank())
    # Verify each deletion: rank(QX_keep) and the dimension of old L recovered by old W coefficients.
    deletion = []
    for d in range(23):
        keep = [j for j in range(23) if j != d]
        QXk = QX[:, keep]
        Xk = X[:, keep]
        Wtk = Wt[keep, :]
        wd = [int(W[i, d]) for i in range(9)]
        deletion.append({
            "drop_term": d,
            "rank_X_keep_Q": int(Xk.rank()),
            "rank_QX_keep_Q": int(QXk.rank()),
            "dim_spanXkeep_intersect_L_from_dimensions": int(Xk.rank() - QXk.rank()),
            "rank_W_keepT_map_y_to_coefficients": int(Wtk.rank()),
            "dropped_w_vector": wd,
            "dropped_w_matrix_rank": mat3_rank_from_vec(wd),
            "dropped_w_nonzero_count": int(sum(1 for x in wd if x != 0)),
            "dropped_w_primitive": primitive(wd),
        })
    # Exact relation basis from W, not from arbitrary nullspace, plus rank type of target slice matrices.
    relations = []
    for c in range(9):
        coeff = [int(W[c, t]) for t in range(23)]
        xcomb = X * sp.Matrix(coeff)
        target = Tuv[:, c]
        relations.append({
            "L_coordinate": c,
            "coeff_support_size": int(sum(1 for x in coeff if x != 0)),
            "coeff_l1": int(sum(abs(x) for x in coeff)),
            "coeff_primitive": primitive(coeff),
            "exact_X_relation_equals_T_slice": bool(xcomb == target),
        })
    result = {
        "description": "Exact relation-space data for cn122 in the projected-kernel quotient Q.",
        "mathematical_identity": "QX lambda=0 iff X lambda is in L=im(Tuv); for cn122, lambda=W^T y gives X lambda=Tuv y.",
        "shapes": {"U": list(U.shape), "V": list(V.shape), "W": list(W.shape), "X": list(X.shape), "Q": list(Q.shape), "QX": list(QX.shape)},
        "exact_checks": {
            "Q_Tuv_zero": bool(err_QT == sp.zeros(72, 9)),
            "X_WT_minus_Tuv_zero": bool(err_T == sp.zeros(81, 9)),
            "QX_WT_zero": bool(qxw == sp.zeros(72, 9)),
            "rank_X_Q": rank_X_Q,
            "rank_QX_Q": rank_QX_Q,
            "dim_kernel_QX_Q": int(23 - rank_QX_Q),
            "rank_WT_Q": rank_Wt_Q,
            "ranks_QX_mod_primes": ranks_mod,
            "ranks_WT_mod_primes": Wt_ranks_mod,
        },
        "deletions": deletion,
        "deletion_summary": {
            "rank_QX_keep_hist": {str(v): sum(1 for d in deletion if d["rank_QX_keep_Q"] == v) for v in sorted(set(d["rank_QX_keep_Q"] for d in deletion))},
            "rank_X_keep_hist": {str(v): sum(1 for d in deletion if d["rank_X_keep_Q"] == v) for v in sorted(set(d["rank_X_keep_Q"] for d in deletion))},
            "intersection_dim_hist": {str(v): sum(1 for d in deletion if d["dim_spanXkeep_intersect_L_from_dimensions"] == v) for v in sorted(set(d["dim_spanXkeep_intersect_L_from_dimensions"] for d in deletion))},
            "dropped_w_rank_hist": {str(v): sum(1 for d in deletion if d["dropped_w_matrix_rank"] == v) for v in sorted(set(d["dropped_w_matrix_rank"] for d in deletion))},
        },
        "relations_from_W_columns": relations,
        "interpretation": "Every one-term deletion of cn122 leaves X_keep rank 22 but rank(QX_keep)=14, so the old 22 UV columns meet L in only eight dimensions. The missing hyperplane in L is w_d^T y=0, governed by the dropped W-factor. This exact structure explains why direct deletion has rank(pi X)=14, not the rank-13 condition required for a full-rank rank-22 solution.",
    }
    out = outdir / "cn122_projected_relation_space.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"rank_X_Q={rank_X_Q} rank_QX_Q={rank_QX_Q} rank_WT_Q={rank_Wt_Q}")
    print(f"deletion rank_QX hist {result['deletion_summary']['rank_QX_keep_hist']} intersection hist {result['deletion_summary']['intersection_dim_hist']} w-rank hist {result['deletion_summary']['dropped_w_rank_hist']}")
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
