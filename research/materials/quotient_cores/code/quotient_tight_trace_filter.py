#!/usr/bin/env python3
"""Tight-contraction trace filter for fixed quotient A-supports.

Given Q_p in F2^{8 x 9 x 9} and a fixed list of quotient A-directions u_t,
relax each rank-one B/C outer product to an arbitrary 9x9 matrix X_t.
The tensor equations are linear:
    sum_t u_t[s] X_t = Q_p[s].
For any dual lambda with M_lambda=sum_s lambda_s Q_p[s] of rank rho and exactly
rho active support terms, every true rank-one completion must be a minimal rank
decomposition of M_lambda.  If G is any generalized inverse obtained from
P M Q = diag(I_rho,0), each active term must satisfy
    trace(G X_t) = 1.
This script adds those trace equations over F2.  Inconsistency rejects the
fixed A-support before the nonlinear B/C solve.
"""
from __future__ import annotations

import argparse
import itertools
import json
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np


def quotient_tensor(pivot: int) -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1
    h = int(pivot).bit_length() - 1
    Q = np.zeros((8, 9, 9), dtype=np.uint8)
    for a_bit in range(9):
        a_val = 1 << a_bit
        qa = a_val
        if (qa >> h) & 1:
            qa ^= int(pivot)
        low = qa & ((1 << h) - 1)
        high = (qa >> (h + 1)) << h
        q_idx = low | high
        # If q_idx==0, the slice lies in the quotient kernel and vanishes.
        if q_idx:
            for qb in range(8):
                if (q_idx >> qb) & 1:
                    Q[qb] ^= T[a_bit]
    return Q


def parse_support(s: str) -> list[int]:
    p = Path(s)
    if p.exists():
        data = json.loads(p.read_text())
        if isinstance(data, list):
            return [int(x) for x in data]
        for key in ["support", "solution", "A_support", "a_vecs", "best_support"]:
            if key in data:
                return [int(x) for x in data[key]]
        if "rounds" in data:
            for r in reversed(data["rounds"]):
                if r.get("fully_admissible") and r.get("solution"):
                    return [int(x) for x in r["solution"]]
        raise ValueError(f"no support-like key in {s}")
    return [int(x) for x in s.replace(";", ",").replace(" ", ",").split(",") if x.strip()]


def mat_rank(M: np.ndarray) -> int:
    A = (M.copy() & 1).astype(np.uint8)
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i, c]:
                piv = i
                break
        if piv is None:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(m):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
        if r == m:
            break
    return int(r)


def generalized_inverse(M: np.ndarray) -> tuple[np.ndarray, int, np.ndarray, np.ndarray, np.ndarray]:
    """Return G, rank, P, Q, D with P M Q = D=diag(I_r,0) and G=Q D+ P."""
    A = (M.copy() & 1).astype(np.uint8)
    n = A.shape[0]
    assert A.shape == (n, n)
    P = np.eye(n, dtype=np.uint8)
    Q = np.eye(n, dtype=np.uint8)
    r = 0
    while r < n:
        piv = None
        for i in range(r, n):
            for j in range(r, n):
                if A[i, j]:
                    piv = (i, j)
                    break
            if piv is not None:
                break
        if piv is None:
            break
        i0, j0 = piv
        if i0 != r:
            A[[r, i0]] = A[[i0, r]]
            P[[r, i0]] = P[[i0, r]]
        if j0 != r:
            A[:, [r, j0]] = A[:, [j0, r]]
            Q[:, [r, j0]] = Q[:, [j0, r]]
        for i in range(n):
            if i != r and A[i, r]:
                A[i] ^= A[r]
                P[i] ^= P[r]
        for j in range(n):
            if j != r and A[r, j]:
                A[:, j] ^= A[:, r]
                Q[:, j] ^= Q[:, r]
        r += 1
    Dplus = np.zeros((n, n), dtype=np.uint8)
    for i in range(r):
        Dplus[i, i] = 1
    G = ((Q @ Dplus @ P) & 1).astype(np.uint8)
    # sanity checks
    if not np.array_equal((P @ M @ Q) & 1, A & 1):
        raise RuntimeError("P M Q sanity failed")
    if not np.array_equal((M @ G @ M) & 1, M & 1):
        raise RuntimeError("generalized inverse sanity failed")
    return G, int(r), P, Q, A


def row_to_int(coeffs: Iterable[int]) -> int:
    x = 0
    for i, b in enumerate(coeffs):
        if int(b) & 1:
            x |= 1 << i
    return x


def rank_int(rows: Sequence[int]) -> int:
    basis: dict[int, int] = {}
    r = 0
    for row in rows:
        x = int(row)
        while x:
            p = x.bit_length() - 1
            b = basis.get(p)
            if b is None:
                basis[p] = x
                r += 1
                break
            x ^= b
    return r


def consistent(rows: Sequence[int], rhs: Sequence[int], nvars: int) -> tuple[bool, int, int]:
    r = rank_int(rows)
    aug = [int(row) | ((int(b) & 1) << nvars) for row, b in zip(rows, rhs)]
    ra = rank_int(aug)
    return r == ra, r, ra


def build_tensor_rows(Q: np.ndarray, support: Sequence[int]) -> tuple[list[int], list[int]]:
    nvars = 81 * len(support)
    rows: list[int] = []
    rhs: list[int] = []
    for s in range(8):
        active = [t for t, u in enumerate(support) if (int(u) >> s) & 1]
        for b in range(9):
            for c in range(9):
                x = 0
                local = 9 * b + c
                for t in active:
                    x |= 1 << (81 * t + local)
                rows.append(x)
                rhs.append(int(Q[s, b, c]))
    return rows, rhs


def lambda_matrix(Q: np.ndarray, lam: int) -> np.ndarray:
    M = np.zeros((9, 9), dtype=np.uint8)
    for s in range(8):
        if (int(lam) >> s) & 1:
            M ^= Q[s]
    return M


def trace_coeff_row(G: np.ndarray, term: int, nterms: int) -> int:
    # trace(G X)=sum_{i,j} G[i,j] X[j,i]; variable local index is 9*row+col.
    x = 0
    base = 81 * term
    for row in range(9):
        for col in range(9):
            if G[col, row] & 1:
                x |= 1 << (base + 9 * row + col)
    return x


def tight_lambda_data(Q: np.ndarray, support: Sequence[int]) -> list[dict]:
    out = []
    for lam in range(1, 256):
        active = [t for t, u in enumerate(support) if ((int(lam) & int(u)).bit_count() & 1)]
        M = lambda_matrix(Q, lam)
        rank = mat_rank(M)
        if len(active) == rank and rank > 0:
            G, r2, _P, _Q, _D = generalized_inverse(M)
            assert r2 == rank
            out.append({"lambda": lam, "rank": rank, "active_terms": active, "G": G})
    return out


def add_trace_for_lambdas(base_rows: list[int], base_rhs: list[int], support: Sequence[int], lambdas: Sequence[dict]) -> tuple[list[int], list[int]]:
    rows = list(base_rows)
    rhs = list(base_rhs)
    nterms = len(support)
    for rec in lambdas:
        G = rec["G"]
        for t in rec["active_terms"]:
            rows.append(trace_coeff_row(G, int(t), nterms))
            rhs.append(1)
    return rows, rhs


def greedy_irredundant(base_rows: list[int], base_rhs: list[int], support: Sequence[int], lambdas: list[dict], nvars: int) -> list[dict]:
    cur = list(lambdas)
    changed = True
    while changed:
        changed = False
        for rec in list(cur):
            trial = [x for x in cur if x is not rec]
            rows, rhs = add_trace_for_lambdas(base_rows, base_rhs, support, trial)
            ok, _, _ = consistent(rows, rhs, nvars)
            if not ok:
                cur = trial
                changed = True
    return cur


def combo_min_subset(base_rows: list[int], base_rhs: list[int], support: Sequence[int], lambdas: list[dict], nvars: int, max_k: int) -> dict:
    ids = list(range(len(lambdas)))
    checked_by_size = {}
    for k in range(1, min(max_k, len(ids)) + 1):
        checked = 0
        examples = []
        for comb in itertools.combinations(ids, k):
            checked += 1
            subset = [lambdas[i] for i in comb]
            rows, rhs = add_trace_for_lambdas(base_rows, base_rhs, support, subset)
            ok, _, _ = consistent(rows, rhs, nvars)
            if not ok:
                examples.append([int(lambdas[i]["lambda"]) for i in comb])
                if len(examples) >= 20:
                    break
        checked_by_size[str(k)] = checked
        if examples:
            return {"found": True, "size": k, "examples": examples, "checked_by_size": checked_by_size}
    return {"found": False, "size": None, "examples": [], "checked_by_size": checked_by_size}


def analyze(pivot: int, support: list[int], min_combo: int = 0) -> dict:
    t0 = time.time()
    Q = quotient_tensor(pivot)
    nvars = 81 * len(support)
    base_rows, base_rhs = build_tensor_rows(Q, support)
    base_ok, base_rank, base_aug = consistent(base_rows, base_rhs, nvars)
    tight = tight_lambda_data(Q, support)
    all_rows, all_rhs = add_trace_for_lambdas(base_rows, base_rhs, support, tight)
    full_ok, full_rank, full_aug = consistent(all_rows, all_rhs, nvars)
    rank_hist = Counter(int(rec["rank"]) for rec in tight)
    active_hist = Counter(len(rec["active_terms"]) for rec in tight)
    result = {
        "schema": "quotient_tight_trace_filter_v1",
        "pivot": int(pivot),
        "support": support,
        "support_size": len(support),
        "variables_X": nvars,
        "tensor_equations": len(base_rows),
        "tensor_consistent": base_ok,
        "tensor_rank_aug": [base_rank, base_aug],
        "tight_lambda_count": len(tight),
        "tight_rank_hist": dict(sorted(rank_hist.items())),
        "tight_active_hist": dict(sorted(active_hist.items())),
        "trace_equations": len(all_rows) - len(base_rows),
        "full_equations": len(all_rows),
        "full_trace_consistent": full_ok,
        "full_rank_aug": [full_rank, full_aug],
        "tight_lambdas_head": [{"lambda": int(r["lambda"]), "rank": int(r["rank"]), "active_terms": [int(t) for t in r["active_terms"]]} for r in tight[:50]],
        "elapsed_sec": time.time() - t0,
    }
    if not full_ok and tight:
        t1 = time.time()
        red = greedy_irredundant(base_rows, base_rhs, support, tight, nvars)
        result["greedy_irredundant_subset"] = {
            "count": len(red),
            "lambdas": [int(r["lambda"]) for r in red],
            "ranks": [int(r["rank"]) for r in red],
            "trace_equations": sum(len(r["active_terms"]) for r in red),
            "elapsed_sec": time.time() - t1,
        }
        if min_combo > 0 and len(tight) <= 80:
            result["combination_min_subset"] = combo_min_subset(base_rows, base_rhs, support, tight, nvars, min_combo)
    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot", type=int, required=True)
    ap.add_argument("--pivot-name", default="")
    ap.add_argument("--support", required=True)
    ap.add_argument("--min-combo", type=int, default=0)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    support = parse_support(args.support)
    result = analyze(args.pivot, support, min_combo=args.min_combo)
    if args.pivot_name:
        result["pivot_name"] = args.pivot_name
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "pivot_name": args.pivot_name,
        "pivot": args.pivot,
        "support_size": result["support_size"],
        "tensor_consistent": result["tensor_consistent"],
        "tight_lambda_count": result["tight_lambda_count"],
        "tight_rank_hist": result["tight_rank_hist"],
        "trace_equations": result["trace_equations"],
        "full_trace_consistent": result["full_trace_consistent"],
        "full_rank_aug": result["full_rank_aug"],
        "greedy_irredundant_subset": result.get("greedy_irredundant_subset"),
        "out": str(args.out),
        "elapsed_sec": round(result["elapsed_sec"], 3),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
