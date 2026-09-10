#!/usr/bin/env python3
"""Tight-contraction trace filter for full T<3,3,3> fixed A-multisets.

For a fixed full A-multiset a_t, relax each rank-one B/C matrix v_t w_t^T
to an arbitrary 9x9 matrix X_t and impose

    sum_t a_t[s] X_t = T_s    for s=0..8.

For any nonzero A-contraction lambda, M_lambda=sum_s lambda_s T_s has matrix
rank rho=3*rank(lambda as 3x3 matrix).  If exactly rho active terms have
<lambda,a_t>=1, equality in the matrix-rank lower bound forces those terms to
form a minimal rank decomposition of M_lambda.  For any generalized inverse G
of M_lambda, every active rank-one term then satisfies trace(G X_t)=1.  Adding
these trace equations gives a fast necessary condition for exact fixed-A Brent
completion.  Consistency is not sufficient; inconsistency rejects a candidate.
"""
from __future__ import annotations

import argparse
import itertools
import json
import os
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from pivot_fixed_full_wang import parse_multiset_arg  # type: ignore
from quotient_tight_trace_filter import mat_rank, generalized_inverse, row_to_int, rank_int, consistent, trace_coeff_row, greedy_irredundant, combo_min_subset  # type: ignore


def build_t333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T


def build_tensor_rows(T: np.ndarray, support: Sequence[int]) -> tuple[list[int], list[int]]:
    nvars = 81 * len(support)
    rows: list[int] = []
    rhs: list[int] = []
    for s in range(9):
        active = [t for t, a in enumerate(support) if (int(a) >> s) & 1]
        for b in range(9):
            for c in range(9):
                x = 0
                local = 9 * b + c
                for t in active:
                    x |= 1 << (81 * t + local)
                rows.append(x)
                rhs.append(int(T[s, b, c]))
    return rows, rhs


def lambda_matrix(T: np.ndarray, lam: int) -> np.ndarray:
    M = np.zeros((9, 9), dtype=np.uint8)
    for s in range(9):
        if (int(lam) >> s) & 1:
            M ^= T[s]
    return M


def tight_lambda_data(T: np.ndarray, support: Sequence[int]) -> list[dict]:
    out = []
    for lam in range(1, 512):
        active = [t for t, a in enumerate(support) if ((int(lam) & int(a)).bit_count() & 1)]
        M = lambda_matrix(T, lam)
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


def analyze(support: list[int], min_combo: int = 0) -> dict:
    t0 = time.time()
    T = build_t333()
    nvars = 81 * len(support)
    base_rows, base_rhs = build_tensor_rows(T, support)
    base_ok, base_rank, base_aug = consistent(base_rows, base_rhs, nvars)
    tight = tight_lambda_data(T, support)
    all_rows, all_rhs = add_trace_for_lambdas(base_rows, base_rhs, support, tight)
    full_ok, full_rank, full_aug = consistent(all_rows, all_rhs, nvars)
    rank_hist = Counter(int(rec["rank"]) for rec in tight)
    active_hist = Counter(len(rec["active_terms"]) for rec in tight)
    mult_hist = Counter(Counter(int(a) for a in support).values())
    result = {
        "schema": "full_tight_trace_filter_v1",
        "support": [int(a) for a in support],
        "support_size": len(support),
        "distinct_A_count": len(set(int(a) for a in support if int(a) != 0)),
        "A_multiplicity_hist": dict(sorted((int(k), int(v)) for k, v in mult_hist.items())),
        "variables_X": nvars,
        "tensor_equations": len(base_rows),
        "tensor_consistent": base_ok,
        "tensor_rank_aug": [base_rank, base_aug],
        "tight_lambda_count": len(tight),
        "tight_rank_hist": dict(sorted((int(k), int(v)) for k, v in rank_hist.items())),
        "tight_active_hist": dict(sorted((int(k), int(v)) for k, v in active_hist.items())),
        "trace_equations": len(all_rows) - len(base_rows),
        "full_equations": len(all_rows),
        "full_trace_consistent": full_ok,
        "full_rank_aug": [full_rank, full_aug],
        "tight_lambdas_head": [{"lambda": int(r["lambda"]), "rank": int(r["rank"]), "active_terms": [int(t) for t in r["active_terms"]]} for r in tight[:80]],
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
        if min_combo > 0 and len(tight) <= 90:
            result["combination_min_subset"] = combo_min_subset(base_rows, base_rhs, support, tight, nvars, min_combo)
    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--multiset", required=True, help="comma-separated full A multiset or JSON file readable by pivot_fixed_full_wang.parse_multiset_arg")
    ap.add_argument("--min-combo", type=int, default=0)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    support = parse_multiset_arg(args.multiset)
    result = analyze(support, min_combo=args.min_combo)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "support_size": result["support_size"],
        "tensor_consistent": result["tensor_consistent"],
        "tight_lambda_count": result["tight_lambda_count"],
        "tight_rank_hist": result["tight_rank_hist"],
        "trace_equations": result["trace_equations"],
        "full_trace_consistent": result["full_trace_consistent"],
        "full_rank_aug": result["full_rank_aug"],
        "greedy_irredundant_subset": result.get("greedy_irredundant_subset"),
        "elapsed_sec": result["elapsed_sec"],
        "out": str(args.out),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
