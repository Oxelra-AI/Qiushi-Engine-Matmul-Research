#!/usr/bin/env python3
"""Code-theoretic LP/MILP relaxations for the Wang T-level capacity problem.

For a hypothetical rank-20 F2 decomposition of T_<3,3,3>, the 20 distinct
A-factors form a projective binary [20,9] code C by evaluating every 3x3
matrix M on the selected columns a_t. Wang's dim-8 subspace bounds imply
that a nonzero message M of matrix rank r has Hamming weight at least 3r.
This script builds increasingly strong linear relaxations of that object:

  simple: split weight enumerator A_{rank,w} + MacWilliams dual constraints.
  first:  additionally tie first weight moments to column-rank counts.
  pair:   additionally tie second moments to pair categories of A-columns.

These relaxations are not yet the full Wang capacity system. They are meant
as cheap Delsarte/MacWilliams pressure tests: infeasibility would be a finite
certificate target; feasibility exposes slack and guides stronger enumeration.
"""
from __future__ import annotations

import argparse
import json
import math
import time
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import lil_matrix, vstack

N = 20
K = 9
Q = 2
CODE_SIZE = 1 << K
RANK_COUNTS = {1: 49, 2: 294, 3: 168}
MIN_WEIGHT = {1: 3, 2: 6, 3: 9}
POINTS = list(range(1, 1 << 9))


def mask_to_mat(mask: int) -> np.ndarray:
    return np.array([(mask >> i) & 1 for i in range(9)], dtype=np.uint8).reshape(3, 3)


def mat_rank_f2_from_mask(mask: int) -> int:
    rows = [((mask >> (3 * i)) & 7) for i in range(3)]
    rows = [r for r in rows if r]
    rank = 0
    bit = 4
    while bit:
        piv = None
        for i in range(rank, len(rows)):
            if rows[i] & bit:
                piv = i
                break
        if piv is not None:
            rows[rank], rows[piv] = rows[piv], rows[rank]
            for j in range(len(rows)):
                if j != rank and (rows[j] & bit):
                    rows[j] ^= rows[rank]
            rank += 1
        bit >>= 1
    return rank


def dot_parity(a: int, b: int) -> int:
    return ((a & b).bit_count() & 1)


def krawtchouk(j: int, w: int, n: int = N) -> int:
    s = 0
    for i in range(j + 1):
        if i <= w and j - i <= n - w:
            s += ((-1) ** i) * math.comb(w, i) * math.comb(n - w, j - i)
    return s


def compute_incidence_counts() -> Dict[Tuple[int, int], int]:
    by_rank = {r: [p for p in POINTS if mat_rank_f2_from_mask(p) == r] for r in (1, 2, 3)}
    reps = {r: by_rank[r][0] for r in (1, 2, 3)}
    inc = {}
    # inc[(message_rank, column_rank)] = number of messages of message_rank hitting fixed column_rank point.
    for mr in (1, 2, 3):
        for cr in (1, 2, 3):
            a = reps[cr]
            c = sum(dot_parity(m, a) for m in by_rank[mr])
            inc[(mr, cr)] = c
    return inc


def compute_pair_categories() -> Tuple[List[dict], Dict[str, int]]:
    """Partition unordered distinct point pairs by endpoint ranks and rank-hit2 counts.

    The category key contains exactly the coefficients needed for the second
    moment constraints, plus endpoint rank multiplicities for consistency.
    It is a relaxation of true G-orbit pair counts but every true selected set
    induces nonnegative integer counts in these categories.
    """
    ranks = {p: mat_rank_f2_from_mask(p) for p in POINTS}
    by_rank = {r: np.array([p for p in POINTS if ranks[p] == r], dtype=np.int16) for r in (1, 2, 3)}
    cats: Dict[Tuple, dict] = {}
    t0 = time.time()
    for idx, a in enumerate(POINTS):
        ra = ranks[a]
        for b in POINTS[idx + 1:]:
            rb = ranks[b]
            # Count rank-r messages hitting both columns.
            hit2 = []
            for mr in (1, 2, 3):
                cnt = 0
                for m in by_rank[mr]:
                    if dot_parity(int(m), a) and dot_parity(int(m), b):
                        cnt += 1
                hit2.append(cnt)
            key = (min(ra, rb), max(ra, rb), ranks[a ^ b], tuple(hit2))
            if key not in cats:
                cats[key] = {
                    "key": key,
                    "endpoint_mult": {1: 0, 2: 0, 3: 0},
                    "rank_sum": ranks[a ^ b],
                    "hit2": {1: hit2[0], 2: hit2[1], 3: hit2[2]},
                    "available_pairs": 0,
                    "example": [a, b],
                }
                cats[key]["endpoint_mult"][ra] += 1
                cats[key]["endpoint_mult"][rb] += 1
            cats[key]["available_pairs"] += 1
    cat_list = sorted(cats.values(), key=lambda c: (c["key"][0], c["key"][1], c["key"][2], c["key"][3]))
    meta = {
        "category_count": len(cat_list),
        "total_pairs": sum(c["available_pairs"] for c in cat_list),
        "elapsed_sec": time.time() - t0,
    }
    return cat_list, meta


@dataclass
class VarIndex:
    names: List[str]
    lb: List[float]
    ub: List[float]
    integrality: List[int]
    a_vars: Dict[Tuple[int, int], int]
    n_vars: Dict[int, int]
    p_vars: Dict[int, int]
    b_vars: Dict[int, int]

    def add(self, name: str, lb: float = 0, ub: float = math.inf, integer: bool = False) -> int:
        i = len(self.names)
        self.names.append(name)
        self.lb.append(lb)
        self.ub.append(ub)
        self.integrality.append(1 if integer else 0)
        return i


def build_problem(mode: str = "simple", integer: bool = False, exact_dual_vars: bool = False):
    vi = VarIndex([], [], [], [], {}, {}, {}, {})
    # Split weight enumerator variables.
    for r in (1, 2, 3):
        for w in range(MIN_WEIGHT[r], N + 1):
            vi.a_vars[(r, w)] = vi.add(f"A_rank{r}_w{w}", 0, RANK_COUNTS[r], integer)
    inc = compute_incidence_counts()
    pair_cats = []
    pair_meta = None
    if mode in ("first", "pair"):
        for q in (1, 2, 3):
            vi.n_vars[q] = vi.add(f"n_col_rank{q}", 0, RANK_COUNTS[q], integer)
    if mode == "pair":
        pair_cats, pair_meta = compute_pair_categories()
        for ci, cat in enumerate(pair_cats):
            vi.p_vars[ci] = vi.add(f"P_cat{ci}", 0, cat["available_pairs"], integer)
    if exact_dual_vars:
        # B_j are dual weight enumerator entries, forced integer in MILP mode.
        for j in range(N + 1):
            vi.b_vars[j] = vi.add(f"B_w{j}", 0, 1 << (N - K), integer)

    rows_eq = []
    rhs_eq = []
    rows_ub = []
    rhs_ub = []
    nvar = len(vi.names)

    def new_row():
        return defaultdict(float)

    def add_eq(row, rhs):
        rows_eq.append(row); rhs_eq.append(rhs)

    def add_ub(row, rhs):
        rows_ub.append(row); rhs_ub.append(rhs)

    # Rank-message counts.
    for r in (1, 2, 3):
        row = new_row()
        for w in range(MIN_WEIGHT[r], N + 1):
            row[vi.a_vars[(r, w)]] = 1
        add_eq(row, RANK_COUNTS[r])

    # Column counts and first moments.
    if mode in ("first", "pair"):
        row = new_row()
        for q in (1, 2, 3): row[vi.n_vars[q]] = 1
        add_eq(row, N)
        for mr in (1, 2, 3):
            row = new_row()
            for w in range(MIN_WEIGHT[mr], N + 1):
                row[vi.a_vars[(mr, w)]] += w
            for cr in (1, 2, 3):
                row[vi.n_vars[cr]] -= inc[(mr, cr)]
            add_eq(row, 0)

    # Pair incidence and second moments.
    if mode == "pair":
        row = new_row()
        for ci in range(len(pair_cats)):
            row[vi.p_vars[ci]] = 1
        add_eq(row, math.comb(N, 2))
        for q in (1, 2, 3):
            row = new_row()
            for ci, cat in enumerate(pair_cats):
                row[vi.p_vars[ci]] += cat["endpoint_mult"][q]
            row[vi.n_vars[q]] -= (N - 1)
            add_eq(row, 0)
        for mr in (1, 2, 3):
            row = new_row()
            for w in range(MIN_WEIGHT[mr], N + 1):
                row[vi.a_vars[(mr, w)]] += w * (w - 1)
            for ci, cat in enumerate(pair_cats):
                row[vi.p_vars[ci]] -= 2 * cat["hit2"][mr]
            add_eq(row, 0)

    # MacWilliams constraints. A_0 includes the zero codeword with coefficient 1.
    if exact_dual_vars:
        for j in range(N + 1):
            row = new_row()
            for (r, w), idx in vi.a_vars.items():
                row[idx] += krawtchouk(j, w)
            row[vi.b_vars[j]] -= CODE_SIZE
            # K_j(0) + sum A_w K_j(w) - |C| B_j = 0
            add_eq(row, -krawtchouk(j, 0))
        # Projective columns: B_1=B_2=0; B_0=1.
        for j, val in [(0, 1), (1, 0), (2, 0)]:
            row = new_row(); row[vi.b_vars[j]] = 1; add_eq(row, val)
    else:
        # B_1 = B_2 = 0 equalities.
        for j in (1, 2):
            row = new_row()
            for (r, w), idx in vi.a_vars.items():
                row[idx] += krawtchouk(j, w)
            add_eq(row, -krawtchouk(j, 0))
        # B_j >= 0 for all j except those handled; -sum <= K_j(0).
        for j in list(range(3, N + 1)):
            row = new_row()
            for (r, w), idx in vi.a_vars.items():
                row[idx] += -krawtchouk(j, w)
            add_ub(row, krawtchouk(j, 0))

    # Convert sparse rows.
    nvar = len(vi.names)
    def to_sparse(rows):
        M = lil_matrix((len(rows), nvar), dtype=float)
        for i, row in enumerate(rows):
            for j, v in row.items():
                if v:
                    M[i, j] = v
        return M.tocsr()
    Aeq = to_sparse(rows_eq)
    Aub = to_sparse(rows_ub)
    beq = np.array(rhs_eq, dtype=float)
    bub = np.array(rhs_ub, dtype=float)
    meta = {
        "mode": mode,
        "integer": integer,
        "exact_dual_vars": exact_dual_vars,
        "num_vars": nvar,
        "num_equalities": len(rhs_eq),
        "num_inequalities": len(rhs_ub),
        "incidence_counts": {f"msg{m}_col{c}": inc[(m,c)] for m in (1,2,3) for c in (1,2,3)},
        "pair_meta": pair_meta,
    }
    return vi, Aeq, beq, Aub, bub, meta, pair_cats


def solve_lp(mode: str, integer: bool, exact_dual_vars: bool, time_limit: float | None):
    vi, Aeq, beq, Aub, bub, meta, pair_cats = build_problem(mode, integer, exact_dual_vars)
    c = np.zeros(len(vi.names), dtype=float)
    bounds = Bounds(np.array(vi.lb, dtype=float), np.array(vi.ub, dtype=float))
    t0 = time.time()
    if integer:
        constraints = []
        if Aeq.shape[0]: constraints.append(LinearConstraint(Aeq, beq, beq))
        if Aub.shape[0]: constraints.append(LinearConstraint(Aub, -np.inf*np.ones_like(bub), bub))
        options = {"disp": False}
        if time_limit is not None:
            options["time_limit"] = time_limit
        res = milp(c=c, integrality=np.array(vi.integrality), bounds=bounds, constraints=constraints, options=options)
        status = res.message
        success = bool(res.success)
        x = None if res.x is None else np.array(res.x)
        fun = None if res.fun is None else float(res.fun)
    else:
        # linprog accepts equality and inequality matrices directly.
        options = {"presolve": True}
        if time_limit is not None:
            options["time_limit"] = time_limit
        res = linprog(c, A_ub=Aub if Aub.shape[0] else None, b_ub=bub if Aub.shape[0] else None,
                      A_eq=Aeq if Aeq.shape[0] else None, b_eq=beq if Aeq.shape[0] else None,
                      bounds=list(zip(vi.lb, vi.ub)), method="highs", options=options)
        status = res.message
        success = bool(res.success)
        x = None if res.x is None else np.array(res.x)
        fun = None if res.fun is None else float(res.fun)
    elapsed = time.time() - t0
    result = {"meta": meta, "solver_status": status, "success": success, "fun": fun, "elapsed_sec": elapsed}
    if x is not None:
        # Extract interpretable distributions.
        split = {str(r): {str(w): float(x[idx]) for (rr, w), idx in vi.a_vars.items() if rr == r and abs(x[idx]) > 1e-7} for r in (1,2,3)}
        total_A = {w: 0.0 for w in range(N+1)}
        total_A[0] = 1.0
        for (r,w), idx in vi.a_vars.items(): total_A[w] += float(x[idx])
        B = {}
        for j in range(N+1):
            val = krawtchouk(j,0) + sum(float(x[idx])*krawtchouk(j,w) for (r,w), idx in vi.a_vars.items())
            B[j] = val / CODE_SIZE
        result["split_weight_enumerator"] = split
        result["A_weight_enumerator"] = {str(w): total_A[w] for w in range(N+1) if abs(total_A[w]) > 1e-7}
        result["dual_weight_enumerator_from_A"] = {str(j): B[j] for j in range(N+1) if abs(B[j]) > 1e-7}
        if vi.n_vars:
            result["column_rank_counts"] = {str(q): float(x[idx]) for q, idx in vi.n_vars.items()}
        if vi.p_vars:
            nz = []
            for ci, idx in vi.p_vars.items():
                if abs(x[idx]) > 1e-7:
                    cat = pair_cats[ci]
                    nz.append({"cat": ci, "value": float(x[idx]), "endpoint_mult": cat["endpoint_mult"], "rank_sum": cat["rank_sum"], "hit2": cat["hit2"], "available_pairs": cat["available_pairs"], "example": cat["example"]})
            result["nonzero_pair_categories"] = nz[:200]
            result["nonzero_pair_category_count"] = len(nz)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["simple", "first", "pair"], default="simple")
    ap.add_argument("--integer", action="store_true")
    ap.add_argument("--exact-dual-vars", action="store_true", help="Use integer dual enumerator variables; meaningful with --integer")
    ap.add_argument("--time-limit", type=float, default=None)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    res = solve_lp(args.mode, args.integer, args.exact_dual_vars, args.time_limit)
    print(json.dumps({k: res[k] for k in ["meta", "solver_status", "success", "elapsed_sec"]}, indent=2))
    if "column_rank_counts" in res:
        print("column_rank_counts", res["column_rank_counts"])
    print("A weights", res.get("A_weight_enumerator"))
    print("dual B nonzero", res.get("dual_weight_enumerator_from_A"))
    if args.out is None:
        tag = f"{args.mode}_{'milp' if args.integer else 'lp'}{'_dualint' if args.exact_dual_vars else ''}.json"
        out = Path("data/wang_code_lp") / tag
    else:
        out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"saved {out}")

if __name__ == "__main__":
    main()
