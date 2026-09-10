#!/usr/bin/env python3
"""Add quotient B/C subspace-span cuts to dim-2 occupation systems.

For Q_W in A'⊗B⊗C with dim A'=7 and a quotient subspace U≤A', any
rank-r decomposition with A-multiplicity vector x satisfies

    x(U) <= r - dim span_{lambda in U^perp} Col(M_lambda),
    x(U) <= r - dim span_{lambda in U^perp} Row(M_lambda),

because terms with a_t in U vanish in all contractions by U^perp, and the
remaining r-x(U) B/C factors must span those column/row spaces.  This script
combines these caps with inherited Wang caps and solves the resulting integer
occupation problem for the analysis dim-2 quotient orbits.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:  # pragma: no cover
    cp_model = None

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))

from node_local_occupation_closure import (  # type: ignore
    LUT_PATH,
    strict_nonzero_proper_subspaces,
    rref_basis,
    pack_basis,
    free_bits_from_rref,
    lift_q,
    mask_from_qbasis,
    popcount,
)
from dim2_quotient_det import orbit_basis, quotient_tensor_W, lambda_matrix  # type: ignore


def rank_int(rows: Iterable[int]) -> int:
    basis = {}
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


def dot_parity(a: int, b: int) -> int:
    return (int(a) & int(b)).bit_count() & 1


def col_row_span_dims(Q, U_qbasis: Sequence[int]) -> tuple[int, int, list[int]]:
    k = Q.shape[0]
    lambdas = []
    for lam in range(1, 1 << k):
        if all(dot_parity(lam, u) == 0 for u in U_qbasis):
            lambdas.append(lam)
    col_vecs = []
    row_vecs = []
    for lam in lambdas:
        M = lambda_matrix(Q, lam)
        for c in range(9):
            x = 0
            for r in range(9):
                if int(M[r, c]) & 1:
                    x |= 1 << r
            if x:
                col_vecs.append(x)
        for r in range(9):
            x = 0
            for c in range(9):
                if int(M[r, c]) & 1:
                    x |= 1 << c
            if x:
                row_vecs.append(x)
    return rank_int(col_vecs), rank_int(row_vecs), lambdas


def load_lut():
    with LUT_PATH.open("rb") as f:
        d = pickle.load(f)
    return d["lut"] if isinstance(d, dict) and "lut" in d else d


def build_rows(orbit_index: int, target: int):
    W = rref_basis(orbit_basis(orbit_index), 9)
    k = 9 - len(W)
    assert k == 7
    free = free_bits_from_rref(W, 9)
    Q = quotient_tensor_W(W)
    lut = load_lut()
    constraints = {}
    row_recs = []
    hist = Counter(); source_hist = Counter(); tighten_hist = Counter(); dim_hist = Counter(); pop_hist = Counter()
    min_cap = 999
    tightened = 0
    for qbasis in strict_nonzero_proper_subspaces(k):
        U_full = rref_basis((*W, *[lift_q(q, free) for q in qbasis]), 9)
        key = pack_basis(U_full)
        lb = int(lut[key])
        wang_cap = int(target) - lb
        dB, dC, lambdas = col_row_span_dims(Q, qbasis)
        bcap = int(target) - dB
        ccap = int(target) - dC
        cap = min(wang_cap, bcap, ccap)
        mask = mask_from_qbasis(tuple(qbasis))
        if mask not in constraints or cap < constraints[mask][0]:
            constraints[mask] = (cap, wang_cap, bcap, ccap, dB, dC, lb, len(qbasis), len(lambdas))
        if cap < wang_cap:
            tightened += 1
            tighten_hist[wang_cap - cap] += 1
        hist[cap] += 1; source_hist[lb] += 1; dim_hist[len(qbasis)] += 1; pop_hist[popcount(mask)] += 1
        min_cap = min(min_cap, cap)
    rows = []
    for mask, (cap, wang_cap, bcap, ccap, dB, dC, lb, qdim, nlams) in sorted(constraints.items(), key=lambda kv: (kv[1][0], popcount(kv[0]), kv[0])):
        pts = [i + 1 for i in range((1 << k) - 1) if (int(mask) >> i) & 1]
        rows.append({
            "mask": int(mask), "pts": pts, "cap": int(cap), "wang_cap": int(wang_cap),
            "bcap": int(bcap), "ccap": int(ccap), "DB": int(dB), "DC": int(dC),
            "source_lb": int(lb), "qdim": int(qdim), "dual_lambda_count": int(nlams),
        })
    meta = {
        "orbit_index": int(orbit_index),
        "W_basis": [int(x) for x in W],
        "target": int(target),
        "quotient_dim": int(k),
        "quotient_tensor_nnz": int(Q.sum()),
        "strict_subspace_rows": len(strict_nonzero_proper_subspaces(k)),
        "unique_masks": len(rows),
        "cap_hist_combined": dict(sorted((int(k), int(v)) for k, v in hist.items())),
        "source_lb_hist": dict(sorted((int(k), int(v)) for k, v in source_hist.items())),
        "subspace_dim_hist": dict(sorted((int(k), int(v)) for k, v in dim_hist.items())),
        "mask_popcount_hist": dict(sorted((int(k), int(v)) for k, v in pop_hist.items())),
        "tightened_vs_wang_rows": int(tightened),
        "tighten_gain_hist": dict(sorted((int(k), int(v)) for k, v in tighten_hist.items())),
        "min_combined_cap": int(min_cap),
        "negative_cap_rows": int(sum(1 for r in rows if r["cap"] < 0)),
    }
    return rows, meta


def solve_int(rows: list[dict], target: int, time_limit: float, workers: int):
    if cp_model is None:
        return {"status": "NO_OR_TOOLS", "feasible": None}
    model = cp_model.CpModel()
    xs = [model.NewIntVar(0, target, f"x_{q}") for q in range(1, 128)]
    model.Add(sum(xs) == target)
    for r in rows:
        cap = int(r["cap"])
        if cap < 0:
            model.Add(0 <= -1)
        else:
            model.Add(sum(xs[q - 1] for q in r["pts"]) <= cap)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = 2525
    t0 = time.time()
    st = solver.Solve(model)
    elapsed = time.time() - t0
    name = solver.StatusName(st)
    out = {"status": name, "elapsed_sec": elapsed, "conflicts": int(solver.NumConflicts()), "branches": int(solver.NumBranches())}
    if st in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        sol = [int(solver.Value(x)) for x in xs]
        nz = [(i + 1, int(v)) for i, v in enumerate(sol) if v]
        out.update({
            "feasible": True,
            "solution_head": nz[:127],
            "solution_weight_check": int(sum(v for _i, v in nz)),
            "support_nonzero_count": int(len(nz)),
            "max_multiplicity": int(max((v for _i, v in nz), default=0)),
        })
    elif st == cp_model.INFEASIBLE:
        out["feasible"] = False
    else:
        out["feasible"] = None
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--orbit-index", type=int, required=True)
    ap.add_argument("--target", type=int, default=18)
    ap.add_argument("--time-limit", type=float, default=120)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    t0 = time.time()
    rows, meta = build_rows(args.orbit_index, args.target)
    solve = solve_int(rows, args.target, args.time_limit, args.workers)
    out = {
        "schema": "dim2_bc_cut_solver_v1",
        "meta": meta,
        "solve": solve,
        "rows_head": [{k: v for k, v in r.items() if k != "pts"} for r in rows[:200]],
        "elapsed_sec": time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(args.out), "orbit_index": args.orbit_index, "meta": meta, "solve": solve, "elapsed_sec": out["elapsed_sec"]}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
