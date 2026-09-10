#!/usr/bin/env python3
r"""analysis: exact CP-SAT feasibility tests for selected pencil budgets.

This is a witness-finding / solver-evidence tool, not a proof-producing checker.
It encodes the exact rank-factorization equations for

  X0 = W,        rank(X0) <= c11
  X1 = M1 + W,  rank(X1) <= c10
  X2 = M2 + W,  rank(X2) <= c01

by writing Xk = Uk Vk^T over F2 with the requested column counts and enforcing
X0 + X1 = M1, X0 + X2 = M2 entrywise by XOR clauses.  Any SAT model gives a
valid explicit 9x9 W; INFEASIBLE is solver evidence only unless later certified.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np
from ortools.sat.python import cp_model

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/pencil_repair"


def gf2_mat_mul(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    return ((A.astype(np.uint8) @ B.astype(np.uint8)) & 1).astype(np.uint8)


def row_masks(M: np.ndarray) -> List[int]:
    out = []
    for i in range(M.shape[0]):
        x = 0
        for j in range(M.shape[1]):
            if int(M[i,j]) & 1:
                x |= 1 << j
        out.append(x)
    return out


def reconstruct_matrix(Uvals: List[List[int]], Vvals: List[List[int]]) -> np.ndarray:
    n = len(Uvals)
    r = len(Uvals[0]) if Uvals and Uvals[0] else 0
    M = np.zeros((n,n), dtype=np.uint8)
    for i in range(n):
        for j in range(n):
            s = 0
            for k in range(r):
                s ^= Uvals[i][k] & Vvals[j][k]
            M[i,j] = s
    return M


def solve_pencil_factor(M1: np.ndarray, M2: np.ndarray, budget: Tuple[int,int,int], time_limit: float = 30.0, workers: int = 8, seed: int = 57) -> Dict[str, object]:
    c10, c01, c11 = budget
    ranks = [c11, c10, c01]  # X0, X1, X2
    n = 9
    model = cp_model.CpModel()
    true_lit = model.NewBoolVar("true")
    model.Add(true_lit == 1)

    U = []
    V = []
    Z = []
    for h, r in enumerate(ranks):
        Uh = [[model.NewBoolVar(f"U{h}_{i}_{k}") for k in range(r)] for i in range(n)]
        Vh = [[model.NewBoolVar(f"V{h}_{j}_{k}") for k in range(r)] for j in range(n)]
        Zh = [[[model.NewBoolVar(f"Z{h}_{i}_{j}_{k}") for k in range(r)] for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(n):
                for k in range(r):
                    z = Zh[i][j][k]
                    u = Uh[i][k]
                    v = Vh[j][k]
                    model.AddImplication(z, u)
                    model.AddImplication(z, v)
                    model.AddBoolOr([u.Not(), v.Not(), z])
        U.append(Uh); V.append(Vh); Z.append(Zh)

    # Entry equations: X0 + X1 = M1 and X0 + X2 = M2.
    for i in range(n):
        for j in range(n):
            lits01 = []
            for k in range(ranks[0]): lits01.append(Z[0][i][j][k])
            for k in range(ranks[1]): lits01.append(Z[1][i][j][k])
            if int(M1[i,j]) == 0:
                lits01 = lits01 + [true_lit]
            model.AddBoolXOr(lits01)

            lits02 = []
            for k in range(ranks[0]): lits02.append(Z[0][i][j][k])
            for k in range(ranks[2]): lits02.append(Z[2][i][j][k])
            if int(M2[i,j]) == 0:
                lits02 = lits02 + [true_lit]
            model.AddBoolXOr(lits02)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = seed
    t0 = time.time()
    status = solver.Solve(model)
    elapsed = time.time() - t0
    names = {
        cp_model.OPTIMAL: "OPTIMAL",
        cp_model.FEASIBLE: "FEASIBLE",
        cp_model.INFEASIBLE: "INFEASIBLE",
        cp_model.MODEL_INVALID: "MODEL_INVALID",
        cp_model.UNKNOWN: "UNKNOWN",
    }
    status_name = names.get(status, str(status))
    out = {
        "status": status_name,
        "elapsed_sec": elapsed,
        "budget_c10_c01_c11": list(budget),
        "solver_num_conflicts": solver.NumConflicts(),
        "solver_num_branches": solver.NumBranches(),
        "solver_wall_time": solver.WallTime(),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        mats = []
        for h, r in enumerate(ranks):
            Uvals = [[int(solver.Value(U[h][i][k])) for k in range(r)] for i in range(n)]
            Vvals = [[int(solver.Value(V[h][j][k])) for k in range(r)] for j in range(n)]
            X = reconstruct_matrix(Uvals, Vvals)
            mats.append(X)
        W, X1, X2 = mats
        ok1 = np.array_equal((W + X1) % 2, M1)
        ok2 = np.array_equal((W + X2) % 2, M2)
        direct = {
            "rank_W": int(mat_rank_f2(W)),
            "rank_M1_plus_W": int(mat_rank_f2((M1 + W) % 2)),
            "rank_M2_plus_W": int(mat_rank_f2((M2 + W) % 2)),
            "factor_equation_X0_plus_X1_eq_M1": bool(ok1),
            "factor_equation_X0_plus_X2_eq_M2": bool(ok2),
            "direct_original_rank_inequalities_pass": bool(mat_rank_f2(W) <= c11 and mat_rank_f2((M1 + W) % 2) <= c10 and mat_rank_f2((M2 + W) % 2) <= c01),
            "W_row_masks": row_masks(W),
        }
        out["witness"] = direct
    return out


def parse_line(s: str) -> Tuple[int,int,int]:
    vals = [int(x) for x in s.replace(',', ' ').split()]
    if len(vals) != 3:
        raise argparse.ArgumentTypeError("line must have three integers")
    return tuple(vals)  # type: ignore


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--line", type=parse_line, default=(42,87,125), help="dual line q1,q2,q3 as '42,87,125'")
    ap.add_argument("--budgets", nargs="*", default=["4,5,5", "5,4,5", "5,5,4"], help="budgets c10,c01,c11")
    ap.add_argument("--time", type=float, default=30.0)
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()

    T = build_matmul_tensor_f2()[1:,:,:].astype(np.uint8) % 2
    q1,q2,q3 = args.line
    M1 = contraction_matrix(T, q1)
    M2 = contraction_matrix(T, q2)
    M3 = contraction_matrix(T, q3)
    budgets = []
    for bs in args.budgets:
        budgets.append(tuple(int(x) for x in bs.replace(',', ' ').split()))
    OUTDIR.mkdir(parents=True, exist_ok=True)
    results = []
    for b in budgets:
        print(f"Solving line={args.line} budget={b} time={args.time}s")
        rec = solve_pencil_factor(M1, M2, b, time_limit=args.time)
        rec["line"] = list(args.line)
        rec["contraction_ranks"] = [int(mat_rank_f2(M1)), int(mat_rank_f2(M2)), int(mat_rank_f2(M3))]
        results.append(rec)
        print(json.dumps({"budget": b, "status": rec["status"], "witness": rec.get("witness")}, indent=2, sort_keys=True)[:4000])
    out = {"schema": "pencil_factor_cpsat_v1", "line": list(args.line), "results": results}
    out_path = args.out or OUTDIR / f"pencil_factor_cpsat_line_{q1}_{q2}_{q3}.json"
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(f"Saved {out_path}")


if __name__ == "__main__":
    main()
