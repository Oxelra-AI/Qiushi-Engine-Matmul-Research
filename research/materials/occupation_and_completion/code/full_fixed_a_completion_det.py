#!/usr/bin/env python3
"""Fixed-A Brent SAT with tight-contraction inverse/determination constraints.

Equality case used: if a tight contraction has
    M = sum_{j=1..r} b_j c_j^T,   r = rank(M) = number of active terms,
then B=[b_j] has full column rank r.  For any left inverse L with L B = I_r,
    C^T = L M,
so every active C factor is a fixed linear image of L.  This remains useful
when r=9, where nullspace constraints are vacuous.

The constraints are redundant for any exact decomposition but expose the rigid
rank-equality structure to a SAT solver.  Optionally also add the symmetric
right-side version using a left inverse of C and B^T = R M^T.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import List, Sequence

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))

from pivot_fixed_full_wang import parse_multiset_arg  # type: ignore
from full_fixed_a_completion_tight import (  # type: ignore
    CNF,
    build_t333,
    lambda_matrix,
    mat_rank,
    parse_solver_solution,
    verify,
)


def tight_contractions(A: Sequence[int], T):
    out = []
    for lam in range(1, 512):
        active = [t for t, a in enumerate(A) if ((int(lam) & int(a)).bit_count() & 1)]
        M = lambda_matrix(T, lam)
        r = mat_rank(M)
        if r > 0 and len(active) == r:
            out.append({"lambda": int(lam), "rank": int(r), "active_terms": active, "M": M})
    return out


def add_inverse_det_B_to_C(F: CNF, V: List[List[int]], W: List[List[int]], tight: List[dict]) -> dict:
    """For each tight M=B C^T, add L B=I and C^T=L M."""
    inv_vars = 0
    prod_vars = 0
    inv_eqs = 0
    det_eqs = 0
    by_rank = Counter()
    for rec in tight:
        active = rec["active_terms"]
        M = rec["M"]
        r = int(rec["rank"])
        # L[j][i], j indexes active term row, i indexes ambient B coordinate.
        L = [[F.new_var() for _ in range(9)] for _ in range(r)]
        inv_vars += r * 9
        for j in range(r):
            for kk, t in enumerate(active):
                zs = []
                for i in range(9):
                    z = F.new_var()
                    prod_vars += 1
                    F.add_and2(z, L[j][i], V[t][i])
                    zs.append(z)
                F.add_xor_eq(zs, 1 if j == kk else 0)
                inv_eqs += 1
        for j, t in enumerate(active):
            for c in range(9):
                xs = [W[t][c]]
                for i in range(9):
                    if int(M[i, c]) & 1:
                        xs.append(L[j][i])
                F.add_xor_eq(xs, 0)
                det_eqs += 1
        by_rank[r] += 1
    return {
        "B_to_C_tight_constraints": len(tight),
        "B_to_C_by_rank": dict(sorted((int(k), int(v)) for k, v in by_rank.items())),
        "B_to_C_inverse_vars": int(inv_vars),
        "B_to_C_product_vars": int(prod_vars),
        "B_to_C_inverse_equations": int(inv_eqs),
        "B_to_C_determination_equations": int(det_eqs),
    }


def add_inverse_det_C_to_B(F: CNF, V: List[List[int]], W: List[List[int]], tight: List[dict]) -> dict:
    """Symmetric constraints: R C=I and B^T=R M^T."""
    inv_vars = 0
    prod_vars = 0
    inv_eqs = 0
    det_eqs = 0
    by_rank = Counter()
    for rec in tight:
        active = rec["active_terms"]
        M = rec["M"]
        r = int(rec["rank"])
        R = [[F.new_var() for _ in range(9)] for _ in range(r)]
        inv_vars += r * 9
        for j in range(r):
            for kk, t in enumerate(active):
                zs = []
                for c in range(9):
                    z = F.new_var()
                    prod_vars += 1
                    F.add_and2(z, R[j][c], W[t][c])
                    zs.append(z)
                F.add_xor_eq(zs, 1 if j == kk else 0)
                inv_eqs += 1
        for j, t in enumerate(active):
            for b in range(9):
                xs = [V[t][b]]
                for c in range(9):
                    if int(M[b, c]) & 1:
                        xs.append(R[j][c])
                F.add_xor_eq(xs, 0)
                det_eqs += 1
        by_rank[r] += 1
    return {
        "C_to_B_tight_constraints": len(tight),
        "C_to_B_by_rank": dict(sorted((int(k), int(v)) for k, v in by_rank.items())),
        "C_to_B_inverse_vars": int(inv_vars),
        "C_to_B_product_vars": int(prod_vars),
        "C_to_B_inverse_equations": int(inv_eqs),
        "C_to_B_determination_equations": int(det_eqs),
    }


def encode(A: Sequence[int], cnf_path: Path, mode: str) -> dict:
    T = build_t333()
    r = len(A)
    F = CNF()
    V = [[F.new_var() for _ in range(9)] for _ in range(r)]
    W = [[F.new_var() for _ in range(9)] for _ in range(r)]
    P = [[[F.new_var() for _ in range(9)] for _ in range(9)] for _ in range(r)]
    for t in range(r):
        for b in range(9):
            for c in range(9):
                F.add_and2(P[t][b][c], V[t][b], W[t][c])
    xor_terms = 0
    for s in range(9):
        active = [t for t, a in enumerate(A) if (int(a) >> s) & 1]
        for b in range(9):
            for c in range(9):
                xs = [P[t][b][c] for t in active]
                xor_terms += len(xs)
                F.add_xor_eq(xs, int(T[s, b, c]))
    tight = tight_contractions(A, T)
    extras = {}
    if mode in ("b2c", "both"):
        extras.update(add_inverse_det_B_to_C(F, V, W, tight))
    if mode in ("c2b", "both"):
        extras.update(add_inverse_det_C_to_B(F, V, W, tight))
    tight_hist = Counter(rec["rank"] for rec in tight)
    cnf_path.parent.mkdir(parents=True, exist_ok=True)
    F.write(cnf_path, comments=[
        f"full T333 fixed-A rank={r} inverse-determination mode={mode}",
        "A_multiset=" + ",".join(map(str, A))[:1000],
        "tight_rank_hist=" + json.dumps(dict(sorted((int(k), int(v)) for k, v in tight_hist.items())), sort_keys=True),
    ])
    return {
        "rank": r,
        "cnf_vars": F.nv,
        "cnf_clauses": len(F.clauses),
        "base_vw_vars": 2 * r * 9,
        "product_vars": r * 81,
        "xor_terms_total": int(xor_terms),
        "cnf_path": str(cnf_path),
        "mode": mode,
        "tight_lambda_count": len(tight),
        "tight_rank_hist": dict(sorted((int(k), int(v)) for k, v in tight_hist.items())),
        **extras,
    }


def run_solver(cnf: Path, solver: str, timeout: int):
    if solver == "cadical":
        cmd = ["cadical", str(cnf)]
    elif solver == "kissat":
        cmd = ["kissat", str(cnf)]
    elif solver == "cryptominisat5":
        cmd = ["cryptominisat5", str(cnf)]
    else:
        cmd = [solver, str(cnf)]
    t0 = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 20)
    return proc, time.time() - t0, cmd


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--multiset", required=True)
    ap.add_argument("--outdir", type=Path, required=True)
    ap.add_argument("--name", default="fixedA_det")
    ap.add_argument("--mode", choices=["b2c", "c2b", "both"], default="b2c")
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--solver", choices=["cadical", "kissat", "cryptominisat5"], default="cadical")
    args = ap.parse_args()
    A = parse_multiset_arg(args.multiset)
    args.outdir.mkdir(parents=True, exist_ok=True)
    cnf = args.outdir / (args.name + ".cnf")
    info = encode(A, cnf, args.mode)
    proc, elapsed, cmd = run_solver(cnf, args.solver, args.timeout)
    sat = None
    if proc.returncode == 10:
        sat = True
    elif proc.returncode == 20:
        sat = False
    rec = {
        "schema": "full_fixed_a_completion_det_v1",
        "A_multiset": [int(x) for x in A],
        "A_size": len(A),
        "encoding": info,
        "solver": args.solver,
        "solver_command": cmd,
        "returncode": int(proc.returncode),
        "sat": sat,
        "elapsed_sec": elapsed,
        "stdout_tail": "\n".join(proc.stdout.splitlines()[-80:]),
        "stderr_tail": "\n".join(proc.stderr.splitlines()[-80:]),
    }
    if sat is True:
        sol = parse_solver_solution(proc.stdout, len(A))
        if sol is not None:
            B, C = sol
            diff = verify(A, B, C)
            rec["verification_diff"] = diff
            rec["B_masks"] = [int(x) for x in B]
            rec["C_masks"] = [int(x) for x in C]
            if diff == 0:
                wit = args.outdir / (args.name + "_witness.json")
                wit.write_text(json.dumps({"terms": [[int(a), int(b), int(c)] for a, b, c in zip(A, B, C)], "rank": len(A), "verified": True}, indent=2, sort_keys=True) + "\n")
                rec["witness_path"] = str(wit)
    out = args.outdir / (args.name + "_result.json")
    out.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "sat": sat,
        "returncode": proc.returncode,
        "elapsed_sec": elapsed,
        "solver": args.solver,
        "mode": args.mode,
        "vars": info["cnf_vars"],
        "clauses": info["cnf_clauses"],
        "tight_lambda_count": info["tight_lambda_count"],
        "tight_rank_hist": info["tight_rank_hist"],
        "verification_diff": rec.get("verification_diff"),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
