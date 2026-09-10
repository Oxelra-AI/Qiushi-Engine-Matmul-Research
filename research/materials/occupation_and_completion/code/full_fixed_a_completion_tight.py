#!/usr/bin/env python3
"""Fixed-A Brent SAT with tight-contraction factor-rigidity constraints.

For a fixed full A-multiset, the usual Brent equations introduce B_t,C_t
and products P_tbc = B_tb & C_tc.  This variant adds SAT-visible necessary
conditions coming from equality in rank subadditivity for every tight
contraction lambda:

    M_lambda = sum_{lambda(a_t)=1} B_t C_t^T,  |active(lambda)| = rank(M_lambda)=r.

Then the active B factors are linearly independent in col(M_lambda), and the
active C factors are linearly independent in row(M_lambda).  We encode:
  * left-null membership: n.B_t = 0 for n^T M_lambda = 0;
  * right-null membership: m.C_t = 0 for M_lambda m = 0;
  * subset nonzero constraints: for every nonempty J in active terms,
        XOR_{t in J} B_t != 0, and similarly for C.

These constraints are redundant for exact decompositions but can greatly
improve propagation in hard fixed-A completion instances, especially when all
basic independent-verification-record X_t equations are vacuous at rank 9.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

import numpy as np

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from pivot_fixed_full_wang import parse_multiset_arg  # type: ignore
from quotient_tight_trace_filter import mat_rank  # type: ignore


def build_t333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1
    return T


def lambda_matrix(T: np.ndarray, lam: int) -> np.ndarray:
    M = np.zeros((9, 9), dtype=np.uint8)
    for s in range(9):
        if (int(lam) >> s) & 1:
            M ^= T[s]
    return M


def gf2_left_nullspace(M: np.ndarray) -> Tuple[List[np.ndarray], int]:
    """Return vectors n with n^T M = 0, plus rank(M), over F2."""
    A = (M.copy().astype(np.uint8) & 1)
    rows, cols = A.shape
    aug = np.zeros((rows, cols + rows), dtype=np.uint8)
    aug[:, :cols] = A
    for i in range(rows):
        aug[i, cols + i] = 1
    rank = 0
    for c in range(cols):
        piv = None
        for r in range(rank, rows):
            if aug[r, c]:
                piv = r
                break
        if piv is None:
            continue
        if piv != rank:
            aug[[rank, piv]] = aug[[piv, rank]]
        for r in range(rows):
            if r != rank and aug[r, c]:
                aug[r] ^= aug[rank]
        rank += 1
    ns: List[np.ndarray] = []
    for r in range(rank, rows):
        if np.any(aug[r, :cols]):
            continue
        v = aug[r, cols:].copy()
        if np.any(v):
            ns.append(v)
    return ns, rank


class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses: List[List[int]] = []
        self.empty_clause_count = 0

    def new_var(self) -> int:
        self.nv += 1
        return self.nv

    def add(self, cl: Iterable[int]) -> None:
        c = [int(x) for x in cl]
        if not c:
            self.empty_clause_count += 1
        self.clauses.append(c)

    def add_and2(self, z: int, x: int, y: int) -> None:
        self.add([-z, x])
        self.add([-z, y])
        self.add([-x, -y, z])

    def add_xor2_def(self, a: int, b: int, c: int) -> None:
        # c = a xor b
        self.add([-a, -b, -c])
        self.add([a, b, -c])
        self.add([a, -b, c])
        self.add([-a, b, c])

    def add_xor_eq(self, xs: Sequence[int], rhs: int) -> None:
        xs = [int(x) for x in xs]
        rhs = int(rhs) & 1
        if not xs:
            if rhs:
                self.add([])
            return
        if len(xs) == 1:
            self.add([xs[0] if rhs else -xs[0]])
            return
        cur = xs[0]
        for x in xs[1:]:
            z = self.new_var()
            self.add_xor2_def(cur, x, z)
            cur = z
        self.add([cur if rhs else -cur])

    def xor_lit(self, xs: Sequence[int]) -> int:
        """Return a literal variable equal to XOR(xs), adding definition clauses."""
        xs = [int(x) for x in xs]
        if not xs:
            z = self.new_var()
            self.add([-z])
            return z
        if len(xs) == 1:
            return xs[0]
        cur = xs[0]
        for x in xs[1:]:
            z = self.new_var()
            self.add_xor2_def(cur, x, z)
            cur = z
        return cur

    def add_vector_xor_nonzero(self, vectors: Sequence[Sequence[int]]) -> None:
        """For same-length Boolean vectors, require their coordinatewise XOR nonzero."""
        width = len(vectors[0])
        lits = []
        for j in range(width):
            lits.append(self.xor_lit([vec[j] for vec in vectors]))
        self.add(lits)

    def write(self, path: Path, comments: Sequence[str] | None = None) -> None:
        with path.open("w") as f:
            if comments:
                for c in comments:
                    f.write("c " + str(c).replace("\n", " ") + "\n")
            f.write(f"p cnf {self.nv} {len(self.clauses)}\n")
            for cl in self.clauses:
                f.write(" ".join(map(str, cl)) + " 0\n")


def tight_contractions(A: Sequence[int], T: np.ndarray) -> List[dict]:
    out = []
    for lam in range(1, 512):
        active = [t for t, a in enumerate(A) if ((int(lam) & int(a)).bit_count() & 1)]
        M = lambda_matrix(T, lam)
        r = mat_rank(M)
        if r > 0 and len(active) == r:
            left_ns, r2 = gf2_left_nullspace(M)
            right_ns, r3 = gf2_left_nullspace(M.T)
            assert r2 == r3 == r
            out.append({
                "lambda": int(lam),
                "rank": int(r),
                "active_terms": active,
                "left_nullspace": left_ns,
                "right_nullspace": right_ns,
            })
    return out


def add_factor_rigidity(F: CNF, V: List[List[int]], W: List[List[int]], tight: List[dict]) -> dict:
    lin_eqs = 0
    nonzero_constraints = 0
    nonzero_by_rank = Counter()
    lin_by_rank = Counter()
    for rec in tight:
        active = rec["active_terms"]
        r = int(rec["rank"])
        # B_t in col(M): left null equations n . B_t = 0.
        for n_vec in rec["left_nullspace"]:
            idxs = [j for j in range(9) if int(n_vec[j]) & 1]
            for t in active:
                F.add_xor_eq([V[t][j] for j in idxs], 0)
                lin_eqs += 1
                lin_by_rank[r] += 1
        # C_t in row(M): right null equations m . C_t = 0.
        for m_vec in rec["right_nullspace"]:
            idxs = [j for j in range(9) if int(m_vec[j]) & 1]
            for t in active:
                F.add_xor_eq([W[t][j] for j in idxs], 0)
                lin_eqs += 1
                lin_by_rank[r] += 1
        # Independence: every nonempty subset XOR is nonzero, for B and C.
        # active length equals r.  Use bit masks over local active list.
        m = len(active)
        for mask in range(1, 1 << m):
            terms = [active[i] for i in range(m) if (mask >> i) & 1]
            F.add_vector_xor_nonzero([V[t] for t in terms])
            F.add_vector_xor_nonzero([W[t] for t in terms])
            nonzero_constraints += 2
            nonzero_by_rank[r] += 2
    return {
        "factor_nullspace_linear_equations": int(lin_eqs),
        "factor_nullspace_linear_equations_by_rank": dict(sorted((int(k), int(v)) for k, v in lin_by_rank.items())),
        "independence_nonzero_constraints": int(nonzero_constraints),
        "independence_nonzero_constraints_by_rank": dict(sorted((int(k), int(v)) for k, v in nonzero_by_rank.items())),
    }


def encode_fixed_a_tight(A: Sequence[int], cnf_path: Path, add_tight: bool = True) -> dict:
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
    tight_info = {
        "tight_lambda_count": len(tight),
        "tight_rank_hist": dict(sorted((int(k), int(v)) for k, v in Counter(rec["rank"] for rec in tight).items())),
        "tight_lambdas": [int(rec["lambda"]) for rec in tight],
    }
    extra = {}
    if add_tight:
        extra = add_factor_rigidity(F, V, W, tight)

    comments = [
        f"full T333 fixed-A over F2 rank={r}",
        "A_multiset=" + ",".join(map(str, A))[:1000],
        f"xor_terms_total={xor_terms}",
        f"tight_factor_rigidity={bool(add_tight)}",
        "tight_rank_hist=" + json.dumps(tight_info["tight_rank_hist"], sort_keys=True),
    ]
    cnf_path.parent.mkdir(parents=True, exist_ok=True)
    F.write(cnf_path, comments)
    info = {
        "rank": r,
        "cnf_vars": F.nv,
        "cnf_clauses": len(F.clauses),
        "empty_clause_count": F.empty_clause_count,
        "base_vw_vars": 2 * r * 9,
        "product_vars": r * 81,
        "xor_terms_total": xor_terms,
        "cnf_path": str(cnf_path),
        "tight_factor_rigidity": bool(add_tight),
        **tight_info,
        **extra,
    }
    return info


def parse_solver_solution(stdout: str, r: int):
    vals = {}
    for line in stdout.splitlines():
        if line.startswith("v "):
            for tok in line.split()[1:]:
                z = int(tok)
                if z:
                    vals[abs(z)] = z > 0
    if not vals:
        return None
    B, C = [], []
    for t in range(r):
        bmask = 0
        cmask = 0
        for b in range(9):
            if vals.get(1 + t * 9 + b, False):
                bmask |= 1 << b
        off = 9 * r
        for c in range(9):
            if vals.get(1 + off + t * 9 + c, False):
                cmask |= 1 << c
        B.append(bmask)
        C.append(cmask)
    return B, C


def verify(A: Sequence[int], B: Sequence[int], C: Sequence[int]) -> int:
    T = build_t333()
    R = np.zeros_like(T)
    for a, b, c in zip(A, B, C):
        for s in range(9):
            if not ((int(a) >> s) & 1):
                continue
            for i in range(9):
                if not ((int(b) >> i) & 1):
                    continue
                for j in range(9):
                    if (int(c) >> j) & 1:
                        R[s, i, j] ^= 1
    return int(np.sum(R ^ T))


def solve_with_solver(cnf: Path, solver: str, timeout: int):
    t0 = time.time()
    if solver == "cadical":
        cmd = ["cadical", str(cnf)]
    elif solver == "kissat":
        cmd = ["kissat", str(cnf)]
    elif solver == "cryptominisat5":
        cmd = ["cryptominisat5", str(cnf)]
    else:
        cmd = [solver, str(cnf)]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 15)
    return proc, time.time() - t0, cmd


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--multiset", required=True)
    ap.add_argument("--outdir", type=Path, required=True)
    ap.add_argument("--name", default="fixedA_tight")
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--solver", default="cadical", choices=["cadical", "kissat", "cryptominisat5"])
    ap.add_argument("--no-tight", action="store_true", help="emit the base Brent CNF only")
    args = ap.parse_args()

    A = parse_multiset_arg(args.multiset)
    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)
    cnf = outdir / (args.name + ".cnf")
    info = encode_fixed_a_tight(A, cnf, add_tight=not args.no_tight)
    proc, elapsed, cmd = solve_with_solver(cnf, args.solver, args.timeout)
    sat = None
    if proc.returncode == 10:
        sat = True
    elif proc.returncode == 20:
        sat = False
    rec = {
        "schema": "full_fixed_a_completion_tight_v1",
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
                wit = outdir / (args.name + "_witness.json")
                wit.write_text(json.dumps({"terms": [[int(a), int(b), int(c)] for a, b, c in zip(A, B, C)], "rank": len(A), "verified": True}, indent=2, sort_keys=True) + "\n")
                rec["witness_path"] = str(wit)
    out = outdir / (args.name + "_result.json")
    out.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "sat": sat,
        "returncode": proc.returncode,
        "elapsed_sec": elapsed,
        "solver": args.solver,
        "vars": info["cnf_vars"],
        "clauses": info["cnf_clauses"],
        "tight_lambda_count": info["tight_lambda_count"],
        "tight_rank_hist": info["tight_rank_hist"],
        "independence_nonzero_constraints": info.get("independence_nonzero_constraints", 0),
        "factor_nullspace_linear_equations": info.get("factor_nullspace_linear_equations", 0),
        "verification_diff": rec.get("verification_diff"),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
