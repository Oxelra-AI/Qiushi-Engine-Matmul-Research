#!/usr/bin/env python3
"""Local exact-rank tests for dim-6 E11 quotient rows (2-slice pencils).

For a quotient subspace U <= F2^8 of dim 6, the quotient tensor has first-mode
annihilator A=U^perp of dimension 2.  For lambda in A the contraction slice is
M_lambda = Lambda(lambda)^T \otimes I_3, a 9x9 matrix.  Thus the quotient tensor
is a 2 x 9 x 9 matrix pencil.

This script builds an exact Boolean SAT encoding for rank <= R of such a pencil:
  M0_ij = XOR_t alpha_t * x_ti * y_tj
  M1_ij = XOR_t beta_t  * x_ti * y_tj
with variables over F2.  SAT for R=LB validates that the Wang lower bound is
sharp for that row; UNSAT for R=LB would locally tighten the Wang cap.

This is a sampling/validation tool, not a global proof unless every relevant row
is covered with certified UNSAT/SAT witnesses or a theorem.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import numpy as np

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = Path("data/pencil_rank")
MASK9 = (1 << 9) - 1


def contains_e11(key: int) -> bool:
    d = key & 0xF
    return d > 0 and (((key >> (4 + 9 * (d - 1))) & MASK9) == 1)


def key9_to_basis8(key9: int) -> Tuple[int, ...]:
    raw = []
    for b in unpack_basis(key9):
        if b == 1:
            continue
        q = int(b)
        if q & 1:
            q ^= 1
        q8 = 0
        for bit in range(1, 9):
            if (q >> bit) & 1:
                q8 |= 1 << (bit - 1)
        if q8:
            raw.append(q8)
    return tuple(rref_basis(raw, n=8)) if raw else tuple()


def dot(a: int, b: int) -> int:
    return (a & b).bit_count() & 1


def annihilator_basis(basis8: Tuple[int, ...]) -> Tuple[int, ...]:
    vecs = [x for x in range(1, 256) if all(dot(x, u) == 0 for u in basis8)]
    piv = [0] * 8
    out = []
    for x in vecs:
        v = x
        for p in range(7, -1, -1):
            if (v >> p) & 1:
                if piv[p]:
                    v ^= piv[p]
                else:
                    piv[p] = v
                    out.append(v)
                    break
    return tuple(rref_basis(out, n=8))


def gf2_rank_matrix(M: np.ndarray) -> int:
    A = (M.copy() & 1).astype(np.uint8)
    r = 0
    m, n = A.shape
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i, c]:
                piv = i; break
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
    return r


def lambda_matrix(lam: int) -> np.ndarray:
    L = np.zeros((3, 3), dtype=np.uint8)
    for a in range(1, 9):
        if (lam >> (a - 1)) & 1:
            i, j = divmod(a, 3)
            L[i, j] = 1
    return L


def contraction_matrix(lam: int) -> np.ndarray:
    L = lambda_matrix(lam)
    return np.kron(L.T, np.eye(3, dtype=np.uint8)).astype(np.uint8)


class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses: List[List[int]] = []
    def var(self) -> int:
        self.nv += 1
        return self.nv
    def add(self, lits: Iterable[int]):
        self.clauses.append(list(lits))
    def unit(self, lit: int):
        self.clauses.append([lit])
    def add_and(self, z: int, x: int, y: int):
        # z <-> x & y
        self.add([-x, -y, z])
        self.add([x, -z])
        self.add([y, -z])
    def xor2(self, z: int, x: int, y: int):
        # z <-> x xor y
        self.add([-x, -y, -z])
        self.add([-x, y, z])
        self.add([x, -y, z])
        self.add([x, y, -z])
    def require_xor(self, xs: List[int], val: int):
        if not xs:
            if val:
                self.add([])
            return
        if len(xs) == 1:
            self.unit(xs[0] if val else -xs[0])
            return
        acc = xs[0]
        for x in xs[1:]:
            z = self.var()
            self.xor2(z, acc, x)
            acc = z
        self.unit(acc if val else -acc)
    def write(self, path: Path):
        with open(path, "w") as f:
            f.write(f"p cnf {self.nv} {len(self.clauses)}\n")
            for cl in self.clauses:
                f.write(" ".join(map(str, cl)) + " 0\n")


def build_rank_cnf(M0: np.ndarray, M1: np.ndarray, R: int, path: Path) -> Dict[str, int]:
    cnf = CNF()
    alpha = [cnf.var() for _ in range(R)]
    beta = [cnf.var() for _ in range(R)]
    x = [[cnf.var() for _ in range(9)] for _ in range(R)]
    y = [[cnf.var() for _ in range(9)] for _ in range(R)]
    ax_terms = [[[] for _ in range(9)] for _ in range(9)]
    bx_terms = [[[] for _ in range(9)] for _ in range(9)]
    for t in range(R):
        for i in range(9):
            for j in range(9):
                xy = cnf.var(); cnf.add_and(xy, x[t][i], y[t][j])
                axy = cnf.var(); cnf.add_and(axy, alpha[t], xy)
                bxy = cnf.var(); cnf.add_and(bxy, beta[t], xy)
                ax_terms[i][j].append(axy)
                bx_terms[i][j].append(bxy)
    for i in range(9):
        for j in range(9):
            cnf.require_xor(ax_terms[i][j], int(M0[i, j]))
            cnf.require_xor(bx_terms[i][j], int(M1[i, j]))
    cnf.write(path)
    return {"vars": cnf.nv, "clauses": len(cnf.clauses)}


def run_cadical(cnf_path: Path, timeout: float) -> Tuple[str, float, str]:
    t0 = time.time()
    try:
        p = subprocess.run(["cadical", "-q", str(cnf_path)], capture_output=True, text=True, timeout=timeout)
        elapsed = time.time() - t0
        out = (p.stdout or "") + (p.stderr or "")
        if p.returncode == 10:
            return "SAT", elapsed, out[-2000:]
        if p.returncode == 20:
            return "UNSAT", elapsed, out[-2000:]
        return f"UNKNOWN_{p.returncode}", elapsed, out[-2000:]
    except subprocess.TimeoutExpired as e:
        elapsed = time.time() - t0
        return "TIMEOUT", elapsed, ((e.stdout or "") + (e.stderr or ""))[-2000:] if isinstance(e.stdout, str) else ""


def select_rows(lut, lb_values: List[int], max_rows_per_lb: int):
    selected = []
    counts = Counter()
    totals = Counter()
    for key, lb in lut.items():
        if not contains_e11(int(key)):
            continue
        dim8 = (int(key) & 0xF) - 1
        if dim8 != 6:
            continue
        totals[int(lb)] += 1
        if int(lb) in lb_values and counts[int(lb)] < max_rows_per_lb:
            b8 = key9_to_basis8(int(key))
            ann = annihilator_basis(b8)
            selected.append({"key9": int(key), "lb": int(lb), "basis8": b8, "annihilator": ann})
            counts[int(lb)] += 1
    return selected, totals


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lb", default="12,14", help="comma-separated LB values among dim8=6 rows")
    ap.add_argument("--rows-per-lb", type=int, default=5)
    ap.add_argument("--rank", type=int, default=-1, help="rank bound; default equals row LB")
    ap.add_argument("--timeout", type=float, default=10.0)
    ap.add_argument("--outdir", type=Path, default=OUTDIR)
    ap.add_argument("--keep-cnf", action="store_true")
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    lb_values = [int(x) for x in args.lb.split(',') if x]

    t0 = time.time()
    lut, _ = load_lut(LUT_PATH)
    rows, totals = select_rows(lut, lb_values, args.rows_per_lb)
    results = []
    print(f"dim8=6 totals by LB: {dict(sorted(totals.items()))}")
    print(f"selected {len(rows)} rows")

    for idx, row in enumerate(rows):
        ann = row["annihilator"]
        assert len(ann) == 2
        M0 = contraction_matrix(ann[0])
        M1 = contraction_matrix(ann[1])
        R = row["lb"] if args.rank < 0 else args.rank
        cnf_path = args.outdir / f"pencil_idx{idx:03d}_lb{row['lb']}_r{R}.cnf"
        meta = build_rank_cnf(M0, M1, R, cnf_path)
        status, solve_sec, tail = run_cadical(cnf_path, args.timeout)
        if not args.keep_cnf:
            try:
                cnf_path.unlink()
            except FileNotFoundError:
                pass
        rec = {
            "idx": idx,
            "key9": row["key9"],
            "lb": row["lb"],
            "rank_tested": R,
            "basis8": list(map(int, row["basis8"])),
            "annihilator": list(map(int, ann)),
            "lambda_ranks": [gf2_rank_matrix(lambda_matrix(ann[0])), gf2_rank_matrix(lambda_matrix(ann[1]))],
            "slice_matrix_ranks": [gf2_rank_matrix(M0), gf2_rank_matrix(M1)],
            "status": status,
            "solve_sec": round(solve_sec, 3),
            "cnf_vars": meta["vars"],
            "cnf_clauses": meta["clauses"],
            "solver_tail": tail,
        }
        results.append(rec)
        print(json.dumps({k: rec[k] for k in ["idx","lb","rank_tested","annihilator","lambda_ranks","status","solve_sec","cnf_vars","cnf_clauses"]}, sort_keys=True))

    out = {
        "status": "ok",
        "purpose": "sample exact SAT rank tests for dim8=6 E11 quotient pencils",
        "elapsed_sec": time.time() - t0,
        "dim8_6_totals_by_lb": dict(sorted((int(k), int(v)) for k, v in totals.items())),
        "lb_values_selected": lb_values,
        "rows_per_lb": args.rows_per_lb,
        "solver_timeout_sec": args.timeout,
        "status_hist": dict(sorted(Counter(r["status"] for r in results).items())),
        "results": results,
    }
    outpath = args.outdir / "pencil_rank_sample.json"
    outpath.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(f"Saved {outpath}")

if __name__ == "__main__":
    main()
