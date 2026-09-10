#!/usr/bin/env python3
"""
analysis: diagonal-collapse test for cyclic-invariant rank-22 over F_2.

For a cyclic ansatz
    T = sum_i X_i^3 + sum_j (U_j,V_j,W_j cyclic orbit),
restrict to A=B=C=M.  In Boolean ANF over F_2, every cube term
ell_X(M)^3 reduces to the linear form ell_X(M), so the cube variables do
not affect the degree-2 or degree-3 diagonal terms.  Thus each skeleton
(f,m) has the necessary orbit-only condition
    high-degree part of sum_{j<=m} ell_Uj ell_Vj ell_Wj
      = high-degree part of tr(M^3),
with C(9,2)+C(9,3)=120 equations in 27m orbit variables.

This script verifies the ANF identity, checks that the degree-3 diagonal
constraints are exactly the 84-dimensional Sym^3 quotient constraints used
in analysis, and solves the 120-equation necessary condition for selected m.
UNSAT for a given m excludes all cyclic F_2 skeletons with that many free
3-orbits, regardless of the number of cube terms.
"""

from __future__ import annotations

import argparse
import itertools
import json
import os
import subprocess
import time
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / "data" / "diagonal_collapse"

N = 9


def idx(a: int, b: int) -> int:
    return 3 * a + b


def build_T333() -> List[List[List[int]]]:
    T = [[[0] * N for _ in range(N)] for _ in range(N)]
    for a in range(3):
        for b in range(3):
            for c in range(3):
                T[idx(a, b)][idx(b, c)][idx(c, a)] ^= 1
    return T


def trM3_anf() -> Dict[int, int]:
    """ANF of tr(M^3) as Boolean function, represented by bit masks."""
    coeff: Dict[int, int] = {}
    for a in range(3):
        for b in range(3):
            for c in range(3):
                mask = (1 << idx(a, b)) | (1 << idx(b, c)) | (1 << idx(c, a))
                coeff[mask] = coeff.get(mask, 0) ^ 1
                if coeff[mask] == 0:
                    del coeff[mask]
    return coeff


def mask_from_tuple(t: Sequence[int]) -> int:
    mask = 0
    for x in t:
        mask |= 1 << x
    return mask


def mask_vars(mask: int) -> Tuple[int, ...]:
    return tuple(i for i in range(N) if (mask >> i) & 1)


def degree(mask: int) -> int:
    return mask.bit_count()


def cyclic_orbit_reps(n: int = N) -> List[Tuple[int, int, int]]:
    seen = set()
    reps = []
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if (i, j, k) not in seen:
                    orb = set()
                    t = (i, j, k)
                    while t not in orb:
                        orb.add(t)
                        t = (t[1], t[2], t[0])
                    reps.append(min(orb))
                    seen |= orb
    reps.sort()
    return reps


def sym3_quotient_pairs(reps: Sequence[Tuple[int, int, int]]):
    """All-distinct cyclic orbit pairs modulo fully symmetric tensors."""
    seen = set()
    pairs = []
    for rep in reps:
        i, j, k = rep
        if i == j or j == k or i == k:
            continue
        trans_orb = [(j, i, k), (i, k, j), (k, j, i)]
        trans_rep = min(trans_orb)
        pair = (min(rep, trans_rep), max(rep, trans_rep))
        if pair not in seen:
            seen.add(pair)
            pairs.append(pair)
    pairs.sort()
    return pairs


def quotient_target(T, pairs):
    return [T[a[0]][a[1]][a[2]] ^ T[b[0]][b[1]][b[2]] for a, b in pairs]


class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses: List[Tuple[int, ...]] = []
        self.and_cache: Dict[Tuple[int, ...], int] = {}
        self.xor_cache: Dict[Tuple[int, int], int] = {}

    def new_var(self) -> int:
        self.nv += 1
        return self.nv

    def new_vars(self, n: int) -> List[int]:
        return [self.new_var() for _ in range(n)]

    def cl(self, *lits: int):
        self.clauses.append(tuple(lits))

    def AND2(self, a: int, b: int) -> int:
        if a == b:
            return a
        key = tuple(sorted((a, b)))
        if key in self.and_cache:
            return self.and_cache[key]
        p = self.new_var()
        self.cl(-a, -b, p)
        self.cl(a, -p)
        self.cl(b, -p)
        self.and_cache[key] = p
        return p

    def AND3(self, a: int, b: int, c: int) -> int:
        key = tuple(sorted((a, b, c)))
        if len(set(key)) == 1:
            return key[0]
        if key in self.and_cache:
            return self.and_cache[key]
        # Use cached AND2s so repeated products across equations are shared.
        p = self.AND2(key[0], key[1])
        q = self.AND2(p, key[2])
        self.and_cache[key] = q
        return q

    def XOR2(self, a: int, b: int) -> int:
        if a == b:
            # a xor a = 0.  Return a fresh forced-false variable for uniformity.
            z = self.new_var()
            self.cl(-z)
            return z
        key = tuple(sorted((a, b)))
        if key in self.xor_cache:
            return self.xor_cache[key]
        s = self.new_var()
        self.cl(-a, -b, -s)
        self.cl(a, b, -s)
        self.cl(a, -b, s)
        self.cl(-a, b, s)
        self.xor_cache[key] = s
        return s

    def assert_xor_eq(self, terms: Sequence[int], target: int):
        # Cancel duplicate term variables mod 2 before building a chain.
        parity: Dict[int, int] = {}
        for t in terms:
            parity[t] = parity.get(t, 0) ^ 1
            if parity[t] == 0:
                del parity[t]
        terms = sorted(parity)
        if not terms:
            if target:
                self.cl()  # empty clause
            return
        if len(terms) == 1:
            self.cl(terms[0] if target else -terms[0])
            return
        acc = terms[0]
        for t in terms[1:-1]:
            acc = self.XOR2(acc, t)
        last = terms[-1]
        if target:
            self.cl(acc, last)
            self.cl(-acc, -last)
        else:
            self.cl(acc, -last)
            self.cl(-acc, last)

    def add_lex_le(self, a: Sequence[int], b: Sequence[int]):
        """a <= b lex, used only as satisfiability-preserving symmetry breaking."""
        assert len(a) == len(b)
        eq = None
        for j in range(len(a)):
            if eq is None:
                self.cl(-a[j], b[j])
            else:
                self.cl(-eq, -a[j], b[j])
            if j < len(a) - 1:
                eqj = self.new_var()
                if eq is None:
                    self.cl(-eqj, -a[j], b[j])
                    self.cl(-eqj, a[j], -b[j])
                    self.cl(-a[j], -b[j], eqj)
                    self.cl(a[j], b[j], eqj)
                else:
                    self.cl(-eqj, eq)
                    self.cl(-eqj, -a[j], b[j])
                    self.cl(-eqj, a[j], -b[j])
                    self.cl(-eq, -a[j], -b[j], eqj)
                    self.cl(-eq, a[j], b[j], eqj)
                eq = eqj

    def write_dimacs(self, path: Path):
        with path.open("w") as f:
            f.write(f"p cnf {self.nv} {len(self.clauses)}\n")
            for c in self.clauses:
                f.write(" ".join(map(str, c)) + " 0\n")


def product_terms_for_mask(mask: int, U: Sequence[int], V: Sequence[int], W: Sequence[int], enc: CNF) -> List[int]:
    """Terms in the ANF coefficient of monomial `mask` for ell_U ell_V ell_W."""
    vars_ = mask_vars(mask)
    d = len(vars_)
    terms: List[int] = []
    if d == 2:
        p, q = vars_
        assignments = [
            (p, p, q), (p, q, p), (q, p, p),
            (q, q, p), (q, p, q), (p, q, q),
        ]
    elif d == 3:
        p, q, r = vars_
        assignments = list(itertools.permutations((p, q, r), 3))
    else:
        raise ValueError(f"degree {d} not supported for high-degree mask")
    for a, b, c in assignments:
        terms.append(enc.AND3(U[a], V[b], W[c]))
    return terms


def encode_diagonal(m: int, targets: Dict[int, int], sym_break: bool = True) -> Tuple[CNF, dict]:
    enc = CNF()
    U = [enc.new_vars(N) for _ in range(m)]
    V = [enc.new_vars(N) for _ in range(m)]
    W = [enc.new_vars(N) for _ in range(m)]
    if sym_break:
        # Diagonal product ell_U ell_V ell_W is S_3-invariant in U,V,W,
        # and the m products are permutable.  These breakers preserve SAT/UNSAT
        # for the diagonal-only necessary condition.
        for o in range(m):
            enc.add_lex_le(U[o], V[o])
            enc.add_lex_le(V[o], W[o])
        for o in range(m - 1):
            enc.add_lex_le(U[o] + V[o] + W[o], U[o + 1] + V[o + 1] + W[o + 1])
    high_masks = sorted([mask for mask in targets if degree(mask) in (2, 3)])
    for mask in high_masks:
        terms: List[int] = []
        for o in range(m):
            terms.extend(product_terms_for_mask(mask, U[o], V[o], W[o], enc))
        enc.assert_xor_eq(terms, targets.get(mask, 0))
    return enc, {"U": U, "V": V, "W": W, "high_masks": high_masks}


def run_solver(cnf: Path, proof: Path | None = None, solver: str = "kissat", timeout: int = 300):
    cmd = [solver, str(cnf)]
    if proof is not None and solver in {"kissat", "cadical"}:
        cmd.append(str(proof))
    t0 = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"status": "TIMEOUT", "time_sec": time.time() - t0, "returncode": None, "stdout_tail": "", "stderr_tail": ""}
    out = r.stdout + r.stderr
    if r.returncode == 10 or "s SATISFIABLE" in out:
        status = "SAT"
    elif r.returncode == 20 or "s UNSATISFIABLE" in out:
        status = "UNSAT"
    else:
        status = "UNKNOWN"
    return {
        "status": status,
        "time_sec": time.time() - t0,
        "returncode": r.returncode,
        "stdout_tail": r.stdout[-4000:],
        "stderr_tail": r.stderr[-4000:],
    }


def verify_drat(cnf: Path, proof: Path, timeout: int = 300):
    if not proof.exists() or proof.stat().st_size == 0:
        return {"status": "NO_PROOF", "time_sec": 0.0, "proof_bytes": 0}
    t0 = time.time()
    try:
        r = subprocess.run(["drat-trim", str(cnf), str(proof)], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"status": "TIMEOUT", "time_sec": time.time() - t0, "proof_bytes": proof.stat().st_size}
    out = r.stdout + r.stderr
    status = "VERIFIED" if "VERIFIED" in out else "UNVERIFIED"
    return {
        "status": status,
        "time_sec": time.time() - t0,
        "proof_bytes": proof.stat().st_size,
        "output_tail": out[-4000:],
    }


def parse_model(stdout: str) -> List[int]:
    vals = []
    for line in stdout.splitlines():
        if line.startswith("v "):
            for tok in line[2:].split():
                lit = int(tok)
                if lit:
                    vals.append(lit)
    return vals


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-m", type=int, default=7)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--solver", default="kissat")
    ap.add_argument("--no-sym-break", action="store_true")
    ap.add_argument("--proof", action="store_true", help="request DRAT proof for UNSAT-capable solver")
    args = ap.parse_args()

    DATA_DIR.mkdir(parents=True, exist_ok=True)
    T = build_T333()
    reps = cyclic_orbit_reps()
    pairs = sym3_quotient_pairs(reps)
    q = quotient_target(T, pairs)
    anf = trM3_anf()

    degree_counts = {d: sum(1 for mask in anf if degree(mask) == d) for d in range(4)}
    high_targets = {mask: (anf.get(mask, 0) & 1) for d in (2, 3) for mask in (mask_from_tuple(s) for s in itertools.combinations(range(N), d))}
    high_targets = {mask: v for mask, v in high_targets.items()}  # keep zeros too
    deg3_masks = [mask_from_tuple(s) for s in itertools.combinations(range(N), 3)]
    deg2_masks = [mask_from_tuple(s) for s in itertools.combinations(range(N), 2)]
    deg3_target = [anf.get(mask, 0) for mask in deg3_masks]
    # Pair order is not the same as combinations; match by support set.
    q_by_mask = {mask_from_tuple(pairs[i][0]): q[i] for i in range(len(pairs))}
    # pairs[i][0] and pairs[i][1] have same variable support.
    quotient_matches_degree3 = all(q_by_mask[mask] == anf.get(mask, 0) for mask in deg3_masks)

    structural = {
        "trM3_degree_counts": degree_counts,
        "linear_masks": [mask_vars(mask) for mask in sorted(anf) if degree(mask) == 1],
        "degree2_nonzero_count": sum(anf.get(mask, 0) for mask in deg2_masks),
        "degree3_nonzero_count": sum(anf.get(mask, 0) for mask in deg3_masks),
        "degree3_nonzero_masks": [mask_vars(mask) for mask in deg3_masks if anf.get(mask, 0)],
        "sym3_quotient_dim": len(pairs),
        "sym3_quotient_hamming_weight": sum(q),
        "degree3_equals_sym3_quotient": quotient_matches_degree3,
        "equation_count_degree2": len(deg2_masks),
        "equation_count_degree3": len(deg3_masks),
        "equation_count_high": len(deg2_masks) + len(deg3_masks),
        "note": "The 84 degree-3 diagonal equations are exactly the analysis E_inv/Sym^3 quotient equations over F2; the additional diagonal-collapse information is the 36 zero degree-2 equations. Linear terms can be supplied by cube terms whenever f>=1.",
    }

    results = []
    print(json.dumps(structural, indent=2))
    for m in range(args.max_m + 1):
        print("=" * 72)
        print(f"m={m}: encoding 120 high-degree diagonal equations in {27*m} primary orbit variables")
        enc, vmap = encode_diagonal(m, high_targets, sym_break=not args.no_sym_break)
        cnf = DATA_DIR / f"diag_highdeg_m{m}.cnf"
        proof = DATA_DIR / f"diag_highdeg_m{m}.drat" if args.proof else None
        enc.write_dimacs(cnf)
        print(f"  CNF {enc.nv} vars, {len(enc.clauses)} clauses; gates={len(enc.and_cache)} AND cache, xors={len(enc.xor_cache)}")
        sol = run_solver(cnf, proof=proof, solver=args.solver, timeout=args.timeout)
        print(f"  {sol['status']} in {sol['time_sec']:.3f}s")
        rec = {
            "m": m,
            "primary_vars": 27 * m,
            "total_vars": enc.nv,
            "clauses": len(enc.clauses),
            "solver": args.solver,
            "timeout": args.timeout,
            "status": sol["status"],
            "solve_sec": round(sol["time_sec"], 6),
            "returncode": sol["returncode"],
            "cnf": str(cnf),
        }
        if sol["status"] == "UNSAT" and proof is not None:
            dv = verify_drat(cnf, proof)
            print(f"  DRAT {dv['status']} proof_bytes={dv.get('proof_bytes', 0)} verify_sec={dv['time_sec']:.3f}")
            rec["drat"] = dv
        elif sol["status"] == "SAT":
            rec["stdout_tail"] = sol["stdout_tail"]
        results.append(rec)

    out = DATA_DIR / "diagonal_collapse_results.json"
    out.write_text(json.dumps({"structural": structural, "results": results}, indent=2) + "\n")
    print("=" * 72)
    print(f"Saved {out}")


if __name__ == "__main__":
    main()
