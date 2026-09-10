#!/usr/bin/env python3
"""Exact E11 prefix-completion SAT over F2 with variable remaining A factors.

Given a prefix of nonzero quotient A masks p_0,...,p_{k-1}, ask whether the
8x9x9 E11 core has a rank-r CPD whose first k A factors equal that prefix,
while all remaining A factors and all B/C factors are free:

    core[a,b,c] = XOR_t alpha[t,a] * beta[t,b] * gamma[t,c].

Because CPD summands are unordered, fixing the first k terms is equivalent to
asking for a decomposition whose A multiset contains the prefix.  Therefore an
UNSAT result for a prefix removes every canonical support subtree containing it
(up to the already verified E11 quotient symmetry, after canonicalizing the
prefix if desired).  A SAT result is decoded and verified as an exact E11 CPD;
for r=19 it lifts to a full F2 rank-22 T333 decomposition by the analysis +3 lift.

The default encoder uses CryptoMiniSat native XOR clauses for the Brent parity
equations.  A plain sequential-XOR CNF can also be emitted/solved for DRAT proof
production with ordinary SAT solvers.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import re
import subprocess
import time
from pathlib import Path

import numpy as np


def vec_from_mask(mask: int, n: int) -> np.ndarray:
    return np.array([(int(mask) >> i) & 1 for i in range(n)], dtype=np.uint8)


def verify(core: np.ndarray, us: list[int], vs: list[int], ws: list[int]) -> tuple[bool, int]:
    R = np.zeros_like(core, dtype=np.uint8)
    for u, v, w in zip(us, vs, ws):
        U = vec_from_mask(u, core.shape[0]).reshape(-1, 1, 1)
        V = vec_from_mask(v, core.shape[1]).reshape(1, -1, 1)
        W = vec_from_mask(w, core.shape[2]).reshape(1, 1, -1)
        R ^= (U * V * W).astype(np.uint8)
    diff = R ^ core
    return bool(not diff.any()), int(diff.sum())


def parse_model(stdout: str) -> list[int]:
    vals: list[int] = []
    for line in stdout.splitlines():
        if line.startswith("v"):
            for tok in line.split()[1:]:
                try:
                    z = int(tok)
                except ValueError:
                    continue
                if z:
                    vals.append(z)
    return vals


def sha256_file(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


class Encoder:
    def __init__(self, mode: str):
        if mode not in {"native", "plain"}:
            raise ValueError(mode)
        self.mode = mode
        self.next_var = 1
        self.cnf: list[list[int]] = []
        self.xors: list[tuple[list[int], int]] = []

    def new(self) -> int:
        v = self.next_var
        self.next_var += 1
        return v

    def add(self, lits) -> None:
        self.cnf.append([int(x) for x in lits])

    def add_and(self, z: int, a: int, b: int) -> None:
        # z = a & b
        self.add([-a, -b, z])
        self.add([a, -z])
        self.add([b, -z])

    def add_xor_plain(self, xs, rhs: int) -> None:
        xs = [int(x) for x in xs]
        rhs = int(rhs) & 1
        if not xs:
            if rhs:
                self.add([])
            return
        if len(xs) == 1:
            self.add([xs[0] if rhs else -xs[0]])
            return
        prev = xs[0]
        for i, curr in enumerate(xs[1:], start=1):
            if i < len(xs) - 1:
                z = self.new()
                # z = prev XOR curr
                self.add([-prev, -curr, -z])
                self.add([prev, curr, -z])
                self.add([prev, -curr, z])
                self.add([-prev, curr, z])
                prev = z
            else:
                # prev XOR curr = rhs
                if rhs:
                    self.add([-prev, -curr])
                    self.add([prev, curr])
                else:
                    self.add([-prev, curr])
                    self.add([prev, -curr])

    def add_xor(self, xs, rhs: int) -> None:
        xs = [int(x) for x in xs]
        rhs = int(rhs) & 1
        if self.mode == "plain":
            self.add_xor_plain(xs, rhs)
            return
        if not xs:
            if rhs:
                self.add([])
            return
        self.xors.append((xs, rhs))

    def write(self, path: Path, comments=None) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("w") as f:
            for c in comments or []:
                f.write("c " + str(c) + "\n")
            f.write(f"p cnf {self.next_var - 1} {len(self.cnf) + len(self.xors)}\n")
            if self.mode == "native":
                for lits, rhs in self.xors:
                    if not lits:
                        if rhs:
                            f.write("0\n")
                        continue
                    ll = list(lits)
                    # CryptoMiniSat native XOR line is true by default; flip one
                    # literal to encode even parity.
                    if rhs == 0:
                        ll[0] = -ll[0]
                    f.write("x " + " ".join(map(str, ll)) + " 0\n")
            for cl in self.cnf:
                f.write(" ".join(map(str, cl)) + " 0\n")


class PrefixCPD:
    def __init__(self, core: np.ndarray, rank: int, prefix: list[int], mode: str, allow_zero_a: bool = False, sort_free_a: bool = False):
        self.core = core.astype(np.uint8) & 1
        self.rank = int(rank)
        self.prefix = [int(x) for x in prefix]
        if len(self.prefix) > self.rank:
            raise ValueError("prefix longer than rank")
        self.nU, self.nV, self.nW = self.core.shape
        if any(x <= 0 or x >= (1 << self.nU) for x in self.prefix):
            raise ValueError(f"prefix masks must be in 1..{(1 << self.nU)-1}")
        self.F = Encoder(mode)
        self.alpha: dict[tuple[int, int], int] = {}
        self.vvar: dict[tuple[int, int], int] = {}
        self.wvar: dict[tuple[int, int], int] = {}
        self.pvar: dict[tuple[int, int, int], int] = {}
        self.qvar: dict[tuple[int, int, int, int], int] = {}
        self.allow_zero_a = allow_zero_a
        self.sort_free_a = sort_free_a
        self._build()

    def add_leq_bits(self, xs: list[int], ys: list[int]) -> None:
        """Add a compact CNF comparator for little-endian bit vectors xs <= ys."""
        if len(xs) != len(ys):
            raise ValueError("comparator bit vectors have unequal length")
        eq_prev: int | None = None  # None means the already processed high bits are certainly equal.
        for i in range(len(xs) - 1, -1, -1):
            x = xs[i]
            y = ys[i]
            if eq_prev is None:
                # If high bits are equal and this bit differs, forbid x_i=1,y_i=0.
                self.F.add([-x, y])
                if i > 0:
                    e = self.F.new()
                    # e <=> (x == y) for the high-prefix equality state.
                    self.F.add([-x, -y, e])       # x & y -> e
                    self.F.add([x, y, e])         # ~x & ~y -> e
                    self.F.add([-e, -x, y])       # e -> x -> y
                    self.F.add([-e, x, -y])       # e -> y -> x
                    eq_prev = e
            else:
                self.F.add([-eq_prev, -x, y])
                if i > 0:
                    e = self.F.new()
                    # e <=> eq_prev & (x == y), enough to propagate exact prefix equality.
                    self.F.add([-e, eq_prev])
                    self.F.add([-e, -x, y])
                    self.F.add([-e, x, -y])
                    self.F.add([-eq_prev, -x, -y, e])
                    self.F.add([-eq_prev, x, y, e])
                    eq_prev = e

    def _build(self) -> None:
        r = self.rank
        for t in range(r):
            for a in range(self.nU):
                self.alpha[(t, a)] = self.F.new()
            for b in range(self.nV):
                self.vvar[(t, b)] = self.F.new()
            for c in range(self.nW):
                self.wvar[(t, c)] = self.F.new()
        for t in range(r):
            for b in range(self.nV):
                for c in range(self.nW):
                    z = self.F.new()
                    self.pvar[(t, b, c)] = z
                    self.F.add_and(z, self.vvar[(t, b)], self.wvar[(t, c)])
        for t in range(r):
            for a in range(self.nU):
                for b in range(self.nV):
                    for c in range(self.nW):
                        z = self.F.new()
                        self.qvar[(t, a, b, c)] = z
                        self.F.add_and(z, self.alpha[(t, a)], self.pvar[(t, b, c)])
        # Fixed prefix terms.
        for t, u in enumerate(self.prefix):
            for a in range(self.nU):
                lit = self.alpha[(t, a)] if ((u >> a) & 1) else -self.alpha[(t, a)]
                self.F.add([lit])
        # Nonzero A factors for all free terms, matching the canonical support
        # search over points of F2^8 \ {0}.  Fixed prefix terms are already nonzero.
        if not self.allow_zero_a:
            for t in range(len(self.prefix), r):
                self.F.add([self.alpha[(t, a)] for a in range(self.nU)])
        # Remaining A terms are unordered. Sorting only the free suffix preserves
        # satisfiability of prefix containment while removing a large permutation
        # symmetry; the fixed prefix need not be numerically before the suffix.
        if getattr(self, "sort_free_a", False):
            for t in range(len(self.prefix), r - 1):
                self.add_leq_bits([self.alpha[(t, a)] for a in range(self.nU)], [self.alpha[(t + 1, a)] for a in range(self.nU)])
        # Brent parity equations.
        for a in range(self.nU):
            for b in range(self.nV):
                for c in range(self.nW):
                    self.F.add_xor([self.qvar[(t, a, b, c)] for t in range(r)], int(self.core[a, b, c]))

    @property
    def var_count(self) -> int:
        return self.F.next_var - 1

    @property
    def cnf_clause_count(self) -> int:
        return len(self.F.cnf)

    @property
    def xor_clause_count(self) -> int:
        return len(self.F.xors)

    def decode(self, model_lits: list[int]) -> tuple[list[int], list[int], list[int]]:
        pos = {int(x) for x in model_lits if int(x) > 0}
        us: list[int] = []
        vs: list[int] = []
        ws: list[int] = []
        for t in range(self.rank):
            um = 0
            vm = 0
            wm = 0
            for a in range(self.nU):
                if self.alpha[(t, a)] in pos:
                    um |= 1 << a
            for b in range(self.nV):
                if self.vvar[(t, b)] in pos:
                    vm |= 1 << b
            for c in range(self.nW):
                if self.wvar[(t, c)] in pos:
                    wm |= 1 << c
            us.append(um)
            vs.append(vm)
            ws.append(wm)
        return us, vs, ws

    def save_npz(self, path: Path, us: list[int], vs: list[int], ws: list[int]) -> None:
        U = np.zeros((self.rank, self.nU), dtype=np.uint8)
        V = np.zeros((self.rank, self.nV), dtype=np.uint8)
        W = np.zeros((self.rank, self.nW), dtype=np.uint8)
        for t, (u, v, w) in enumerate(zip(us, vs, ws)):
            U[t] = vec_from_mask(u, self.nU)
            V[t] = vec_from_mask(v, self.nV)
            W[t] = vec_from_mask(w, self.nW)
        path.parent.mkdir(parents=True, exist_ok=True)
        np.savez(path, U=U, V=V, W=W, u_masks=np.array(us, dtype=np.uint16), v_masks=np.array(vs, dtype=np.uint16), w_masks=np.array(ws, dtype=np.uint16))


def solve_native(cnf_path: Path, solver: str, timeout: int, threads: int, maxconfl: int) -> dict:
    cmd = [solver, "--verb", "0", "-t", str(threads), "--maxtime", str(timeout)]
    if maxconfl > 0:
        cmd += ["--maxconfl", str(maxconfl)]
    cmd.append(str(cnf_path))
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=timeout + 30)
        elapsed = time.time() - t0
        status = "UNKNOWN"
        if re.search(r"\bUNSATISFIABLE\b", proc.stdout):
            status = "UNSAT"
        elif re.search(r"\bSATISFIABLE\b", proc.stdout):
            status = "SAT"
        elif re.search(r"\bINDETERMINATE\b", proc.stdout):
            status = "UNKNOWN"
        return {
            "command": " ".join(cmd),
            "returncode": proc.returncode,
            "status": status,
            "elapsed_sec": elapsed,
            "stdout_tail": proc.stdout[-4000:],
            "stderr_tail": proc.stderr[-2000:],
            "model": parse_model(proc.stdout) if status == "SAT" else None,
        }
    except subprocess.TimeoutExpired as exc:
        return {
            "command": " ".join(cmd),
            "returncode": None,
            "status": "TIMEOUT",
            "elapsed_sec": time.time() - t0,
            "stdout_tail": (exc.stdout or "")[-4000:] if isinstance(exc.stdout, str) else "",
            "stderr_tail": (exc.stderr or "")[-2000:] if isinstance(exc.stderr, str) else "",
            "model": None,
        }


def solve_plain(cnf_path: Path, solver: str, timeout: int, proof_path: Path | None) -> dict:
    cmd = [solver, str(cnf_path)]
    if proof_path is not None:
        cmd.append(str(proof_path))
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=timeout)
        elapsed = time.time() - t0
        status = "UNKNOWN"
        if re.search(r"\bUNSATISFIABLE\b", proc.stdout) or proc.returncode == 20:
            status = "UNSAT"
        elif re.search(r"\bSATISFIABLE\b", proc.stdout) or proc.returncode == 10:
            status = "SAT"
        return {
            "command": " ".join(cmd),
            "returncode": proc.returncode,
            "status": status,
            "elapsed_sec": elapsed,
            "stdout_tail": proc.stdout[-4000:],
            "stderr_tail": proc.stderr[-2000:],
            "model": parse_model(proc.stdout) if status == "SAT" else None,
            "proof_path": str(proof_path) if proof_path is not None else None,
        }
    except subprocess.TimeoutExpired as exc:
        return {
            "command": " ".join(cmd),
            "returncode": None,
            "status": "TIMEOUT",
            "elapsed_sec": time.time() - t0,
            "stdout_tail": (exc.stdout or "")[-4000:] if isinstance(exc.stdout, str) else "",
            "stderr_tail": (exc.stderr or "")[-2000:] if isinstance(exc.stderr, str) else "",
            "model": None,
            "proof_path": str(proof_path) if proof_path is not None else None,
        }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--core", type=Path, default=Path("data/restricted_cores/mask_001_E11_core.npy"))
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--prefix", required=True, help="Comma-separated fixed A masks; empty string allowed for no prefix")
    ap.add_argument("--outdir", type=Path, required=True)
    ap.add_argument("--name", default="prefix_completion")
    ap.add_argument("--mode", choices=["native", "plain"], default="native")
    ap.add_argument("--solver", default=None, help="default cryptominisat5 for native, kissat for plain")
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--maxconfl", type=int, default=0)
    ap.add_argument("--allow-zero-a", action="store_true")
    ap.add_argument("--sort-free-a", action="store_true", help="sort only the unfixed A suffix to break term-permutation symmetry without changing prefix containment")
    ap.add_argument("--write-only", action="store_true", help="emit CNF/XCNF and metadata without solving")
    ap.add_argument("--proof", action="store_true", help="for plain mode, ask solver to write a DRAT proof")
    args = ap.parse_args()

    core = np.load(args.core).astype(np.uint8) & 1
    prefix = [int(x) for x in args.prefix.split(",") if x.strip()]
    args.outdir.mkdir(parents=True, exist_ok=True)
    pc = PrefixCPD(core, args.rank, prefix, args.mode, allow_zero_a=args.allow_zero_a, sort_free_a=args.sort_free_a)
    suffix = ".xor.cnf" if args.mode == "native" else ".cnf"
    cnf_path = args.outdir / f"{args.name}{suffix}"
    comments = [
        "E11 prefix-completion CPD SAT",
        f"rank={args.rank}",
        f"prefix={prefix}",
        f"mode={args.mode}",
        f"allow_zero_a={args.allow_zero_a}",
    ]
    pc.F.write(cnf_path, comments)
    result = {
        "purpose": "exact E11 prefix-completion CPD SAT with variable remaining A and all B/C factors",
        "field": "F2",
        "core": str(args.core),
        "core_shape": list(core.shape),
        "rank": args.rank,
        "prefix": prefix,
        "prefix_size": len(prefix),
        "mode": args.mode,
        "allow_zero_a": bool(args.allow_zero_a),
        "sort_free_a": bool(args.sort_free_a),
        "vars": pc.var_count,
        "cnf_clauses": pc.cnf_clause_count,
        "native_xor_clauses": pc.xor_clause_count,
        "cnf_path": str(cnf_path),
        "cnf_sha256": sha256_file(cnf_path),
        "meaning": "SAT gives an exact E11 CPD after decode/verification; UNSAT for this prefix excludes every decomposition whose A multiset contains the prefix. Solver-only UNSAT should be upgraded to a plain-CNF DRAT proof before use as a durable subtree certificate.",
    }
    if not args.write_only:
        solver = args.solver or ("cryptominisat5" if args.mode == "native" else "kissat")
        proof_path = None
        if args.mode == "plain" and args.proof:
            proof_path = args.outdir / f"{args.name}.drat"
        if args.mode == "native":
            solve = solve_native(cnf_path, solver, args.timeout, args.threads, args.maxconfl)
        else:
            solve = solve_plain(cnf_path, solver, args.timeout, proof_path)
        model = solve.pop("model", None)
        result["solve"] = solve
        if solve.get("status") == "SAT" and model:
            us, vs, ws = pc.decode(model)
            ok, diff = verify(core, us, vs, ws)
            sol_path = args.outdir / f"{args.name}.solution.npz"
            pc.save_npz(sol_path, us, vs, ws)
            result["decoded_solution"] = {
                "u_masks": us,
                "v_masks": vs,
                "w_masks": ws,
                "verified": ok,
                "diff_count": diff,
                "solution_npz": str(sol_path),
                "model_lit_count": len(model),
            }
        if proof_path is not None and proof_path.exists():
            result["proof_sha256"] = sha256_file(proof_path)
            result["proof_size_bytes"] = proof_path.stat().st_size
    out = args.outdir / f"{args.name}.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    summary = {
        "rank": args.rank,
        "prefix": prefix,
        "mode": args.mode,
        "vars": result["vars"],
        "cnf_clauses": result["cnf_clauses"],
        "native_xor_clauses": result["native_xor_clauses"],
        "status": result.get("solve", {}).get("status", "WRITE_ONLY"),
        "decoded_verified": result.get("decoded_solution", {}).get("verified"),
        "elapsed_sec": result.get("solve", {}).get("elapsed_sec"),
        "json": str(out),
    }
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
