#!/usr/bin/env python3
"""Optimized exact E11 prefix-completion SAT over F2.

For a fixed A-prefix in a rank-r CPD, this encoder does not create variable
A-bits or A*B*C contribution variables for the fixed terms.  A fixed prefix term
contributes p_{t,b,c}=beta_{t,b}&gamma_{t,c} directly to Brent equations when
its fixed A mask contains the A-coordinate.  Only the unfixed suffix terms keep
variable alpha bits and q=alpha&p products.

Thus UNSAT for a prefix refutes every E11 rank-r decomposition containing that
A-prefix, while SAT is decoded and exactly verified.  The optimization is
logically equivalent to the direct prefix-completion encoding but much smaller
for large prefixes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
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


class XCNF:
    def __init__(self):
        self.next = 1
        self.cnf: list[list[int]] = []
        self.xors: list[tuple[list[int], int]] = []

    def new(self) -> int:
        v = self.next
        self.next += 1
        return v

    def add(self, lits) -> None:
        self.cnf.append([int(x) for x in lits])

    def add_and(self, z: int, a: int, b: int) -> None:
        self.add([-a, -b, z])
        self.add([a, -z])
        self.add([b, -z])

    def add_xor(self, lits, rhs: int) -> None:
        ll = [int(x) for x in lits]
        rhs = int(rhs) & 1
        if not ll:
            if rhs:
                self.add([])
            return
        self.xors.append((ll, rhs))

    def write(self, path: Path, comments=None) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("w") as f:
            for c in comments or []:
                f.write("c " + str(c) + "\n")
            f.write(f"p cnf {self.next - 1} {len(self.cnf) + len(self.xors)}\n")
            for lits, rhs in self.xors:
                if not lits:
                    if rhs:
                        f.write("0\n")
                    continue
                ll = list(lits)
                if rhs == 0:
                    ll[0] = -ll[0]
                f.write("x " + " ".join(map(str, ll)) + " 0\n")
            for cl in self.cnf:
                f.write(" ".join(map(str, cl)) + " 0\n")


class OptimizedPrefixCPD:
    def __init__(self, core: np.ndarray, rank: int, prefix: list[int], sort_free_a: bool = False, allow_zero_a: bool = False):
        self.core = core.astype(np.uint8) & 1
        self.rank = int(rank)
        self.prefix = [int(x) for x in prefix]
        if len(self.prefix) > self.rank:
            raise ValueError("prefix longer than rank")
        self.nU, self.nV, self.nW = self.core.shape
        if any(x <= 0 or x >= (1 << self.nU) for x in self.prefix):
            raise ValueError(f"prefix masks must be in 1..{(1 << self.nU)-1}")
        self.sort_free_a = bool(sort_free_a)
        self.allow_zero_a = bool(allow_zero_a)
        self.F = XCNF()
        self.alpha: dict[tuple[int, int], int] = {}
        self.vvar: dict[tuple[int, int], int] = {}
        self.wvar: dict[tuple[int, int], int] = {}
        self.pvar: dict[tuple[int, int, int], int] = {}
        self.qvar: dict[tuple[int, int, int, int], int] = {}
        self._build()

    def add_leq_bits(self, xs: list[int], ys: list[int]) -> None:
        if len(xs) != len(ys):
            raise ValueError("bad comparator")
        eq_prev: int | None = None
        for i in range(len(xs) - 1, -1, -1):
            x, y = xs[i], ys[i]
            if eq_prev is None:
                self.F.add([-x, y])
                if i > 0:
                    e = self.F.new()
                    self.F.add([-x, -y, e])
                    self.F.add([x, y, e])
                    self.F.add([-e, -x, y])
                    self.F.add([-e, x, -y])
                    eq_prev = e
            else:
                self.F.add([-eq_prev, -x, y])
                if i > 0:
                    e = self.F.new()
                    self.F.add([-e, eq_prev])
                    self.F.add([-e, -x, y])
                    self.F.add([-e, x, -y])
                    self.F.add([-eq_prev, -x, -y, e])
                    self.F.add([-eq_prev, x, y, e])
                    eq_prev = e

    def _build(self) -> None:
        k = len(self.prefix)
        for t in range(self.rank):
            if t >= k:
                for a in range(self.nU):
                    self.alpha[(t, a)] = self.F.new()
            for b in range(self.nV):
                self.vvar[(t, b)] = self.F.new()
            for c in range(self.nW):
                self.wvar[(t, c)] = self.F.new()
        for t in range(self.rank):
            for b in range(self.nV):
                for c in range(self.nW):
                    z = self.F.new()
                    self.pvar[(t, b, c)] = z
                    self.F.add_and(z, self.vvar[(t, b)], self.wvar[(t, c)])
        for t in range(k, self.rank):
            for a in range(self.nU):
                for b in range(self.nV):
                    for c in range(self.nW):
                        z = self.F.new()
                        self.qvar[(t, a, b, c)] = z
                        self.F.add_and(z, self.alpha[(t, a)], self.pvar[(t, b, c)])
        if not self.allow_zero_a:
            for t in range(k, self.rank):
                self.F.add([self.alpha[(t, a)] for a in range(self.nU)])
        if self.sort_free_a:
            for t in range(k, self.rank - 1):
                self.add_leq_bits([self.alpha[(t, a)] for a in range(self.nU)], [self.alpha[(t + 1, a)] for a in range(self.nU)])
        for a in range(self.nU):
            for b in range(self.nV):
                for c in range(self.nW):
                    lits: list[int] = []
                    for t, u in enumerate(self.prefix):
                        if (int(u) >> a) & 1:
                            lits.append(self.pvar[(t, b, c)])
                    for t in range(k, self.rank):
                        lits.append(self.qvar[(t, a, b, c)])
                    self.F.add_xor(lits, int(self.core[a, b, c]))

    def decode(self, model_lits: list[int]) -> tuple[list[int], list[int], list[int]]:
        pos = {int(x) for x in model_lits if int(x) > 0}
        us: list[int] = []
        vs: list[int] = []
        ws: list[int] = []
        k = len(self.prefix)
        for t in range(self.rank):
            if t < k:
                um = self.prefix[t]
            else:
                um = 0
                for a in range(self.nU):
                    if self.alpha[(t, a)] in pos:
                        um |= 1 << a
            vm = 0
            wm = 0
            for b in range(self.nV):
                if self.vvar[(t, b)] in pos:
                    vm |= 1 << b
            for c in range(self.nW):
                if self.wvar[(t, c)] in pos:
                    wm |= 1 << c
            us.append(um); vs.append(vm); ws.append(wm)
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


def solve(cnf_path: Path, timeout: int, threads: int, solver: str, maxconfl: int = 0) -> dict:
    cmd = [solver, "--verb", "0", "-t", str(threads), "--maxtime", str(timeout)]
    if maxconfl > 0:
        cmd += ["--maxconfl", str(maxconfl)]
    cmd.append(str(cnf_path))
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=timeout + 30)
        status = "UNKNOWN"
        if re.search(r"\bUNSATISFIABLE\b", proc.stdout):
            status = "UNSAT"
        elif re.search(r"\bSATISFIABLE\b", proc.stdout):
            status = "SAT"
        return {"command": " ".join(cmd), "returncode": proc.returncode, "status": status, "elapsed_sec": time.time() - t0,
                "stdout_tail": proc.stdout[-4000:], "stderr_tail": proc.stderr[-2000:], "model": parse_model(proc.stdout) if status == "SAT" else None}
    except subprocess.TimeoutExpired as exc:
        return {"command": " ".join(cmd), "returncode": None, "status": "TIMEOUT", "elapsed_sec": time.time() - t0,
                "stdout_tail": (exc.stdout or "")[-4000:] if isinstance(exc.stdout, str) else "", "stderr_tail": (exc.stderr or "")[-2000:] if isinstance(exc.stderr, str) else "", "model": None}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--core", type=Path, default=Path("data/restricted_cores/mask_001_E11_core.npy"))
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--prefix", required=True)
    ap.add_argument("--outdir", type=Path, required=True)
    ap.add_argument("--name", default="prefix_opt")
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--solver", default="cryptominisat5")
    ap.add_argument("--maxconfl", type=int, default=0)
    ap.add_argument("--sort-free-a", action="store_true")
    ap.add_argument("--allow-zero-a", action="store_true")
    ap.add_argument("--write-only", action="store_true")
    args = ap.parse_args()

    core = np.load(args.core).astype(np.uint8) & 1
    prefix = [int(x) for x in args.prefix.split(",") if x.strip()]
    pc = OptimizedPrefixCPD(core, args.rank, prefix, sort_free_a=args.sort_free_a, allow_zero_a=args.allow_zero_a)
    args.outdir.mkdir(parents=True, exist_ok=True)
    cnf_path = args.outdir / f"{args.name}.xor.cnf"
    pc.F.write(cnf_path, ["optimized E11 prefix-completion CPD SAT", f"rank={args.rank}", f"prefix={prefix}", f"sort_free_a={args.sort_free_a}"])
    result = {
        "purpose": "optimized exact E11 prefix-completion Brent SAT with fixed-A terms eliminated",
        "field": "F2",
        "rank": args.rank,
        "core": str(args.core),
        "prefix": prefix,
        "prefix_size": len(prefix),
        "sort_free_a": bool(args.sort_free_a),
        "allow_zero_a": bool(args.allow_zero_a),
        "vars": pc.F.next - 1,
        "cnf_clauses": len(pc.F.cnf),
        "native_xor_clauses": len(pc.F.xors),
        "cnf_path": str(cnf_path),
        "cnf_sha256": sha256_file(cnf_path),
        "meaning": "SAT decodes to an exact E11 CPD; UNSAT refutes all rank-r E11 CPDs whose A multiset contains this prefix. Fixed prefix terms are encoded directly in Brent XORs.",
    }
    if not args.write_only:
        sol = solve(cnf_path, args.timeout, args.threads, args.solver, args.maxconfl)
        model = sol.pop("model", None)
        result["solve"] = sol
        if sol.get("status") == "SAT" and model:
            us, vs, ws = pc.decode(model)
            ok, diff = verify(core, us, vs, ws)
            sol_path = args.outdir / f"{args.name}.solution.npz"
            pc.save_npz(sol_path, us, vs, ws)
            result["decoded_solution"] = {"u_masks": us, "v_masks": vs, "w_masks": ws, "verified": ok, "diff_count": diff, "solution_npz": str(sol_path), "model_lit_count": len(model)}
    out = args.outdir / f"{args.name}.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "prefix": prefix,
        "rank": args.rank,
        "vars": result["vars"],
        "cnf_clauses": result["cnf_clauses"],
        "native_xor_clauses": result["native_xor_clauses"],
        "status": result.get("solve", {}).get("status", "WRITE_ONLY"),
        "decoded_verified": result.get("decoded_solution", {}).get("verified"),
        "elapsed_sec": result.get("solve", {}).get("elapsed_sec"),
        "json": str(out),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
