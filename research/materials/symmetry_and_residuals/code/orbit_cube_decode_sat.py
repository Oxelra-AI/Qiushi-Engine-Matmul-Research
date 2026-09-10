#!/usr/bin/env python3
"""
analysis: cyclic F_2 search with orbit variables and cube syndrome decoding.

Instead of representing f fixed cyclic terms by f unknown linear forms with
cubic Tseitin gates, enumerate the 511 nonzero Boolean cubes x⊗x⊗x and use
one selector variable per cube.  The cube side is then a linear syndrome
with a cardinality bound <= f = 22 - 3m.

For each m = number of free cyclic 3-orbits, encode:
    T333 = sum_{selected cubes c} c^3
           + sum_{o=1}^m (U_o⊗V_o⊗W_o + cyclic rotations)
over F_2, with at most f selected cubes.  The 249 cyclic-invariant coordinate
equations are native XOR clauses for CryptoMiniSat; orbit monomials use AND
Tseitin gates.  The 120 diagonal-collapse high-degree consequences from
f2_diagonal_collapse.py are added as extra orbit-only XOR clauses.

SAT witnesses are expanded and verified against all 729 Brent equations.
UNSAT from this native-XOR encoding is a strong computational result but is
not by itself a DRAT certificate; if needed, rerun a standard-CNF proof encoder.
"""

from __future__ import annotations

import argparse
import itertools
import json
import subprocess
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / "data" / "orbit_cube_decode"
N = 9


def idx(a: int, b: int) -> int:
    return 3 * a + b


def build_T333():
    T = [[[0] * N for _ in range(N)] for _ in range(N)]
    for a in range(3):
        for b in range(3):
            for c in range(3):
                T[idx(a, b)][idx(b, c)][idx(c, a)] ^= 1
    return T


def cyclic_orbit_reps(n: int = N) -> List[Tuple[int, int, int]]:
    seen = set(); reps = []
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if (i, j, k) in seen:
                    continue
                orb = set(); t = (i, j, k)
                while t not in orb:
                    orb.add(t); t = (t[1], t[2], t[0])
                reps.append(min(orb)); seen |= orb
    reps.sort()
    return reps


def trM3_anf_masks() -> Dict[int, int]:
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


def all_nonzero_cube_masks() -> List[int]:
    return list(range(1, 1 << N))


def cube_coeff(cube_mask: int, i: int, j: int, k: int) -> int:
    return ((cube_mask >> i) & 1) & ((cube_mask >> j) & 1) & ((cube_mask >> k) & 1)


class CMSXOREncoder:
    def __init__(self):
        self.nv = 0
        self.reg: List[Tuple[int, ...]] = []
        self.xors: List[Tuple[int, List[int]]] = []  # XOR(vars) = target
        self.and_cache: Dict[Tuple[int, ...], int] = {}

    def new_var(self) -> int:
        self.nv += 1
        return self.nv

    def new_vars(self, n: int) -> List[int]:
        return [self.new_var() for _ in range(n)]

    def cl(self, *lits: int):
        self.reg.append(tuple(lits))

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
        if len(set(key)) == 2:
            xs = list(key)
            if xs[0] == xs[1]:
                q = self.AND2(xs[0], xs[2])
            else:
                q = self.AND2(xs[0], xs[1])
        else:
            q = self.AND2(self.AND2(key[0], key[1]), key[2])
        self.and_cache[key] = q
        return q

    def add_xor(self, terms: Sequence[int], target: int):
        # cancel duplicate variable occurrences over F_2
        parity: Dict[int, int] = {}
        for t in terms:
            parity[t] = parity.get(t, 0) ^ 1
            if parity[t] == 0:
                del parity[t]
        terms = sorted(parity)
        if not terms:
            if target:
                self.cl()  # empty regular clause
            return
        self.xors.append((target & 1, list(terms)))

    def add_lex_le(self, a: Sequence[int], b: Sequence[int]):
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

    def add_at_most_k(self, xs: Sequence[int], k: int):
        """Sinz sequential-counter encoding for sum xs <= k."""
        n = len(xs)
        if k >= n:
            return
        if k < 0:
            self.cl(); return
        if k == 0:
            for x in xs:
                self.cl(-x)
            return
        # s[i][j] for i=0..n-1, j=1..k, encoded as list index j-1.
        s = [[self.new_var() for _ in range(k)] for _ in range(n)]
        # i=0
        self.cl(-xs[0], s[0][0])
        for j in range(1, k):
            self.cl(-s[0][j])
        # i>0
        for i in range(1, n):
            # s_i1 <- x_i or s_{i-1,1}
            self.cl(-xs[i], s[i][0])
            self.cl(-s[i-1][0], s[i][0])
            # prevent k+1 at i
            self.cl(-xs[i], -s[i-1][k-1])
            for j in range(1, k):
                self.cl(-s[i-1][j], s[i][j])
                self.cl(-xs[i], -s[i-1][j-1], s[i][j])

    def write(self, path: Path):
        with path.open("w") as f:
            f.write(f"p cnf {self.nv} {len(self.reg) + len(self.xors)}\n")
            for cl in self.reg:
                f.write(" ".join(map(str, cl)) + " 0\n")
            # CryptoMiniSat XOR clause convention: positive XOR literals = true.
            # A negated literal flips parity, so negating one term encodes target 0.
            for target, terms in self.xors:
                lits = terms[:]
                if target == 0:
                    lits[0] = -lits[0]
                f.write("x " + " ".join(map(str, lits)) + " 0\n")


def orbit_contribution_vars(enc: CMSXOREncoder, U, V, W, i: int, j: int, k: int) -> List[int]:
    if i == j == k:
        return [enc.AND3(U[i], V[i], W[i])]
    return [
        enc.AND3(U[i], V[j], W[k]),
        enc.AND3(V[i], W[j], U[k]),
        enc.AND3(W[i], U[j], V[k]),
    ]


def product_terms_for_mask(mask: int, U, V, W, enc: CMSXOREncoder) -> List[int]:
    vs = mask_vars(mask)
    terms = []
    if len(vs) == 2:
        p, q = vs
        assignments = [(p,p,q), (p,q,p), (q,p,p), (q,q,p), (q,p,q), (p,q,q)]
    elif len(vs) == 3:
        assignments = list(itertools.permutations(vs, 3))
    else:
        raise ValueError(mask)
    for a, b, c in assignments:
        terms.append(enc.AND3(U[a], V[b], W[c]))
    return terms


def encode_instance(m: int, f: int, add_diag: bool = True, sym_break: bool = True):
    T = build_T333(); reps = cyclic_orbit_reps(); cube_masks = all_nonzero_cube_masks()
    enc = CMSXOREncoder()
    U = [enc.new_vars(N) for _ in range(m)]
    V = [enc.new_vars(N) for _ in range(m)]
    W = [enc.new_vars(N) for _ in range(m)]
    S = enc.new_vars(len(cube_masks))  # selected nonzero cubes

    if sym_break:
        for o in range(m):
            # rotation (U,V,W)->(V,W,U): choose lex-min first vector among the three.
            enc.add_lex_le(U[o], V[o])
            enc.add_lex_le(U[o], W[o])
        for o in range(m - 1):
            enc.add_lex_le(U[o] + V[o] + W[o], U[o + 1] + V[o + 1] + W[o + 1])

    enc.add_at_most_k(S, f)

    # Full cyclic-invariant coordinate equations with linear cube selectors.
    for i, j, k in reps:
        terms: List[int] = []
        for o in range(m):
            terms.extend(orbit_contribution_vars(enc, U[o], V[o], W[o], i, j, k))
        for s_var, cm in zip(S, cube_masks):
            if cube_coeff(cm, i, j, k):
                terms.append(s_var)
        enc.add_xor(terms, T[i][j][k])

    diag_masks = []
    if add_diag:
        anf = trM3_anf_masks()
        for d in (2, 3):
            for tup in itertools.combinations(range(N), d):
                mask = mask_from_tuple(tup)
                terms = []
                for o in range(m):
                    terms.extend(product_terms_for_mask(mask, U[o], V[o], W[o], enc))
                enc.add_xor(terms, anf.get(mask, 0))
                diag_masks.append(mask)

    return enc, {"U": U, "V": V, "W": W, "S": S, "cube_masks": cube_masks, "reps": reps, "diag_masks": diag_masks}


def run_cms(path: Path, timeout: int):
    t0 = time.time()
    try:
        r = subprocess.run(["cryptominisat5", "--verb", "0", str(path)], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"status": "TIMEOUT", "time_sec": time.time() - t0, "returncode": None, "stdout": "", "stderr": ""}
    out = r.stdout + r.stderr
    if r.returncode == 10:
        st = "SAT"
    elif r.returncode == 20:
        st = "UNSAT"
    else:
        st = "UNKNOWN"
    return {"status": st, "time_sec": time.time() - t0, "returncode": r.returncode, "stdout": r.stdout, "stderr": r.stderr}


def parse_assignment(stdout: str) -> Dict[int, bool]:
    assign: Dict[int, bool] = {}
    for line in stdout.splitlines():
        if line.startswith("v "):
            for tok in line[2:].split():
                lit = int(tok)
                if lit == 0:
                    continue
                assign[abs(lit)] = (lit > 0)
    return assign


def bits_from_vars(assign: Dict[int, bool], vars_: Sequence[int]) -> List[int]:
    return [1 if assign.get(v, False) else 0 for v in vars_]


def mask_to_vec(mask: int) -> List[int]:
    return [(mask >> i) & 1 for i in range(N)]


def extract_solution(assign, vmap, m: int):
    orbits = []
    for o in range(m):
        orbits.append((bits_from_vars(assign, vmap["U"][o]), bits_from_vars(assign, vmap["V"][o]), bits_from_vars(assign, vmap["W"][o])))
    selected = []
    for var, cm in zip(vmap["S"], vmap["cube_masks"]):
        if assign.get(var, False):
            selected.append(cm)
    cubes = [mask_to_vec(cm) for cm in selected]
    return cubes, orbits, selected


def verify_brent(cubes, orbits, T):
    err = 0
    bad = []
    for i in range(N):
        for j in range(N):
            for k in range(N):
                val = 0
                for x in cubes:
                    val ^= x[i] & x[j] & x[k]
                for U, V, W in orbits:
                    val ^= U[i] & V[j] & W[k]
                    val ^= V[i] & W[j] & U[k]
                    val ^= W[i] & U[j] & V[k]
                if val != T[i][j][k]:
                    err += 1
                    if len(bad) < 20:
                        bad.append((i, j, k, val, T[i][j][k]))
    return err, bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, action="append", help="m value(s) to run; default 4..7")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--no-diag", action="store_true")
    ap.add_argument("--no-sym-break", action="store_true")
    args = ap.parse_args()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    ms = args.m if args.m is not None else [4, 5, 6, 7]
    T = build_T333()
    results = []
    for m in ms:
        f = 22 - 3 * m
        if f < 0:
            raise ValueError(f"m={m} gives f={f}<0")
        print("=" * 80)
        print(f"rank<=22 cyclic skeleton by orbit count m={m}, cube budget f={f}")
        t0 = time.time()
        enc, vmap = encode_instance(m, f, add_diag=not args.no_diag, sym_break=not args.no_sym_break)
        enc_sec = time.time() - t0
        tag = f"m{m}_f{f}" + ("_nodiag" if args.no_diag else "")
        cnf = DATA_DIR / f"orbit_cube_{tag}.cnf"
        enc.write(cnf)
        print(f"  encoded in {enc_sec:.2f}s: {enc.nv} vars, {len(enc.reg)} regular clauses, {len(enc.xors)} XOR clauses, file={cnf}")
        sol = run_cms(cnf, timeout=args.timeout)
        print(f"  CMS {sol['status']} in {sol['time_sec']:.3f}s returncode={sol['returncode']}")
        rec = {
            "m": m,
            "f": f,
            "rank_budget": f + 3 * m,
            "primary_orbit_vars": 27 * m,
            "cube_selector_vars": 511,
            "total_vars": enc.nv,
            "regular_clauses": len(enc.reg),
            "xor_clauses": len(enc.xors),
            "encoding_sec": round(enc_sec, 6),
            "timeout": args.timeout,
            "status": sol["status"],
            "solve_sec": round(sol["time_sec"], 6),
            "returncode": sol["returncode"],
            "cnf": str(cnf),
        }
        if sol["status"] == "SAT":
            assign = parse_assignment(sol["stdout"])
            cubes, orbits, selected = extract_solution(assign, vmap, m)
            err, bad = verify_brent(cubes, orbits, T)
            rec.update({
                "brent_errors": err,
                "bad_examples": bad,
                "selected_cube_count": len(selected),
                "selected_cube_masks": selected,
                "selected_cube_vectors": cubes,
                "orbits": [[U, V, W] for (U, V, W) in orbits],
                "nonzero_orbit_count": sum(1 for U, V, W in orbits if any(U) or any(V) or any(W)),
            })
            print(f"  witness selected_cubes={len(selected)} nonzero_orbits={rec['nonzero_orbit_count']} brent_errors={err}")
            if err == 0:
                print("  *** VERIFIED FULL 729 BRENT EQUATIONS: CYCLIC F2 RANK<=22 WITNESS FOUND ***")
        else:
            rec["stdout_tail"] = sol["stdout"][-4000:]
            rec["stderr_tail"] = sol["stderr"][-4000:]
        results.append(rec)
        # Save after each instance for crash-safe evidence.
        out = DATA_DIR / "orbit_cube_decode_results.json"
        out.write_text(json.dumps({"results": results}, indent=2) + "\n")
    print("=" * 80)
    out = DATA_DIR / "orbit_cube_decode_results.json"
    print(f"Saved {out}")


if __name__ == "__main__":
    main()
