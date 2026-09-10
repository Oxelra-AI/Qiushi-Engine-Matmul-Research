#!/usr/bin/env python3
"""DIMACS CNF generator and validator for the E11 8x9x9 core CPD equations over F2.

Mathematical target
-------------------
For rank r, variables are binary masks
    u_t in F2^8, v_t in F2^9, w_t in F2^9,  t=0..r-1,
and the Brent equations are
    XOR_t u_t[s] v_t[b] w_t[c] = core[s,b,c]
for all s=0..7, b,c=0..8, where core = T_{<3,3,3>}[1:9,:,:]
(the E11 quotient/restricted core with the a00 slice deleted).

Layer discipline
----------------
This script deliberately separates clauses by status.

Certified layer (usable in a theorem after independent replay of this generator):
  * exact Brent equations with explicit Tseytin AND variables and XOR chains;
  * per-slice capacity |{t: u_t[s]=1}| >= 3, encoded by exhaustive forbidden
    patterns of size <=2. This follows from rank(I_3)=3 in each nonzero slice;
  * term permutation sorting by integer value of u_t, encoded as u_t <= u_{t+1}.

Orbit-branch layer (theorem-safe only together with the verified stabilizer-orbit
cover):
  * a branch chooses the first occupied E11 quotient point orbit. Earlier orbits
    are forbidden, and one term is forced to equal the representative of the
    branch orbit. The union over all point orbits covers all nonzero-u solutions
    up to the E11 quotient stabilizer.

Accelerator layer (search only unless independently proved in this investigation):
  * placeholder for distinct-u, Wang rows, independent-verification-record consequences. These are
    intentionally NOT emitted by this script yet.

Positive controls
-----------------
Use --known-pool/--known-row/--known-units to add unit clauses for a known core
CPD. With --validate-known, the script computes all auxiliary variables from the
known base assignment and checks every emitted clause before writing trust in any
solver result.
"""
from __future__ import annotations

import argparse
import json
import itertools
import hashlib
from pathlib import Path
from typing import Dict, Iterable, List, Tuple, Optional

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DEFAULT_CORE = WS / "data" / "e11_bridge" / "e11_core_8x9x9.npy"
DEFAULT_ORBITS = WS / "data" / "e11_orbits" / "e11_quotient_orbits.json"


def build_t333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1
    return T


def build_core() -> np.ndarray:
    return build_t333()[1:9].copy()


def vec_from_mask(mask: int, n: int) -> np.ndarray:
    return np.array([(int(mask) >> i) & 1 for i in range(n)], dtype=np.uint8)


def reconstruct_core_from_terms(terms: List[Tuple[int, int, int]]) -> np.ndarray:
    out = np.zeros((8, 9, 9), dtype=np.uint8)
    for u, v, w in terms:
        out ^= (vec_from_mask(u, 8).reshape(8, 1, 1)
                * vec_from_mask(v, 9).reshape(1, 9, 1)
                * vec_from_mask(w, 9).reshape(1, 1, 9)).astype(np.uint8)
    return out


def load_pool_terms(path: Path, row: int, rank: Optional[int] = None, sort_u: bool = False) -> List[Tuple[int, int, int]]:
    arr = np.load(path)
    flat = arr[row]
    r = len(flat) // 3
    terms = [(int(flat[3 * t]), int(flat[3 * t + 1]), int(flat[3 * t + 2])) for t in range(r)]
    if rank is not None and r != rank:
        raise ValueError(f"known pool row has rank {r}, requested rank {rank}")
    if sort_u:
        terms = sorted(terms, key=lambda z: (z[0], z[1], z[2]))
    return terms


class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses: List[List[int]] = []
        self.comments: List[str] = []
        self.names: Dict[str, int] = {}
        self.rev: Dict[int, str] = {}

    def new_var(self, name: str) -> int:
        self.nv += 1
        v = self.nv
        self.names[name] = v
        self.rev[v] = name
        return v

    def add(self, lits: Iterable[int]):
        c = [int(x) for x in lits]
        if not c:
            raise ValueError("empty clause requested")
        self.clauses.append(c)

    def add_unit(self, lit: int):
        self.add([lit])

    def add_and2(self, out: int, a: int, b: int):
        # out <-> (a & b)
        self.add([-out, a])
        self.add([-out, b])
        self.add([out, -a, -b])

    def add_xor2(self, out: int, a: int, b: int):
        # out <-> a XOR b
        self.add([-a, -b, -out])
        self.add([-a, b, out])
        self.add([a, -b, out])
        self.add([a, b, -out])

    def add_xor_equals(self, xs: List[int], target: int, stem: str):
        target = int(target) & 1
        if len(xs) == 0:
            if target:
                raise ValueError("cannot encode false empty XOR without empty clause in this generator")
            return
        if len(xs) == 1:
            self.add_unit(xs[0] if target else -xs[0])
            return
        acc = self.new_var(f"{stem}.xor0")
        self.add_xor2(acc, xs[0], xs[1])
        for i, x in enumerate(xs[2:], start=1):
            nxt = self.new_var(f"{stem}.xor{i}")
            self.add_xor2(nxt, acc, x)
            acc = nxt
        self.add_unit(acc if target else -acc)

    def add_xnor_var(self, out: int, a: int, b: int):
        # out <-> (a == b)
        self.add([-out, -a, b])
        self.add([-out, a, -b])
        self.add([out, a, b])
        self.add([out, -a, -b])

    def add_prefix_eq_step(self, out: int, prev: Optional[int], a: int, b: int):
        # out <-> (prev is true) AND (a == b); if prev is None, prev is constant true.
        if prev is not None:
            self.add([-out, prev])
        self.add([-out, -a, b])
        self.add([-out, a, -b])
        if prev is None:
            self.add([out, a, b])
            self.add([out, -a, -b])
        else:
            self.add([-prev, a, b, out])
            self.add([-prev, -a, -b, out])

    def write_dimacs(self, path: Path):
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w") as f:
            for c in self.comments:
                f.write(f"c {c}\n")
            f.write(f"p cnf {self.nv} {len(self.clauses)}\n")
            for cl in self.clauses:
                f.write(" ".join(str(x) for x in cl) + " 0\n")

    def evaluate_clause(self, clause: List[int], assignment: Dict[int, int]) -> bool:
        for lit in clause:
            v = abs(lit)
            if v not in assignment:
                raise KeyError(f"variable {v} ({self.rev.get(v)}) missing from assignment")
            val = bool(assignment[v])
            if (lit > 0 and val) or (lit < 0 and not val):
                return True
        return False

    def validate(self, assignment: Dict[int, int], max_bad: int = 20) -> dict:
        bad = []
        for i, cl in enumerate(self.clauses):
            if not self.evaluate_clause(cl, assignment):
                bad.append({"clause_index": i, "clause": cl, "names": [self.rev.get(abs(x), "?") for x in cl]})
                if len(bad) >= max_bad:
                    break
        return {"ok": len(bad) == 0, "num_clauses": len(self.clauses), "bad_head": bad}


class E11CoreEncoder:
    def __init__(self, rank: int, core: np.ndarray, sort_u: bool = True, capacity: bool = True,
                 branch_orbits: Optional[dict] = None, branch_index: Optional[int] = None,
                 known_terms: Optional[List[Tuple[int, int, int]]] = None, known_units: bool = False):
        self.rank = int(rank)
        self.core = core.astype(np.uint8) & 1
        assert self.core.shape == (8, 9, 9)
        self.sort_u = bool(sort_u)
        self.capacity = bool(capacity)
        self.branch_orbits = branch_orbits
        self.branch_index = branch_index
        self.known_terms = known_terms
        self.known_units = bool(known_units)
        self.F = CNF()
        self.u: List[List[int]] = []
        self.v: List[List[int]] = []
        self.w: List[List[int]] = []
        self.uv: Dict[Tuple[int, int, int], int] = {}
        self.p: Dict[Tuple[int, int, int, int], int] = {}
        self.layers: List[str] = []

    def make_base(self):
        for t in range(self.rank):
            self.u.append([self.F.new_var(f"u[{t},{s}]") for s in range(8)])
            self.v.append([self.F.new_var(f"v[{t},{b}]") for b in range(9)])
            self.w.append([self.F.new_var(f"w[{t},{c}]") for c in range(9)])

    def add_brent(self):
        self.layers.append("certified:Brent+Tseytin+XOR")
        # uv variables reused over c.
        for t in range(self.rank):
            for s in range(8):
                for b in range(9):
                    x = self.F.new_var(f"uv[{t},{s},{b}]")
                    self.uv[(t, s, b)] = x
                    self.F.add_and2(x, self.u[t][s], self.v[t][b])
        # p variables and parity equations.
        for s in range(8):
            for b in range(9):
                for c in range(9):
                    xs = []
                    for t in range(self.rank):
                        x = self.F.new_var(f"p[{t},{s},{b},{c}]")
                        self.p[(t, s, b, c)] = x
                        self.F.add_and2(x, self.uv[(t, s, b)], self.w[t][c])
                        xs.append(x)
                    self.F.add_xor_equals(xs, int(self.core[s, b, c]), f"eq[{s},{b},{c}]")

    def add_slice_capacity(self):
        if not self.capacity:
            return
        self.layers.append("certified:slice_capacity_ge3")
        # For each slice, forbid exactly 0,1,2 active u-bits. This is compact for rank <=21.
        for s in range(8):
            vars_s = [self.u[t][s] for t in range(self.rank)]
            for k in (0, 1, 2):
                for true_set in itertools.combinations(range(self.rank), k):
                    Tset = set(true_set)
                    # Clause falsified precisely when variables in Tset are true and all others false.
                    clause = []
                    for t, var in enumerate(vars_s):
                        clause.append(-var if t in Tset else var)
                    self.F.add(clause)

    def add_sort_u(self):
        if not self.sort_u:
            return
        self.layers.append("certified:term_sort_u_integer_nondecreasing")
        # Enforce integer value u_t <= u_{t+1}. Compare bits high to low.
        for t in range(self.rank - 1):
            prev_eq: Optional[int] = None  # constant true before top bit
            for bit in range(7, -1, -1):
                a = self.u[t][bit]
                b = self.u[t + 1][bit]
                # If all higher bits equal, not(a=1,b=0).
                if prev_eq is None:
                    self.F.add([-a, b])
                else:
                    self.F.add([-prev_eq, -a, b])
                if bit > 0:
                    nxt = self.F.new_var(f"lexeq_u[{t},{bit}]")
                    self.F.add_prefix_eq_step(nxt, prev_eq, a, b)
                    prev_eq = nxt

    @staticmethod
    def forbid_value_clause(vars_bits: List[int], value: int) -> List[int]:
        # Forbid all bits exactly equal to value.
        clause = []
        for i, var in enumerate(vars_bits):
            clause.append(-var if ((value >> i) & 1) else var)
        return clause

    def add_orbit_branch(self):
        if self.branch_index is None:
            return
        if self.branch_orbits is None:
            raise ValueError("branch_index requested but no orbit JSON supplied")
        orbits = self.branch_orbits["point_orbits"]["orbits"]
        i = int(self.branch_index)
        if not (0 <= i < len(orbits)):
            raise ValueError(f"branch index {i} outside 0..{len(orbits)-1}")
        self.layers.append(f"orbit_cover:branch_{i}")
        # Order orbits by their listed orbit id. Earlier occupied orbits are forbidden.
        earlier_values: List[int] = []
        for j in range(i):
            vals = self._orbit_members(orbits[j])
            earlier_values.extend(vals)
        for x in sorted(set(earlier_values)):
            for t in range(self.rank):
                self.F.add(self.forbid_value_clause(self.u[t], x))
        rep = int(orbits[i]["seed"] if "seed" in orbits[i] else orbits[i]["reps"][0])
        # Force at least one term to be exactly the branch representative. We use selector variables
        # e_t -> (u_t == rep), plus OR_t e_t. This is sufficient and exact for the branch.
        selectors = []
        for t in range(self.rank):
            e = self.F.new_var(f"branch_eq_rep[{i},{t},{rep}]")
            selectors.append(e)
            for bit, var in enumerate(self.u[t]):
                self.F.add([-e, var if ((rep >> bit) & 1) else -var])
        self.F.add(selectors)

    def _orbit_members(self, orbit_record: dict) -> List[int]:
        # this investigation-local orbit JSON generated by e11_quotient_orbits.py stores members.
        if "members" in orbit_record:
            return [int(x) for x in orbit_record["members"]]
        # Fallback for the old earlier research JSON (no members): only reps are present. Do not use for proofs.
        return [int(x) for x in orbit_record.get("reps", [])]

    def add_known_units(self):
        if not self.known_units:
            return
        if self.known_terms is None:
            raise ValueError("known_units requested but no known terms supplied")
        if len(self.known_terms) != self.rank:
            raise ValueError("known term rank mismatch")
        self.layers.append("control:known_base_units")
        for t, (um, vm, wm) in enumerate(self.known_terms):
            for bit, var in enumerate(self.u[t]):
                self.F.add_unit(var if ((um >> bit) & 1) else -var)
            for bit, var in enumerate(self.v[t]):
                self.F.add_unit(var if ((vm >> bit) & 1) else -var)
            for bit, var in enumerate(self.w[t]):
                self.F.add_unit(var if ((wm >> bit) & 1) else -var)

    def build(self) -> CNF:
        self.make_base()
        self.add_brent()
        self.add_slice_capacity()
        self.add_sort_u()
        self.add_orbit_branch()
        self.add_known_units()
        self.F.comments.extend([
            "E11 core CPD CNF over F2",
            f"rank={self.rank}",
            f"core_shape={list(self.core.shape)} core_nnz={int(self.core.sum())}",
            "core_convention=T333[1:9,:,:], i.e. a00 slice deleted, no XOR for E11",
            "layers=" + ",".join(self.layers),
            "base_var_count=" + str(self.rank * 26),
            "certified clauses are Brent/Tseytin/XOR, per-slice capacity >=3, and term sorting when enabled",
            "orbit branch clauses require this investigation-local quotient stabilizer orbit-cover proof if used",
        ])
        return self.F

    def known_full_assignment(self) -> Dict[int, int]:
        if self.known_terms is None:
            raise ValueError("no known terms supplied")
        if len(self.known_terms) != self.rank:
            raise ValueError("known term rank mismatch")
        A: Dict[int, int] = {}
        # Base vars.
        for t, (um, vm, wm) in enumerate(self.known_terms):
            for bit, var in enumerate(self.u[t]):
                A[var] = (um >> bit) & 1
            for bit, var in enumerate(self.v[t]):
                A[var] = (vm >> bit) & 1
            for bit, var in enumerate(self.w[t]):
                A[var] = (wm >> bit) & 1
        # Auxiliary vars by name order is easiest after all vars exist.
        # Compute uv and p directly.
        for (t, s, b), var in self.uv.items():
            A[var] = A[self.u[t][s]] & A[self.v[t][b]]
        for (t, s, b, c), var in self.p.items():
            A[var] = A[self.uv[(t, s, b)]] & A[self.w[t][c]]
        # Compute lex prefix equality variables and XOR chain variables from names.
        # The XOR variables are named eq[s,b,c].xorN in creation order. Reconstruct by scanning.
        # First all lexeq variables:
        for vnum, name in sorted(self.F.rev.items()):
            if name.startswith("lexeq_u["):
                inside = name[len("lexeq_u["):-1]
                t_s, bit_s = inside.split(",")
                t = int(t_s); bit = int(bit_s)
                # lexeq_u[t,bit] stores equality of bits 7..bit for pair (t,t+1).
                eq = 1
                for j in range(7, bit - 1, -1):
                    if A[self.u[t][j]] != A[self.u[t + 1][j]]:
                        eq = 0
                        break
                A[vnum] = eq
        # Branch selector vars: choose truth as exact equality to rep.
        for vnum, name in sorted(self.F.rev.items()):
            if name.startswith("branch_eq_rep["):
                inside = name[len("branch_eq_rep["):-1]
                bi_s, t_s, rep_s = inside.split(",")
                t = int(t_s); rep = int(rep_s)
                A[vnum] = 1 if all(A[self.u[t][bit]] == ((rep >> bit) & 1) for bit in range(8)) else 0
        # XOR chain vars.
        # Group by equation stem.
        xor_groups: Dict[Tuple[int, int, int], List[Tuple[int, int]]] = {}
        for vnum, name in sorted(self.F.rev.items()):
            if name.startswith("eq[") and ".xor" in name:
                left, idx_s = name.split(".xor")
                inside = left[len("eq["):-1]
                s_s, b_s, c_s = inside.split(",")
                key = (int(s_s), int(b_s), int(c_s))
                xor_groups.setdefault(key, []).append((int(idx_s), vnum))
        for key, items in xor_groups.items():
            s, b, c = key
            xs = [self.p[(t, s, b, c)] for t in range(self.rank)]
            vals = [A[x] for x in xs]
            acc = vals[0] ^ vals[1]
            for idx, var in sorted(items):
                if idx == 0:
                    A[var] = vals[0] ^ vals[1]
                    acc = A[var]
                else:
                    acc = acc ^ vals[idx + 1]
                    A[var] = acc
        return A


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--core", type=Path, default=DEFAULT_CORE)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--meta", type=Path, default=None)
    ap.add_argument("--no-sort-u", action="store_true")
    ap.add_argument("--no-capacity", action="store_true")
    ap.add_argument("--orbits", type=Path, default=DEFAULT_ORBITS)
    ap.add_argument("--branch-index", type=int, default=None)
    ap.add_argument("--known-pool", type=Path, default=None)
    ap.add_argument("--known-row", type=int, default=0)
    ap.add_argument("--known-units", action="store_true")
    ap.add_argument("--validate-known", action="store_true")
    ap.add_argument("--check-cut-soundness", action="store_true", help="with --known-pool, test whether non-unit cuts are satisfied by the known decomposition")
    args = ap.parse_args()

    if args.core.exists():
        core = np.load(args.core)
    else:
        core = build_core()
    if core.shape != (8, 9, 9):
        raise ValueError(f"bad core shape {core.shape}")

    known_terms = None
    known_validation = None
    if args.known_pool is not None:
        known_terms = load_pool_terms(args.known_pool, args.known_row, rank=args.rank, sort_u=not args.no_sort_u)
        recon = reconstruct_core_from_terms(known_terms)
        diff = int(np.sum(recon ^ core))
        if diff != 0:
            raise ValueError(f"known terms do not reconstruct core, diff={diff}")

    branch_orbits = None
    if args.branch_index is not None:
        branch_orbits = json.loads(args.orbits.read_text())

    enc = E11CoreEncoder(
        rank=args.rank,
        core=core,
        sort_u=not args.no_sort_u,
        capacity=not args.no_capacity,
        branch_orbits=branch_orbits,
        branch_index=args.branch_index,
        known_terms=known_terms,
        known_units=args.known_units,
    )
    F = enc.build()

    if args.validate_known:
        if known_terms is None:
            raise ValueError("--validate-known requires --known-pool")
        A = enc.known_full_assignment()
        known_validation = F.validate(A)
        if not known_validation["ok"]:
            print(json.dumps(known_validation, indent=2))
            raise SystemExit("known assignment does not satisfy generated CNF")

    cut_soundness = None
    if args.check_cut_soundness:
        if known_terms is None:
            raise ValueError("--check-cut-soundness requires --known-pool")
        # Rebuild the exact same configuration once without known-unit clauses, so the
        # known decomposition is tested against structural/cut clauses rather than
        # trivially forced base units.
        enc2 = E11CoreEncoder(
            rank=args.rank,
            core=core,
            sort_u=not args.no_sort_u,
            capacity=not args.no_capacity,
            branch_orbits=branch_orbits,
            branch_index=args.branch_index,
            known_terms=known_terms,
            known_units=False,
        )
        F2 = enc2.build()
        A2 = enc2.known_full_assignment()
        cut_soundness = F2.validate(A2)
        if not cut_soundness["ok"]:
            print(json.dumps(cut_soundness, indent=2))
            raise SystemExit("known decomposition violates this non-unit configuration")

    F.write_dimacs(args.out)
    digest = sha256_file(args.out)
    meta = {
        "problem": "E11 core CPD over F2",
        "rank": args.rank,
        "core_shape": list(core.shape),
        "core_nnz": int(core.sum()),
        "cnf_path": str(args.out),
        "sha256": digest,
        "num_vars": F.nv,
        "num_clauses": len(F.clauses),
        "base_vars": args.rank * 26,
        "sort_u": not args.no_sort_u,
        "slice_capacity_ge3": not args.no_capacity,
        "branch_index": args.branch_index,
        "layers": enc.layers,
        "known_pool": None if args.known_pool is None else str(args.known_pool),
        "known_row": args.known_row if args.known_pool is not None else None,
        "known_units": args.known_units,
        "known_validation": known_validation,
        "cut_soundness_validation": cut_soundness,
        "semantics": {
            "Brent": "XOR_t u_t[s]*v_t[b]*w_t[c] = core[s,b,c] for all 648 entries",
            "core_convention": "T333[1:9,:,:], a00 slice deleted",
            "capacity": "rank(I3)=3 in each of the eight nonzero slices implies at least three active terms per slice",
            "sort_u": "term permutation symmetry permits integer-nondecreasing u order",
            "branch": "earlier quotient point orbits forbidden and one term fixed to branch representative; complete only across all branches with verified orbit cover",
        },
    }
    if args.meta is None:
        args.meta = args.out.with_suffix(args.out.suffix + ".meta.json")
    args.meta.parent.mkdir(parents=True, exist_ok=True)
    args.meta.write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": "ok",
        "cnf": str(args.out),
        "meta": str(args.meta),
        "sha256": digest,
        "vars": F.nv,
        "clauses": len(F.clauses),
        "layers": enc.layers,
        "known_validation_ok": None if known_validation is None else known_validation["ok"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
