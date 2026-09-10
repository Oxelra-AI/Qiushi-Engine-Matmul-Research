#!/usr/bin/env python3
"""Lazy Wang-occupation support search coupled to one reusable fixed-A SAT model.

The E11 constructive route is exact over F2:
  a rank-19 CPD of the 8x9x9 E11 core lifts to a full rank-22 T333 CPD.

This script uses the complete Wang lower-bound LUT as an A-side occupation
necessary condition and immediately tests complete occupation-feasible A-multisets
with a reusable SAT solver in which the A-bits are assumptions.  It avoids
rebuilding one fixed-U CNF per support.

Workflow:
  1. Build/cache all 417,199 E11 core subspace masks with capacities at s=19.
  2. Start CP-SAT with total multiplicity and all 1D/2D Wang cuts.
  3. Repeatedly solve for an A-multiset, scan every cached subspace using bitsets,
     add exact violated Wang cuts when found.
  4. When a multiset passes all cached occupation cuts, canonicalize it under the
     verified 576-element quotient action and solve the fixed-A Brent equations
     using one incremental PySAT solver under A-bit assumptions.
  5. SAT gives an exact E11 rank-19 CPD, saved and independently verified.
     UNSAT adds an orbit block for the tested A-multiset and continues.

A finite run with UNSAT supports is not by itself a lower bound unless the search
records show every occupation-feasible orbit has been tested.  The produced cuts,
canonical supports, SAT statuses, and any witness are reusable evidence.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable

import numpy as np

SCRIPTS_A01 = Path("scripts")
SCRIPTS_A02 = Path("scripts")
for P in (SCRIPTS_A01, SCRIPTS_A02):
    if str(P) not in sys.path:
        sys.path.insert(0, str(P))

from core_capacity_from_wang_lut import CoreQuotient, PIVOTS  # noqa: E402
from wang_capacity_lazy import pack_basis, unpack_basis, subspace_points_from_basis  # noqa: E402
from wang_capacity_orbit_closed import extension_keys  # noqa: E402


def load_lut(path: Path):
    with path.open("rb") as f:
        d = pickle.load(f)
    return d["lut"], d.get("meta", {})


def enumerate_subspace_keys(n: int = 8) -> list[int]:
    levels = {0: {pack_basis(tuple())}}
    all_keys = set(levels[0])
    for d in range(n):
        nxt = set()
        for key in levels[d]:
            for ekey in extension_keys(unpack_basis(key), n=n):
                if (ekey & 0xF) == d + 1:
                    nxt.add(ekey)
        levels[d + 1] = nxt
        all_keys.update(nxt)
        print(f"  enum dim {d+1}: {len(nxt):,}")
    return sorted(all_keys)


def pts_to_mask(pts: Iterable[int]) -> int:
    m = 0
    for p in pts:
        if p:
            m |= 1 << (int(p) - 1)
    return m


def mask_to_points(mask: int) -> list[int]:
    pts = []
    x = int(mask)
    while x:
        lb = x & -x
        pts.append(lb.bit_length())  # because bit index p-1 -> point p
        x ^= lb
    return pts


def build_or_load_constraint_cache(lut_path: Path, cache_path: Path, rank: int = 19, rebuild: bool = False) -> dict:
    if cache_path.exists() and not rebuild:
        with cache_path.open("rb") as f:
            cache = pickle.load(f)
        if cache.get("rank_s") == rank and cache.get("core_name") == "E11":
            print(f"Loaded cache {cache_path}: {len(cache['masks']):,} subspaces")
            return cache
        print("Cache metadata mismatch; rebuilding.")

    print("Loading Wang LUT for E11 occupation cache...")
    lut, meta = load_lut(lut_path)
    core = CoreQuotient(PIVOTS["E11"])
    print("Enumerating all F2^8 subspaces for E11 cache...")
    keys8 = enumerate_subspace_keys(8)
    masks: list[int] = []
    caps: list[int] = []
    Ls: list[int] = []
    dims: list[int] = []
    key_list: list[int] = []
    t0 = time.time()
    for i, key8 in enumerate(keys8):
        key9 = core.key9_from_key8(key8)
        L = int(lut[key9])
        cap = int(rank - L)
        pts = subspace_points_from_basis(unpack_basis(key8))
        masks.append(pts_to_mask(pts))
        caps.append(cap)
        Ls.append(L)
        dims.append(key8 & 0xF)
        key_list.append(key8)
        if (i + 1) % 100000 == 0:
            print(f"  cached {i+1:,}/{len(keys8):,}")
    cache = {
        "problem": "E11 complete Wang occupation constraints as bit masks",
        "field": "F2",
        "core_name": "E11",
        "rank_s": rank,
        "lut_path": str(lut_path),
        "lut_meta_brief": {
            "coverage_ok": meta.get("coverage_ok"),
            "conflict_count": meta.get("conflict_count"),
            "subspace_count": len(lut),
        },
        "keys8": key_list,
        "masks": masks,
        "caps": caps,
        "Ls": Ls,
        "dims": dims,
        "stats": {
            "subspace_count": len(keys8),
            "dim_counts": dict(Counter(dims)),
            "L_counts": dict(Counter(Ls)),
            "cap_counts": dict(Counter(caps)),
            "nonvacuous_count": sum(1 for m, c in zip(masks, caps) if m and c < rank),
            "build_elapsed_sec": time.time() - t0,
        },
    }
    cache_path.parent.mkdir(parents=True, exist_ok=True)
    with cache_path.open("wb") as f:
        pickle.dump(cache, f, protocol=pickle.HIGHEST_PROTOCOL)
    cache_path.with_suffix(".summary.json").write_text(json.dumps({k: v for k, v in cache.items() if k not in ("keys8", "masks", "caps", "Ls", "dims")}, indent=2, sort_keys=True) + "\n")
    print(f"Saved cache {cache_path}")
    return cache


def multiset_to_bitsets(sol: dict[int, int]) -> tuple[int, dict[int, int]]:
    support_mask = 0
    extra: dict[int, int] = {}
    for p, c in sol.items():
        support_mask |= 1 << (int(p) - 1)
        if int(c) > 1:
            extra[int(p)] = int(c) - 1
    return support_mask, extra


def occupancy(mask: int, support_mask: int, extra: dict[int, int]) -> int:
    occ = (int(mask) & int(support_mask)).bit_count()
    for p, e in extra.items():
        if (int(mask) >> (p - 1)) & 1:
            occ += e
    return occ


def scan_violations(sol: dict[int, int], cache: dict, max_report: int = 2000) -> tuple[list[dict], dict]:
    support_mask, extra = multiset_to_bitsets(sol)
    masks = cache["masks"]
    caps = cache["caps"]
    dims = cache["dims"]
    Ls = cache["Ls"]
    keys8 = cache["keys8"]
    violations = []
    t0 = time.time()
    by_dim = Counter()
    by_L = Counter()
    max_excess = 0
    for i, (m, cap) in enumerate(zip(masks, caps)):
        if not m:
            continue
        occ = occupancy(m, support_mask, extra)
        if occ > cap:
            exc = occ - cap
            max_excess = max(max_excess, exc)
            by_dim[dims[i]] += 1
            by_L[Ls[i]] += 1
            if len(violations) < max_report:
                violations.append({
                    "index": i,
                    "key8": keys8[i],
                    "dim8": dims[i],
                    "L": Ls[i],
                    "cap": cap,
                    "occupancy": occ,
                    "excess": exc,
                    "point_count": int(m).bit_count(),
                    "points_head": mask_to_points(m)[:40],
                })
    violations.sort(key=lambda v: (v["excess"], v["L"], v["occupancy"], -v["dim8"]), reverse=True)
    stats = {
        "violation_count": int(sum(by_dim.values())),
        "violations_by_dim8": dict(by_dim),
        "violations_by_L": dict(by_L),
        "max_excess": max_excess,
        "elapsed_sec": time.time() - t0,
    }
    return violations, stats


# ---------- correct quotient orbit action loading ----------

def load_perms(perms_path: Path) -> list[tuple[int, ...]]:
    data = np.load(perms_path)
    arr = data["perms"]
    perms = [tuple(int(x) for x in row.tolist()) for row in arr]
    if len(perms) != 576:
        raise ValueError(f"expected 576 perms, got {len(perms)} from {perms_path}")
    if any(p[0] != 0 or set(p[1:]) != set(range(1, 256)) for p in perms):
        raise ValueError("bad quotient permutation set")
    return perms


def canonical_multiset(ms: Iterable[int], perms: list[tuple[int, ...]]) -> tuple[int, ...]:
    base = tuple(sorted(int(x) for x in ms))
    best = base
    for p in perms:
        img = tuple(sorted(p[x] for x in base))
        if img < best:
            best = img
    return best


def orbit_images(sol: dict[int, int], perms: list[tuple[int, ...]]) -> list[dict[int, int]]:
    seen = set()
    out = []
    ms = []
    for p, c in sorted(sol.items()):
        ms.extend([int(p)] * int(c))
    for perm in perms:
        img = tuple(sorted(perm[p] for p in ms))
        if img in seen:
            continue
        seen.add(img)
        d: dict[int, int] = {}
        for p in img:
            d[p] = d.get(p, 0) + 1
        out.append(d)
    return out


# ---------- incremental fixed-A SAT over the E11 core ----------

class IncrementalFixedASAT:
    def __init__(self, core_path: Path, rank: int, solver_name: str):
        from pysat.solvers import Solver
        self.core = np.load(core_path).astype(np.uint8) & 1
        self.rank = rank
        self.nU, self.nV, self.nW = self.core.shape
        self.next_var = 1
        self.clauses: list[list[int]] = []
        self.alpha: dict[tuple[int, int], int] = {}
        self.vvar: dict[tuple[int, int], int] = {}
        self.wvar: dict[tuple[int, int], int] = {}
        self.pvar: dict[tuple[int, int, int], int] = {}
        self.qvar: dict[tuple[int, int, int, int], int] = {}
        self._build_cnf()
        self.solver = Solver(name=solver_name, bootstrap_with=self.clauses)
        self.solver_name = solver_name

    def new_var(self) -> int:
        v = self.next_var
        self.next_var += 1
        return v

    def add(self, cl: Iterable[int]):
        self.clauses.append([int(x) for x in cl])

    def add_and(self, z: int, x: int, y: int):
        # z <-> x & y
        self.add([-x, -y, z])
        self.add([x, -z])
        self.add([y, -z])

    def add_xor_equals(self, vars_list: list[int], target: int):
        xs = list(vars_list)
        if not xs:
            if target:
                self.add([])
            return
        if len(xs) == 1:
            self.add([xs[0] if target else -xs[0]])
            return
        prev = xs[0]
        for i, curr in enumerate(xs[1:], start=1):
            if i < len(xs) - 1:
                z = self.new_var()
                # z = prev XOR curr
                self.add([-prev, -curr, -z])
                self.add([prev, curr, -z])
                self.add([prev, -curr, z])
                self.add([-prev, curr, z])
                prev = z
            else:
                if target:
                    self.add([-prev, -curr])
                    self.add([prev, curr])
                else:
                    self.add([-prev, curr])
                    self.add([prev, -curr])

    def _build_cnf(self):
        r = self.rank
        for t in range(r):
            for a in range(self.nU):
                self.alpha[(t, a)] = self.new_var()
            for b in range(self.nV):
                self.vvar[(t, b)] = self.new_var()
            for c in range(self.nW):
                self.wvar[(t, c)] = self.new_var()
        for t in range(r):
            for b in range(self.nV):
                for c in range(self.nW):
                    z = self.new_var()
                    self.pvar[(t, b, c)] = z
                    self.add_and(z, self.vvar[(t, b)], self.wvar[(t, c)])
        for t in range(r):
            for a in range(self.nU):
                for b in range(self.nV):
                    for c in range(self.nW):
                        z = self.new_var()
                        self.qvar[(t, a, b, c)] = z
                        self.add_and(z, self.alpha[(t, a)], self.pvar[(t, b, c)])
        for a in range(self.nU):
            for b in range(self.nV):
                for c in range(self.nW):
                    self.add_xor_equals([self.qvar[(t, a, b, c)] for t in range(r)], int(self.core[a, b, c]))

    @property
    def var_count(self) -> int:
        return self.next_var - 1

    @property
    def clause_count(self) -> int:
        return len(self.clauses)

    def assumptions_for_support(self, ms: list[int]) -> list[int]:
        if len(ms) != self.rank:
            raise ValueError(f"support list length {len(ms)} != rank {self.rank}")
        assumptions = []
        for t, u in enumerate(ms):
            for a in range(self.nU):
                var = self.alpha[(t, a)]
                assumptions.append(var if ((int(u) >> a) & 1) else -var)
        return assumptions

    @staticmethod
    def mask_from_model(model_set: set[int], vars_for_bits: list[int]) -> int:
        out = 0
        for i, var in enumerate(vars_for_bits):
            if var in model_set:
                out |= 1 << i
        return out

    def verify(self, us: list[int], vs: list[int], ws: list[int]) -> tuple[bool, int]:
        R = np.zeros_like(self.core)
        for u, v, w in zip(us, vs, ws):
            U = np.array([(int(u) >> a) & 1 for a in range(self.nU)], dtype=np.uint8).reshape(-1, 1, 1)
            V = np.array([(int(v) >> b) & 1 for b in range(self.nV)], dtype=np.uint8).reshape(1, -1, 1)
            W = np.array([(int(w) >> c) & 1 for c in range(self.nW)], dtype=np.uint8).reshape(1, 1, -1)
            R ^= (U * V * W).astype(np.uint8)
        diff = R ^ self.core
        return bool(not diff.any()), int(diff.sum())

    def save_npz(self, path: Path, us: list[int], vs: list[int], ws: list[int]):
        U = np.zeros((len(us), self.nU), dtype=np.uint8)
        V = np.zeros((len(us), self.nV), dtype=np.uint8)
        W = np.zeros((len(us), self.nW), dtype=np.uint8)
        for t, (u, v, w) in enumerate(zip(us, vs, ws)):
            for a in range(self.nU):
                U[t, a] = (int(u) >> a) & 1
            for b in range(self.nV):
                V[t, b] = (int(v) >> b) & 1
            for c in range(self.nW):
                W[t, c] = (int(w) >> c) & 1
        path.parent.mkdir(parents=True, exist_ok=True)
        np.savez(path, U=U, V=V, W=W, u_masks=np.array(us, dtype=np.uint16), v_masks=np.array(vs, dtype=np.uint16), w_masks=np.array(ws, dtype=np.uint16))

    def solve_support(self, ms: list[int], timeout_conflicts: int | None = None) -> dict:
        assumptions = self.assumptions_for_support(ms)
        t0 = time.time()
        if timeout_conflicts is not None:
            if hasattr(self.solver, "conf_budget"):
                self.solver.conf_budget(int(timeout_conflicts))
            sat = self.solver.solve_limited(assumptions=assumptions)
        else:
            sat = self.solver.solve(assumptions=assumptions)
        elapsed = time.time() - t0
        if sat is False:
            return {"status": "UNSAT", "elapsed_sec": elapsed}
        if sat is None:
            return {"status": "UNKNOWN", "elapsed_sec": elapsed, "conflict_budget": timeout_conflicts}
        model = self.solver.get_model()
        model_set = {lit for lit in model if lit > 0}
        vs = []
        ws = []
        for t in range(self.rank):
            vs.append(self.mask_from_model(model_set, [self.vvar[(t, b)] for b in range(self.nV)]))
            ws.append(self.mask_from_model(model_set, [self.wvar[(t, c)] for c in range(self.nW)]))
        ok, diff = self.verify(ms, vs, ws)
        return {"status": "SAT", "elapsed_sec": elapsed, "u_masks": ms, "v_masks": vs, "w_masks": ws, "verified": ok, "diff_count": diff}

    def delete(self):
        self.solver.delete()


# ---------- CP-SAT model utilities ----------

def add_mask_cut(model, xvars, mask: int, cap: int):
    pts = mask_to_points(mask)
    if not pts:
        if cap < 0:
            model.add(False)
        return
    model.add(sum(xvars[p] for p in pts) <= int(cap))


def solution_from_solver(solver, xvars) -> dict[int, int]:
    sol = {}
    for p in range(1, 256):
        val = int(solver.value(xvars[p]))
        if val:
            sol[p] = val
    return sol


def multiset_list(sol: dict[int, int]) -> list[int]:
    ms = []
    for p, c in sorted(sol.items()):
        ms.extend([p] * c)
    return ms


def add_exact_solution_block(model, xvars, sol: dict[int, int], tag: str):
    # With total multiplicity fixed at 19, exact equality to sol is prevented by
    # requiring at least one positive support variable to differ from its value.
    bs = []
    for p, c in sorted(sol.items()):
        b = model.new_bool_var(f"block_{tag}_{p}")
        model.add(xvars[p] == int(c)).only_enforce_if(b)
        model.add(xvars[p] != int(c)).only_enforce_if(b.Not())
        bs.append(b)
    model.add(sum(bs) <= len(bs) - 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--cache", type=Path, default=Path("data/e11_capacity_sat/e11_capacity_cache.pkl"))
    ap.add_argument("--perms", type=Path, default=Path("data/e11_quotient_action/e11_quotient_action_verification.perms.npz"))
    ap.add_argument("--core", type=Path, default=Path("data/restricted_cores/mask_001_E11_core.npy"))
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--max-iters", type=int, default=30)
    ap.add_argument("--solver-time", type=float, default=60.0)
    ap.add_argument("--max-cuts-per-iter", type=int, default=2000)
    ap.add_argument("--max-orbit-block-images", type=int, default=576)
    ap.add_argument("--sat-solver", default="cadical195")
    ap.add_argument("--sat-conflicts", type=int, default=200000, help="Conflict budget per fixed-A SAT call; use <=0 for unlimited.")
    ap.add_argument("--json-out", type=Path, default=Path("data/e11_capacity_sat/lazy_incremental_sat_results.json"))
    ap.add_argument("--rebuild-cache", action="store_true")
    args = ap.parse_args()

    from ortools.sat.python import cp_model

    t_all = time.time()
    cache = build_or_load_constraint_cache(args.lut, args.cache, args.rank, args.rebuild_cache)
    perms = load_perms(args.perms)
    fixed_sat = IncrementalFixedASAT(args.core, args.rank, args.sat_solver)
    print(f"Incremental fixed-A SAT: solver={args.sat_solver} vars={fixed_sat.var_count:,} clauses={fixed_sat.clause_count:,}")

    model = cp_model.CpModel()
    xvars = {p: model.new_int_var(0, args.rank, f"x_{p}") for p in range(1, 256)}
    model.add(sum(xvars[p] for p in range(1, 256)) == args.rank)

    masks = cache["masks"]
    caps = cache["caps"]
    dims = cache["dims"]
    Ls = cache["Ls"]
    keys8 = cache["keys8"]
    added_indices: set[int] = set()
    cut_records = []

    def add_cut_index(i: int, reason: str) -> bool:
        if i in added_indices:
            return False
        if masks[i] and caps[i] < args.rank:
            add_mask_cut(model, xvars, masks[i], caps[i])
            added_indices.add(i)
            cut_records.append({"index": i, "key8": keys8[i], "dim8": dims[i], "L": Ls[i], "cap": caps[i], "point_count": int(masks[i]).bit_count(), "reason": reason})
            return True
        return False

    # Initial 1D/2D occupation information is cheap and strong.
    for i, d in enumerate(dims):
        if d <= 2:
            add_cut_index(i, "initial_dim_le_2")
    print(f"Initial Wang cuts: {len(added_indices):,} by dim {dict(Counter(rec['dim8'] for rec in cut_records))}")

    seen_canonical = set()
    tested_supports = []
    history = []
    conclusion = None
    witness_path = None

    for it in range(1, args.max_iters + 1):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = args.solver_time
        solver.parameters.num_workers = 8
        solver.parameters.random_seed = 9000 + it
        t0 = time.time()
        status = solver.solve(model)
        elapsed = time.time() - t0
        status_name = {
            cp_model.OPTIMAL: "OPTIMAL",
            cp_model.FEASIBLE: "FEASIBLE",
            cp_model.INFEASIBLE: "INFEASIBLE",
            cp_model.MODEL_INVALID: "MODEL_INVALID",
            cp_model.UNKNOWN: "UNKNOWN",
        }.get(status, str(status))
        entry = {"iteration": it, "cpsat_status": status_name, "cut_count": len(added_indices), "solve_elapsed_sec": elapsed}
        print(f"iter {it}: CP-SAT {status_name} with {len(added_indices):,} cuts in {elapsed:.2f}s")
        if status == cp_model.INFEASIBLE:
            conclusion = "OCCUPATION_INFEASIBLE_WITH_ADDED_CUTS"
            history.append(entry)
            break
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            conclusion = f"CAPACITY_SOLVER_{status_name}"
            history.append(entry)
            break

        sol = solution_from_solver(solver, xvars)
        ms = multiset_list(sol)
        entry["solution"] = {str(k): v for k, v in sorted(sol.items())}
        entry["support_size"] = len(sol)
        entry["max_mult"] = max(sol.values()) if sol else 0
        entry["orbit_canonical"] = list(canonical_multiset(ms, perms))
        print(f"  support={len(sol)} max_mult={entry['max_mult']} ms={ms}")

        violations, stats = scan_violations(sol, cache, max_report=args.max_cuts_per_iter)
        entry["complete_occupation_scan"] = stats
        if violations:
            nadd = 0
            for v in violations[:args.max_cuts_per_iter]:
                if add_cut_index(v["index"], f"complete_scan_iter_{it}"):
                    nadd += 1
            entry["cuts_added"] = nadd
            entry["violations_head"] = violations[:20]
            print(f"  occupation violations={stats['violation_count']:,} max_excess={stats['max_excess']} scan={stats['elapsed_sec']:.2f}s added={nadd}")
            history.append(entry)
            if nadd == 0:
                # Avoid returning the same violated solution forever.
                add_exact_solution_block(model, xvars, sol, f"violated_{it}")
                entry["exact_block_added_due_to_no_new_cut"] = True
            continue

        canon = tuple(entry["orbit_canonical"])
        entry["complete_occupation_feasible"] = True
        if canon in seen_canonical:
            entry["orbit_duplicate"] = True
            add_exact_solution_block(model, xvars, sol, f"dup_{it}")
            print("  complete occupation feasible but orbit duplicate; exact raw block added")
            history.append(entry)
            continue
        seen_canonical.add(canon)

        sat_res = fixed_sat.solve_support(ms, None if args.sat_conflicts <= 0 else args.sat_conflicts)
        entry["fixed_A_sat"] = {k: v for k, v in sat_res.items() if k not in ("v_masks", "w_masks")}
        print(f"  complete occupation feasible; fixed-A SAT {sat_res['status']} in {sat_res['elapsed_sec']:.2f}s")
        tested_supports.append({
            "iteration": it,
            "canonical": list(canon),
            "solution": {str(k): v for k, v in sorted(sol.items())},
            "sat_status": sat_res["status"],
            "sat_verified": sat_res.get("verified"),
            "sat_diff_count": sat_res.get("diff_count"),
            "sat_elapsed_sec": sat_res["elapsed_sec"],
        })
        if sat_res["status"] == "SAT":
            out_npz = args.json_out.with_suffix(".rank19_e11_solution.npz")
            fixed_sat.save_npz(out_npz, sat_res["u_masks"], sat_res["v_masks"], sat_res["w_masks"])
            witness_path = str(out_npz)
            entry["witness_npz"] = witness_path
            conclusion = "FOUND_E11_RANK19_CPD"
            history.append(entry)
            break

        # Exclude this exact A-multiset and, by the verified quotient action, all orbit images.
        images = orbit_images(sol, perms)
        if args.max_orbit_block_images > 0:
            images = images[:args.max_orbit_block_images]
        for j, img_sol in enumerate(images):
            add_exact_solution_block(model, xvars, img_sol, f"orb_{it}_{j}")
        entry["orbit_blocks_added"] = len(images)
        history.append(entry)
        print(f"  added {len(images)} exact orbit blocks after SAT {sat_res['status']}")

    fixed_sat.delete()
    if conclusion is None:
        conclusion = "ITERATION_LIMIT_REACHED"

    result = {
        "problem": "E11 rank-19 occupation-guided incremental fixed-A SAT search",
        "field": "F2",
        "rank_s": args.rank,
        "meaning": "SAT witness verifies an E11 rank-19 CPD and hence gives a full F2 rank-22 T333 decomposition after the known +3 lift. UNSAT records exclude only tested A-multiset orbits unless all complete occupation-feasible orbits are exhausted.",
        "constraint_cache": {"path": str(args.cache), "stats": cache.get("stats"), "lut_meta_brief": cache.get("lut_meta_brief")},
        "quotient_permutation_file": str(args.perms),
        "incremental_sat": {"solver": args.sat_solver, "variables": fixed_sat.var_count, "clauses": fixed_sat.clause_count},
        "initial_cut_count": sum(1 for rec in cut_records if rec["reason"] == "initial_dim_le_2"),
        "final_cut_count": len(added_indices),
        "cuts_by_dim8": dict(Counter(rec["dim8"] for rec in cut_records)),
        "tested_complete_occupation_feasible_orbits": len(tested_supports),
        "tested_supports": tested_supports,
        "conclusion": conclusion,
        "witness_npz": witness_path,
        "history": history,
        "elapsed_sec": time.time() - t_all,
    }
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "conclusion": conclusion,
        "tested_complete_occupation_feasible_orbits": len(tested_supports),
        "final_cut_count": len(added_indices),
        "witness_npz": witness_path,
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))
    print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
