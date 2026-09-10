#!/usr/bin/env python3
"""Orbit-distinct E11 A-support enumeration by incremental SAT plus exact fixed-U tests.

This is an alternative to generic integer CP-SAT for the E11 rank-19 Wang
occupation model.  It encodes the current finite set of occupation cuts as CNF
cardinality constraints and keeps one PySAT solver alive while it lazily adds
violated complete-Wang cuts.  When a support passes all 417,199 cached cuts, it
is canonicalized under the verified E11 quotient action and sent to the exact
fixed-A Brent SAT layer.

The A-side occupation variables use the exact dim-1 capacities: 249 points have
multiplicity <=1 and 6 points have multiplicity <=2.  Boolean y_p records one
copy of point p; z_p is present only for the six cap-2 points and records a
second copy with z_p => y_p.  All subspace capacities are encoded as cardinality
constraints over y_p plus the z_p belonging to points inside the subspace.

A SAT fixed-U witness is saved as an exact E11 rank-19 CPD and can be lifted to
rank 22 for T333 by the verified analysis +3 construction.  A finite collection of
UNSAT tested supports excludes only those orbit representatives unless every
occupation-feasible orbit is exhausted.
"""
from __future__ import annotations

import argparse
import json
import pickle
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable

import numpy as np
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))

from e11_capacity_incremental_sat import build_or_load_constraint_cache, mask_to_points  # noqa: E402
from e11_capacity_incremental_sat import load_perms, canonical_multiset, orbit_images  # noqa: E402


def point_caps_from_cache(cache: dict) -> dict[int, int]:
    caps = {}
    for m, cap, dim in zip(cache["masks"], cache["caps"], cache["dims"]):
        if dim == 1 and int(m).bit_count() == 1:
            p = int(m).bit_length()  # bit p-1 is set
            caps[p] = int(cap)
    if set(caps) != set(range(1, 256)):
        raise ValueError(f"bad singleton cap coverage: {len(caps)}")
    return caps


def multiset_to_bitsets(sol: dict[int, int]) -> tuple[int, dict[int, int]]:
    support_mask = 0
    extra = {}
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


def scan_violations(sol: dict[int, int], cache: dict, max_report: int) -> tuple[list[dict], dict]:
    support_mask, extra = multiset_to_bitsets(sol)
    violations = []
    by_dim = Counter()
    by_L = Counter()
    max_excess = 0
    t0 = time.time()
    for i, (m, cap) in enumerate(zip(cache["masks"], cache["caps"])):
        if not m:
            continue
        occ = occupancy(m, support_mask, extra)
        if occ > cap:
            exc = occ - cap
            by_dim[cache["dims"][i]] += 1
            by_L[cache["Ls"][i]] += 1
            max_excess = max(max_excess, exc)
            if len(violations) < max_report:
                violations.append({
                    "index": i,
                    "key8": cache["keys8"][i],
                    "dim8": cache["dims"][i],
                    "L": cache["Ls"][i],
                    "cap": cap,
                    "occupancy": occ,
                    "excess": exc,
                    "point_count": int(m).bit_count(),
                    "points_head": mask_to_points(m)[:40],
                })
    violations.sort(key=lambda v: (v["excess"], v["L"], v["occupancy"], -v["dim8"]), reverse=True)
    return violations, {
        "violation_count": int(sum(by_dim.values())),
        "violations_by_dim8": dict(by_dim),
        "violations_by_L": dict(by_L),
        "max_excess": max_excess,
        "elapsed_sec": time.time() - t0,
    }


class OccupationSATSolver:
    def __init__(self, rank: int, point_caps: dict[int, int], solver_name: str):
        self.rank = rank
        self.point_caps = point_caps
        self.top = 0
        self.y = {p: self._new_var() for p in range(1, 256)}
        self.z = {p: self._new_var() for p, cap in point_caps.items() if cap >= 2}
        self.solver = Solver(name=solver_name)
        self.solver_name = solver_name
        self.cut_count = 0
        self.clause_count = 0
        self._bootstrap()

    def _new_var(self) -> int:
        self.top += 1
        return self.top

    def add_clause(self, cl: Iterable[int]):
        self.solver.add_clause([int(x) for x in cl])
        self.clause_count += 1

    def add_card_atmost(self, lits: list[int], bound: int):
        if bound < 0:
            self.add_clause([])
            return
        if bound >= len(lits):
            return
        if bound == 0:
            for lit in lits:
                self.add_clause([-lit])
            return
        enc = CardEnc.atmost(lits=lits, bound=int(bound), top_id=self.top, encoding=EncType.seqcounter)
        self.top = max(self.top, enc.nv)
        for cl in enc.clauses:
            self.add_clause(cl)

    def add_card_equals(self, lits: list[int], bound: int):
        enc = CardEnc.equals(lits=lits, bound=int(bound), top_id=self.top, encoding=EncType.seqcounter)
        self.top = max(self.top, enc.nv)
        for cl in enc.clauses:
            self.add_clause(cl)

    def _bootstrap(self):
        # second copy implies first copy
        for p, zlit in self.z.items():
            self.add_clause([-zlit, self.y[p]])
        total_lits = [self.y[p] for p in range(1, 256)] + [self.z[p] for p in sorted(self.z)]
        self.add_card_equals(total_lits, self.rank)

    def lits_for_subspace_mask(self, mask: int) -> list[int]:
        lits = []
        x = int(mask)
        while x:
            lb = x & -x
            p = lb.bit_length()
            lits.append(self.y[p])
            if p in self.z:
                lits.append(self.z[p])
            x ^= lb
        return lits

    def add_cut(self, mask: int, cap: int):
        self.add_card_atmost(self.lits_for_subspace_mask(mask), int(cap))
        self.cut_count += 1

    def solve(self, conflict_budget: int | None = None):
        if conflict_budget is not None and hasattr(self.solver, "conf_budget"):
            self.solver.conf_budget(int(conflict_budget))
            return self.solver.solve_limited()
        return self.solver.solve()

    def extract_solution(self) -> dict[int, int]:
        model = self.solver.get_model()
        pos = {lit for lit in model if lit > 0}
        sol = {}
        for p in range(1, 256):
            c = 1 if self.y[p] in pos else 0
            if p in self.z and self.z[p] in pos:
                c += 1
            if c:
                sol[p] = c
        return sol

    def block_multiset(self, sol: dict[int, int]):
        lits = []
        for p, c in sorted(sol.items()):
            lits.append(self.y[p])
            if c >= 2:
                if p not in self.z:
                    raise ValueError("duplicate on non-cap2 point")
                lits.append(self.z[p])
        # Total multiplicity is fixed, so negating all occupied occurrence literals blocks exactly this multiset.
        self.add_clause([-lit for lit in lits])

    def delete(self):
        self.solver.delete()


def multiset_list(sol: dict[int, int]) -> list[int]:
    out = []
    for p, c in sorted(sol.items()):
        out.extend([int(p)] * int(c))
    return out


def run_fixed_u_sat(ms: list[int], outdir: Path, name: str, solver: str, timeout: int) -> dict:
    outdir.mkdir(parents=True, exist_ok=True)
    cmd = [
        "python", "scripts/fixed_u_core_sat.py",
        "--source", "list",
        "--u-list", ",".join(str(x) for x in ms),
        "--outdir", str(outdir),
        "--name", name,
        "--solve",
        "--solver", solver,
        "--timeout", str(timeout),
    ]
    t0 = time.time()
    proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=timeout + 30)
    json_path = outdir / f"{name}.json"
    data = json.loads(json_path.read_text()) if json_path.exists() else {}
    return {
        "command": " ".join(cmd),
        "returncode": proc.returncode,
        "elapsed_sec": time.time() - t0,
        "json_path": str(json_path),
        "cnf_path": str(outdir / f"{name}.cnf"),
        "stdout_tail": proc.stdout[-2000:],
        "stderr_tail": proc.stderr[-1000:],
        "result": data,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--cache", type=Path, default=Path("data/e11_capacity_sat/e11_capacity_cache.pkl"))
    ap.add_argument("--perms", type=Path, default=Path("data/e11_quotient_action/e11_quotient_action_verification.perms.npz"))
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--support-solver", default="cadical195")
    ap.add_argument("--support-conflicts", type=int, default=0, help="Optional conflict budget per support-enumerator solve; <=0 means unlimited.")
    ap.add_argument("--max-iters", type=int, default=100)
    ap.add_argument("--max-cuts-per-iter", type=int, default=2000)
    ap.add_argument("--initial-max-dim", type=int, default=2, help="Add all cached Wang cuts with dim <= this value before search.")
    ap.add_argument("--initial-max-cap", type=int, default=-1, help="Also add all cached Wang cuts with cap <= this value before search; <0 disables.")
    ap.add_argument("--fixed-u-solver", default="kissat")
    ap.add_argument("--fixed-u-timeout", type=int, default=120)
    ap.add_argument("--outdir", type=Path, default=Path("data/e11_occupation_sat"))
    ap.add_argument("--json-out", type=Path, default=Path("data/e11_occupation_sat/results.json"))
    ap.add_argument("--rebuild-cache", action="store_true")
    args = ap.parse_args()

    t_all = time.time()
    cache = build_or_load_constraint_cache(args.lut, args.cache, args.rank, args.rebuild_cache)
    perms = load_perms(args.perms)
    point_caps = point_caps_from_cache(cache)
    cap_counter = Counter(point_caps.values())
    cap2_points = sorted(p for p, c in point_caps.items() if c >= 2)
    print(f"point cap distribution: {dict(cap_counter)} cap2_points={cap2_points}")

    occ = OccupationSATSolver(args.rank, point_caps, args.support_solver)
    added_indices = set()
    cut_records = []

    def add_cut_index(i: int, reason: str) -> bool:
        if i in added_indices:
            return False
        if cache["masks"][i] and cache["caps"][i] < args.rank:
            occ.add_cut(cache["masks"][i], cache["caps"][i])
            added_indices.add(i)
            cut_records.append({
                "index": i,
                "key8": cache["keys8"][i],
                "dim8": cache["dims"][i],
                "L": cache["Ls"][i],
                "cap": cache["caps"][i],
                "point_count": int(cache["masks"][i]).bit_count(),
                "reason": reason,
            })
            return True
        return False

    # Start with low-dimensional occupation cuts; optionally include all small-capacity cuts.
    for i, d in enumerate(cache["dims"]):
        if d <= args.initial_max_dim:
            add_cut_index(i, f"initial_dim_le_{args.initial_max_dim}")
    if args.initial_max_cap >= 0:
        for i, cap in enumerate(cache["caps"]):
            if cap <= args.initial_max_cap:
                add_cut_index(i, f"initial_cap_le_{args.initial_max_cap}")
    print(f"bootstrap clauses={occ.clause_count:,} vars={occ.top:,} cuts={len(added_indices):,} initial_max_dim={args.initial_max_dim} initial_max_cap={args.initial_max_cap}")

    history = []
    tested_orbits = []
    seen_canon = set()
    conclusion = None
    witness = None

    for it in range(1, args.max_iters + 1):
        t0 = time.time()
        sat = occ.solve(None if args.support_conflicts <= 0 else args.support_conflicts)
        solve_elapsed = time.time() - t0
        entry = {"iteration": it, "cut_count": len(added_indices), "clauses": occ.clause_count, "vars": occ.top, "support_solve_elapsed_sec": solve_elapsed}
        if sat is None:
            entry["support_status"] = "UNKNOWN"
            conclusion = "SUPPORT_SOLVER_UNKNOWN"
            history.append(entry)
            print(f"iter {it}: support solver UNKNOWN after {solve_elapsed:.2f}s")
            break
        if sat is False:
            entry["support_status"] = "UNSAT"
            conclusion = "OCCUPATION_INFEASIBLE_FOR_ADDED_CUTS"
            history.append(entry)
            print(f"iter {it}: support solver UNSAT after {solve_elapsed:.2f}s with {len(added_indices):,} cuts")
            break
        sol = occ.extract_solution()
        ms = multiset_list(sol)
        canon = canonical_multiset(ms, perms)
        entry.update({
            "support_status": "SAT",
            "solution": {str(k): v for k, v in sorted(sol.items())},
            "multiset": ms,
            "support_size": len(sol),
            "max_mult": max(sol.values()) if sol else 0,
            "orbit_canonical": list(canon),
        })
        print(f"iter {it}: support SAT in {solve_elapsed:.2f}s cuts={len(added_indices):,} support={len(sol)} maxmult={entry['max_mult']} ms={ms}")

        violations, stats = scan_violations(sol, cache, max_report=args.max_cuts_per_iter)
        entry["complete_occupation_scan"] = stats
        if violations:
            nadd = 0
            for v in violations[:args.max_cuts_per_iter]:
                if add_cut_index(v["index"], f"scan_iter_{it}"):
                    nadd += 1
            entry["cuts_added"] = nadd
            entry["violations_head"] = violations[:20]
            print(f"  violations={stats['violation_count']:,} max_excess={stats['max_excess']} scan={stats['elapsed_sec']:.2f}s added={nadd}")
            if nadd == 0:
                occ.block_multiset(sol)
                entry["exact_block_due_to_no_new_cut"] = True
            history.append(entry)
            continue

        entry["complete_occupation_feasible"] = True
        if canon in seen_canon:
            occ.block_multiset(sol)
            entry["orbit_duplicate"] = True
            print("  complete occupation feasible but orbit duplicate; raw block added")
            history.append(entry)
            continue
        seen_canon.add(canon)

        fixed = run_fixed_u_sat(ms, args.outdir / "fixed_u", f"occ_iter{it:04d}", args.fixed_u_solver, args.fixed_u_timeout)
        solve = fixed.get("result", {}).get("solve", {})
        fixed_status = solve.get("status", "NO_RESULT")
        entry["fixed_u_sat"] = {
            "status": fixed_status,
            "elapsed_sec": solve.get("elapsed_sec"),
            "json_path": fixed.get("json_path"),
            "cnf_path": fixed.get("cnf_path"),
            "returncode": solve.get("returncode"),
        }
        tested_orbits.append({
            "iteration": it,
            "canonical": list(canon),
            "solution": {str(k): v for k, v in sorted(sol.items())},
            "fixed_u_status": fixed_status,
            "fixed_u_json": fixed.get("json_path"),
        })
        print(f"  COMPLETE occupation feasible; fixed-U {fixed_status}")
        if fixed_status == "SAT":
            conclusion = "FOUND_FIXED_U_SAT_NEEDS_MODEL_DECODE_VERIFY"
            witness = fixed.get("json_path")
            history.append(entry)
            break
        # Exclude this orbit and continue.
        imgs = orbit_images(sol, perms)
        for img in imgs:
            occ.block_multiset(img)
        entry["orbit_blocks_added"] = len(imgs)
        history.append(entry)
        print(f"  added {len(imgs)} orbit blocks for fixed-U {fixed_status}")

    if conclusion is None:
        conclusion = "ITERATION_LIMIT_REACHED"
    occ.delete()

    result = {
        "problem": "E11 rank-19 orbit-distinct occupation support enumeration plus fixed-U SAT",
        "field": "F2",
        "rank_s": args.rank,
        "meaning": "A fixed-U SAT witness gives an E11 rank-19 CPD and hence full T333 rank 22 over F2 after the verified +3 lift. An UNSAT support orbit excludes only that orbit unless every complete-occupation-feasible orbit is exhausted.",
        "cache": {"path": str(args.cache), "stats": cache.get("stats"), "lut_meta_brief": cache.get("lut_meta_brief")},
        "correct_quotient_perms": str(args.perms),
        "point_cap_distribution": dict(cap_counter),
        "cap2_points": cap2_points,
        "support_solver": args.support_solver,
        "initial_cut_count": sum(1 for r in cut_records if str(r["reason"]).startswith("initial_")),
        "final_cut_count": len(added_indices),
        "cuts_by_dim8": dict(Counter(r["dim8"] for r in cut_records)),
        "tested_complete_occupation_feasible_orbits": len(tested_orbits),
        "tested_orbits": tested_orbits,
        "conclusion": conclusion,
        "witness": witness,
        "history": history,
        "elapsed_sec": time.time() - t_all,
    }
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "conclusion": conclusion,
        "final_cut_count": len(added_indices),
        "tested_complete_occupation_feasible_orbits": len(tested_orbits),
        "witness": witness,
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))
    print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
