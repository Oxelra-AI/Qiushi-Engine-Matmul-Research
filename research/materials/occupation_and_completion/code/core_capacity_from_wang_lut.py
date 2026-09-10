#!/usr/bin/env python3
"""Core-level Wang occupation capacity tests derived from the full T-level LUT.

For a pivot p in F2^9, the codimension-one core is the restriction of
T_<3,3,3> to V/<p> on the A side (equivalently, impose the corresponding
one-dimensional Wang constraint and project away the pivot direction).

A rank-s decomposition of the core with projective A-factors q_t in F2^8\0
must satisfy, for every subspace Psi <= F2^8,

    #{t : q_t in Psi\0} <= s - L_T(span(p, lift(Psi))).

This script loads the complete expanded Wang lower-bound LUT built by
wang_capacity_lazy.py and tests these finite occupation systems lazily.  A
feasible output only says that Wang's occupation table alone does not exclude
that A-factor support.  An infeasible output for s=19 proves the corresponding
core rank is at least 20 over F2, but by itself does not prove T-level rank >=21.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

# Make same-directory imports work when called from the user root.
SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import (  # noqa: E402
    load_qmm_a_factors,
    pack_basis,
    rref_basis,
    rref_key,
    unpack_basis,
    in_rowspace,
    subspace_points_from_basis,
)

PIVOTS = {
    "E11": 1,
    "E12_E21": 10,
    "E13_E22_E31": 84,
}


def load_lut(path: Path) -> Tuple[Dict[int, int], dict]:
    with path.open("rb") as f:
        payload = pickle.load(f)
    return payload["lut"], payload.get("meta", {})


class CoreQuotient:
    def __init__(self, pivot: int):
        if pivot <= 0 or pivot >= (1 << 9):
            raise ValueError(f"bad pivot {pivot}")
        self.pivot = pivot
        self.pivot_bit = (pivot & -pivot).bit_length() - 1
        self.comp_bits = [i for i in range(9) if i != self.pivot_bit]
        assert len(self.comp_bits) == 8

    def lift8(self, q: int) -> int:
        v = 0
        for k, bit in enumerate(self.comp_bits):
            if (q >> k) & 1:
                v |= 1 << bit
        return v

    def project9(self, a: int) -> int:
        """Project a 9-bit vector modulo span(pivot) into the chosen complement."""
        v = a
        if (v >> self.pivot_bit) & 1:
            v ^= self.pivot
        if (v >> self.pivot_bit) & 1:
            raise AssertionError("pivot reduction failed")
        q = 0
        for k, bit in enumerate(self.comp_bits):
            if (v >> bit) & 1:
                q |= 1 << k
        return q

    def key9_from_key8(self, key8: int) -> int:
        rows8 = unpack_basis(key8)
        rows9 = [self.pivot] + [self.lift8(r) for r in rows8]
        return rref_key(rows9, n=9)

    def key8_from_rows(self, rows: Sequence[int]) -> int:
        return pack_basis(rref_basis(rows, n=8))


def all_subset_span_keys_core(support: Sequence[int]) -> List[int]:
    m = len(support)
    basis_by_mask = {0: tuple()}
    keys = set()
    for mask in range(1, 1 << m):
        lb = mask & -mask
        j = lb.bit_length() - 1
        prev = mask ^ lb
        b = rref_basis(list(basis_by_mask[prev]) + [support[j]], n=8)
        basis_by_mask[mask] = b
        keys.add(pack_basis(b))
    return list(keys)


def occupancy_key8(key8: int, sol: Dict[int, int]) -> int:
    basis = unpack_basis(key8)
    return sum(c for p, c in sol.items() if in_rowspace(p, basis, n=8))


def check_core_solution(sol: Dict[int, int], s: int, core: CoreQuotient, lut: Dict[int, int], max_report: int = 50) -> Tuple[List[dict], dict]:
    support = sorted(sol)
    t0 = time.time()
    keys8 = all_subset_span_keys_core(support)
    violations = []
    for key8 in keys8:
        key9 = core.key9_from_key8(key8)
        lb = lut[key9]
        occ = occupancy_key8(key8, sol)
        cap = s - lb
        if occ > cap:
            violations.append({
                "key8": key8,
                "basis8": list(unpack_basis(key8)),
                "key9": key9,
                "basis9": list(unpack_basis(key9)),
                "dim8": key8 & 0xF,
                "dim9": key9 & 0xF,
                "lb": lb,
                "cap": cap,
                "occupancy": occ,
                "excess": occ - cap,
            })
    violations.sort(key=lambda v: (v["excess"], v["lb"], v["occupancy"], -v["dim8"]), reverse=True)
    stats = {
        "support_size": len(support),
        "total_multiplicity": sum(sol.values()),
        "unique_subset_spans": len(keys8),
        "violation_count": len(violations),
        "violations_by_dim8": dict(Counter(v["dim8"] for v in violations)),
        "violations_by_lb": dict(Counter(v["lb"] for v in violations)),
        "elapsed_sec": time.time() - t0,
    }
    return violations[:max_report], stats


def add_core_cut(model, x: Dict[int, object], key8: int, core: CoreQuotient, lut: Dict[int, int], s: int, added: set, records: list, reason: str) -> bool:
    if key8 in added:
        return False
    key9 = core.key9_from_key8(key8)
    lb = lut[key9]
    cap = s - lb
    pts = subspace_points_from_basis(unpack_basis(key8))
    model.Add(sum(x[p] for p in pts) <= cap)
    added.add(key8)
    records.append({"key8": key8, "dim8": key8 & 0xF, "key9": key9, "dim9": key9 & 0xF, "lb": lb, "cap": cap, "point_count": len(pts), "reason": reason})
    return True


def solve_core_lazy(core_name: str, pivot: int, lut: Dict[int, int], s: int, outdir: Path, max_iters: int, solver_time: float, init_dim2: bool = True) -> dict:
    from ortools.sat.python import cp_model

    core = CoreQuotient(pivot)
    model = cp_model.CpModel()
    points = list(range(1, 256))
    x = {p: model.NewIntVar(0, s, f"x_{p}") for p in points}
    model.Add(sum(x[p] for p in points) == s)

    added = set()
    cuts = []
    # Initial one-dimensional point constraints, plus optionally all 2D lines.
    for q in points:
        key8 = core.key8_from_rows([q])
        add_core_cut(model, x, key8, core, lut, s, added, cuts, "all_dim1_initial")
    if init_dim2:
        # Enumerate all 2D subspaces as spans of pairs; rref_key removes duplicates.
        all_dim2 = set()
        for a in points:
            for b in range(a + 1, 256):
                key8 = core.key8_from_rows([a, b])
                if (key8 & 0xF) == 2:
                    all_dim2.add(key8)
        for key8 in sorted(all_dim2):
            add_core_cut(model, x, key8, core, lut, s, added, cuts, "all_dim2_initial")
    print(f"Core {core_name} s={s}: initial cuts={len(added)} by dim {dict(Counter(c['dim8'] for c in cuts))}")

    history = []
    final_status = None
    final_solution = None
    for it in range(1, max_iters + 1):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = solver_time
        solver.parameters.num_search_workers = 8
        solver.parameters.random_seed = 2000 + it
        t0 = time.time()
        status = solver.Solve(model)
        elapsed = time.time() - t0
        status_name = {
            cp_model.OPTIMAL: "OPTIMAL",
            cp_model.FEASIBLE: "FEASIBLE",
            cp_model.INFEASIBLE: "INFEASIBLE",
            cp_model.MODEL_INVALID: "MODEL_INVALID",
            cp_model.UNKNOWN: "UNKNOWN",
        }.get(status, str(status))
        entry = {"iteration": it, "solver_status": status_name, "cut_count": len(added), "solve_elapsed_sec": elapsed}
        print(f"Core {core_name} s={s} iter {it}: status={status_name}, cuts={len(added)}, elapsed={elapsed:.2f}s")
        if status in (cp_model.INFEASIBLE, cp_model.MODEL_INVALID):
            final_status = status_name
            history.append(entry)
            break
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            final_status = status_name
            history.append(entry)
            break
        sol = {p: solver.Value(var) for p, var in x.items() if solver.Value(var)}
        entry["solution"] = {str(k): v for k, v in sorted(sol.items())}
        entry["support_size"] = len(sol)
        entry["max_mult"] = max(sol.values()) if sol else 0
        violations, stats = check_core_solution(sol, s, core, lut, max_report=5000)
        entry["check_stats"] = stats
        entry["violations_head"] = violations[:20]
        print(f"  support={len(sol)} max_mult={entry['max_mult']} spans={stats['unique_subset_spans']:,} violations={stats['violation_count']:,} check={stats['elapsed_sec']:.2f}s")
        if not violations:
            final_status = "CAPACITY_FEASIBLE_NO_VIOLATION_FOUND"
            final_solution = sol
            history.append(entry)
            break
        nadd = 0
        for v in violations:
            if add_core_cut(model, x, v["key8"], core, lut, s, added, cuts, f"lazy_iter_{it}"):
                nadd += 1
        entry["lazy_cuts_added"] = nadd
        print(f"  added {nadd} cuts")
        history.append(entry)
        if nadd == 0:
            final_status = "STALLED_NO_NEW_CUTS"
            final_solution = sol
            break

    result = {
        "problem": "core Wang occupation capacity",
        "field": "F2",
        "core_name": core_name,
        "pivot_mask": pivot,
        "rank_s": s,
        "meaning": "Infeasible at s=19 proves this core has F2 rank at least 20. Feasible means Wang occupation constraints alone admit an A-factor multiset for a rank-s core decomposition; B/C factors still need solving.",
        "final_status": final_status,
        "final_solution": {str(k): v for k, v in sorted(final_solution.items())} if final_solution else None,
        "iterations": history,
        "cut_count": len(added),
        "cuts_by_dim8": dict(Counter(c["dim8"] for c in cuts)),
        "cuts_by_lb": dict(Counter(c["lb"] for c in cuts)),
        "cut_records_head": cuts[:100],
        "cut_records_tail": cuts[-100:],
    }
    outdir.mkdir(parents=True, exist_ok=True)
    outpath = outdir / f"core_capacity_{core_name}_s{s}.json"
    outpath.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Saved {outpath}")
    return result


def check_cn122_core_restrictions(lut: Dict[int, int]) -> dict:
    qmm = Path("data/cn122_3x3_r23_repro/scheme.qmm")
    factors9 = load_qmm_a_factors(qmm)
    out = {}
    for name, pivot in PIVOTS.items():
        core = CoreQuotient(pivot)
        qs = [core.project9(a) for a in factors9]
        surviving = [q for q in qs if q]
        sol = dict(Counter(surviving))
        violations, stats = check_core_solution(sol, len(surviving), core, lut, max_report=20)
        out[name] = {
            "pivot_mask": pivot,
            "cn122_restricted_length": len(surviving),
            "distinct_A_factors": len(sol),
            "max_multiplicity": max(sol.values()) if sol else 0,
            "A_factor_multiset": {str(k): v for k, v in sorted(sol.items())},
            "check_stats": stats,
            "violations_head": violations,
        }
        print(f"cn122 restriction {name}: len={len(surviving)} distinct={len(sol)} maxmult={out[name]['max_multiplicity']} violations={stats['violation_count']}")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--outdir", type=Path, default=Path("data/core_capacity"))
    ap.add_argument("--check-cn122", action="store_true")
    ap.add_argument("--core", choices=list(PIVOTS) + ["all"], default="all")
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--max-iters", type=int, default=50)
    ap.add_argument("--solver-time", type=float, default=120.0)
    ap.add_argument("--no-dim2-initial", action="store_true")
    ap.add_argument("--solve", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    lut, meta = load_lut(args.lut)
    args.outdir.mkdir(parents=True, exist_ok=True)
    print(f"Loaded LUT: {len(lut):,} subspaces; coverage_ok={meta.get('coverage_ok')} conflicts={meta.get('conflict_count')}")
    summary = {"lut_meta": meta, "cn122_core_checks": None, "solve_results": []}

    if args.check_cn122:
        summary["cn122_core_checks"] = check_cn122_core_restrictions(lut)
        (args.outdir / "cn122_core_capacity_checks.json").write_text(json.dumps(summary["cn122_core_checks"], indent=2, sort_keys=True) + "\n")

    if args.solve:
        todo = list(PIVOTS.items()) if args.core == "all" else [(args.core, PIVOTS[args.core])]
        for name, pivot in todo:
            res = solve_core_lazy(name, pivot, lut, args.rank, args.outdir, args.max_iters, args.solver_time, init_dim2=not args.no_dim2_initial)
            summary["solve_results"].append({k: v for k, v in res.items() if k not in ("iterations",)})

    summary["elapsed_sec"] = time.time() - t0
    (args.outdir / "core_capacity_summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(f"Saved summary to {args.outdir / 'core_capacity_summary.json'}")


if __name__ == "__main__":
    main()
