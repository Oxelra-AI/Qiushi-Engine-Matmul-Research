#!/usr/bin/env python3
"""analysis: canonical lift-bit feasibility for a fixed quotient support.

This reconstructs the full-tensor A-side Wang lift constraints from subspace
bases, not from the analysis exporters.  It uses the analysis quotient convention
(highest pivot bit deleted) and native point labels p=1..255.

For a fixed pivot q and quotient support S, variables eps_p choose the full lift
s(p)+eps_p*q.  We include full Wang rows of dimension <=3 and cap_20<=5 from
Wang's LUT.  q-containing rows are independent quotient-occupation checks;
non-q rows yield pseudo-Boolean constraints on the eps variables.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from collections import Counter
from itertools import combinations
from pathlib import Path
from typing import Iterable, Sequence

ROOT = Path("research/research_record")
S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, pack_basis, in_rowspace  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:  # pragma: no cover
    cp_model = None

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = ROOT / "workspace/data/quotient_lift"
OUTDIR.mkdir(parents=True, exist_ok=True)
PIVOTS = {"rank2": 17, "rank3": 273}
PEER_RANK2_SUPPORT = [1,3,9,33,99,128,132,144,148,160,184,189,192,198,209,215,224,249,254]


def sha_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def section_lift(qpoint: int, pivot: int) -> int:
    h = pivot.bit_length() - 1
    low = qpoint & ((1 << h) - 1)
    high = (qpoint >> h) << (h + 1)
    return low | high


def quotient_project(a: int, pivot: int) -> int:
    if a == 0 or a == pivot:
        return 0
    h = pivot.bit_length() - 1
    if (a >> h) & 1:
        a ^= pivot
    low = a & ((1 << h) - 1)
    high = (a >> (h + 1)) << h
    return low | high


def rref_subspace_bases(n: int, d: int) -> Iterable[tuple[int, ...]]:
    if d == 0:
        yield tuple()
        return
    for pivs_asc in combinations(range(n), d):
        pivs = tuple(sorted(pivs_asc, reverse=True))
        free_per_row = [[j for j in range(p) if j not in pivs] for p in pivs]
        total = sum(len(f) for f in free_per_row)
        for assignment in range(1 << total):
            rows = []
            bitpos = 0
            for p, free in zip(pivs, free_per_row):
                row = 1 << p
                for j in free:
                    if (assignment >> bitpos) & 1:
                        row |= 1 << j
                    bitpos += 1
                rows.append(row)
            yield tuple(rows)


def lut_lb(lut: dict, basis: Sequence[int]) -> int:
    rb = rref_basis(basis, n=9)
    key = int(pack_basis(rb))
    return int(lut[key])


def reduce_by_basis(x: int, basis: Sequence[int]) -> int:
    y = int(x)
    for b in basis:
        hb = int(b).bit_length() - 1
        if hb >= 0 and ((y >> hb) & 1):
            y ^= int(b)
    return y


def in_span_fast(x: int, basis: Sequence[int]) -> bool:
    return reduce_by_basis(x, basis) == 0


def constraint_to_readable(zmask: int, omask: int, support: list[int]) -> dict:
    zeros = [support[i] for i in range(len(support)) if (zmask >> i) & 1]
    ones = [support[i] for i in range(len(support)) if (omask >> i) & 1]
    return {"eps0_points": zeros, "eps1_points": ones, "active": len(zeros) + len(ones)}


def build_constraints(lut: dict, pivot: int, support: list[int], max_dim: int = 3, max_cap: int = 5) -> dict:
    support = list(support)
    nvars = len(support)
    lifts = [(section_lift(p, pivot), section_lift(p, pivot) ^ pivot) for p in support]
    best_constraints: dict[tuple[int, int], int] = {}
    source_head: dict[tuple[int, int], dict] = {}
    q_independent_violations = []
    stats = {
        "full_rows_considered": 0,
        "full_rows_cap_le_max_dim_le_max": 0,
        "q_containing_rows": 0,
        "nonq_rows": 0,
        "nonq_active_rows": 0,
        "nonq_tautological_rows": 0,
        "impossible_single_row": 0,
        "active_size_hist": Counter(),
        "cap_hist": Counter(),
        "dim_hist": Counter(),
        "pattern_kind_hist": Counter(),
    }
    for d in range(1, max_dim + 1):
        for basis in rref_subspace_bases(9, d):
            stats["full_rows_considered"] += 1
            lb = lut_lb(lut, basis)
            cap = 20 - lb
            if cap < 0 or cap > max_cap:
                continue
            stats["full_rows_cap_le_max_dim_le_max"] += 1
            stats["cap_hist"][cap] += 1
            stats["dim_hist"][d] += 1
            contains_q = in_span_fast(pivot, basis)
            if contains_q:
                stats["q_containing_rows"] += 1
                occ = 1  # distinguished pivot term
                pts = []
                for idx, (a0, a1) in enumerate(lifts):
                    b0 = in_span_fast(a0, basis)
                    b1 = in_span_fast(a1, basis)
                    # If q is in W, the two lift memberships should agree.
                    if b0 != b1:
                        raise AssertionError(("q-containing membership mismatch", pivot, basis, support[idx], b0, b1))
                    if b0:
                        occ += 1
                        pts.append(support[idx])
                if occ > cap:
                    q_independent_violations.append({
                        "dim": d,
                        "cap20": cap,
                        "occ_with_q": occ,
                        "projected_points": pts,
                        "basis": list(map(int, basis)),
                    })
                continue
            stats["nonq_rows"] += 1
            zmask = 0
            omask = 0
            active = 0
            for idx, (a0, a1) in enumerate(lifts):
                b0 = in_span_fast(a0, basis)
                b1 = in_span_fast(a1, basis)
                if b0 and b1:
                    raise AssertionError(("non-q row contains both lifts", pivot, basis, support[idx]))
                if b0:
                    zmask |= 1 << idx
                    active += 1
                elif b1:
                    omask |= 1 << idx
                    active += 1
            if active == 0:
                continue
            stats["nonq_active_rows"] += 1
            stats["active_size_hist"][active] += 1
            if active <= cap:
                stats["nonq_tautological_rows"] += 1
                continue
            key = (zmask, omask)
            if key not in best_constraints or cap < best_constraints[key]:
                best_constraints[key] = cap
                source_head[key] = {
                    "dim": d,
                    "cap20": cap,
                    "lb": lb,
                    "basis": list(map(int, basis)),
                    **constraint_to_readable(zmask, omask, support),
                }
    constraints = [(z, o, c) for (z, o), c in best_constraints.items()]
    constraints.sort(key=lambda t: (t[2], (t[0] | t[1]).bit_count(), t[0], t[1]))
    stats["dedup_constraints"] = len(constraints)
    stats["q_independent_violations"] = len(q_independent_violations)
    # Convert Counters.
    for k in ["active_size_hist", "cap_hist", "dim_hist", "pattern_kind_hist"]:
        stats[k] = {str(a): int(b) for a, b in sorted(stats[k].items())}  # type: ignore[index]
    return {
        "pivot": pivot,
        "support": support,
        "nvars": nvars,
        "constraints": constraints,
        "source_head": source_head,
        "q_independent_violations": q_independent_violations[:20],
        "stats": stats,
    }


def solve_cpsat(bundle: dict, time_limit: float = 120.0) -> dict:
    if cp_model is None:
        return {"solver": "ortools_unavailable", "status": "UNKNOWN"}
    support = bundle["support"]
    n = len(support)
    model = cp_model.CpModel()
    xs = [model.NewBoolVar(f"e_{p}") for p in support]
    for zmask, omask, cap in bundle["constraints"]:
        terms = []
        for i in range(n):
            if (zmask >> i) & 1:
                terms.append(1 - xs[i])
            if (omask >> i) & 1:
                terms.append(xs[i])
        if terms:
            model.Add(sum(terms) <= int(cap))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = 8
    status = solver.Solve(model)
    name = solver.StatusName(status)
    rec = {
        "solver": "ortools_cp_sat",
        "status": name,
        "wall_time": solver.WallTime(),
        "num_conflicts": solver.NumConflicts(),
        "num_branches": solver.NumBranches(),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        assignment = {str(support[i]): int(solver.Value(xs[i])) for i in range(n)}
        rec["assignment"] = assignment
        rec["assignment_bits_in_support_order"] = [int(solver.Value(xs[i])) for i in range(n)]
    return rec


def validate_assignment(bundle: dict, bits: list[int]) -> dict:
    n = len(bits)
    max_excess = 0
    violations = []
    for zmask, omask, cap in bundle["constraints"]:
        occ = 0
        for i, b in enumerate(bits):
            if ((zmask >> i) & 1) and b == 0:
                occ += 1
            if ((omask >> i) & 1) and b == 1:
                occ += 1
        if occ > cap:
            max_excess = max(max_excess, occ - cap)
            if len(violations) < 20:
                violations.append({"cap": cap, "occ": occ, "active": (zmask | omask).bit_count(), "zeros_idx": [i for i in range(n) if (zmask >> i) & 1], "ones_idx": [i for i in range(n) if (omask >> i) & 1]})
    return {"checked_constraints": len(bundle["constraints"]), "violation_count_head_limited": len(violations), "max_excess": max_excess, "violations_head": violations}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot-name", choices=["rank2", "rank3"], default="rank2")
    ap.add_argument("--support", type=str, default=",".join(map(str, PEER_RANK2_SUPPORT)))
    ap.add_argument("--time-limit", type=float, default=120.0)
    args = ap.parse_args()
    support = [int(x) for x in args.support.split(",") if x.strip()]
    pivot = PIVOTS[args.pivot_name]
    t0 = time.time()
    print(f"Loading LUT {LUT_PATH}")
    lut, meta = load_lut(LUT_PATH)
    print(f"Building canonical lift-bit constraints for {args.pivot_name}, pivot={pivot}, support size={len(support)}")
    bundle = build_constraints(lut, pivot, support)
    print(json.dumps({"stats": bundle["stats"], "q_independent_violations_head": bundle["q_independent_violations"][:3]}, indent=2, sort_keys=True))
    print("Solving CP-SAT...")
    sol = solve_cpsat(bundle, args.time_limit)
    print(json.dumps(sol, indent=2, sort_keys=True)[:5000])
    validation = None
    if "assignment_bits_in_support_order" in sol:
        validation = validate_assignment(bundle, sol["assignment_bits_in_support_order"])
        print("Validation:", json.dumps(validation, indent=2, sort_keys=True))
    out = {
        "schema": "s0908_canonical_lift_bit_feasibility_v1",
        "source_lut": str(LUT_PATH),
        "source_lut_sha256": sha_file(LUT_PATH),
        "lut_coverage_ok": meta.get("coverage_ok"),
        "pivot_name": args.pivot_name,
        "pivot": pivot,
        "support": support,
        "support_label": "peer_rank2_wang_admissible" if args.pivot_name == "rank2" and support == PEER_RANK2_SUPPORT else "custom",
        "stats": bundle["stats"],
        "q_independent_violations_head": bundle["q_independent_violations"],
        "constraints_head": [
            {"cap": c, **constraint_to_readable(z, o, support), "source": bundle["source_head"].get((z, o), {})}
            for z, o, c in bundle["constraints"][:50]
        ],
        "solve": sol,
        "assignment_validation": validation,
        "elapsed_sec": time.time() - t0,
    }
    out_path = OUTDIR / f"lift_bit_feasibility_{args.pivot_name}.json"
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(f"Saved {out_path} in {out['elapsed_sec']:.1f}s")


if __name__ == "__main__":
    main()
