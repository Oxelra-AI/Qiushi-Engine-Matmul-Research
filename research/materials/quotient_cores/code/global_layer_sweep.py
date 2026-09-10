#!/usr/bin/env python3
"""analysis: global CP-SAT sweeps by Wang row layer.

This tests whether simple global row layers suggested by face proof cores already
constrain the distinct 19-point E11 support problem, and rescans any subset
model against the complete 417,199-row Wang table.  Solver statuses are search
evidence only unless later replayed with CNF/DRAT/PB.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Callable

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints, complete_core_wang_scan  # noqa: E402
from cert_trace_separator import full_violation_scan  # noqa: E402
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis  # noqa: E402

LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
OUTDIR = ROOT / "workspace/data/global_layer_sweep"


def pts_from_rec(rec):
    # Use point_bitset because it is the direct complete-core incidence; fall back to key unpacking.
    if "point_bitset" in rec:
        pts = []
        bs = int(rec["point_bitset"])
        while bs:
            bit = bs & -bs
            pts.append(bit.bit_length())
            bs ^= bit
        return pts
    return subspace_points_from_basis(unpack_basis(int(rec["key8"])))


def build_selector(name: str):
    if name.startswith("Lge"):
        thr = int(name[3:])
        return lambda rec: int(rec["L"]) >= thr
    if name.startswith("Leq"):
        val = int(name[3:])
        return lambda rec: int(rec["L"]) == val
    if name.startswith("dimge"):
        thr = int(name[5:])
        return lambda rec: int(rec["dim8"]) >= thr
    if name.startswith("dimin"):
        vals = set(int(x) for x in name[5:].split("_") if x)
        return lambda rec: int(rec["dim8"]) in vals
    if name == "d6d7":
        return lambda rec: int(rec["dim8"]) in {6, 7}
    if name == "d5d6d7":
        return lambda rec: int(rec["dim8"]) in {5, 6, 7}
    if name == "primitive_like_high":
        return lambda rec: (int(rec["L"]) >= 17) or (int(rec["dim8"]) >= 6)
    raise ValueError(f"unknown family {name}")


def solve_family(records, name: str, selector: Callable, solver_time: float, workers: int, seed: int):
    from ortools.sat.python import cp_model
    t0 = time.time()
    model = cp_model.CpModel()
    points = list(range(1, 256))
    x = {p: model.NewBoolVar(f"x_{p}") for p in points}
    model.Add(sum(x[p] for p in points) == 19)
    row_count = 0
    by_L = Counter(); by_dim = Counter(); cap_hist = Counter(); size_hist = Counter(); skipped = 0
    for rec in records:
        if not selector(rec):
            continue
        L = int(rec["L"]); cap = 19 - L
        pts = pts_from_rec(rec)
        if len(pts) <= cap:
            skipped += 1
            continue
        model.Add(sum(x[p] for p in pts) <= cap)
        row_count += 1
        by_L[L] += 1; by_dim[int(rec["dim8"])] += 1; cap_hist[cap] += 1; size_hist[len(pts)] += 1
    # deterministic-looking objective to obtain reproducible models rather than arbitrary first hit
    model.Minimize(sum(((p * 37 + seed) % 997) * x[p] for p in points))
    build_sec = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(solver_time)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = int(seed)
    ts = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - ts
    status_name = solver.StatusName(status)
    out = {
        "name": name,
        "row_count": int(row_count),
        "skipped_trivial": int(skipped),
        "by_L": {str(k): int(v) for k, v in sorted(by_L.items())},
        "by_dim8": {str(k): int(v) for k, v in sorted(by_dim.items())},
        "cap_hist": {str(k): int(v) for k, v in sorted(cap_hist.items())},
        "row_size_hist": {str(k): int(v) for k, v in sorted(size_hist.items())},
        "build_sec": round(build_sec, 3),
        "status": status_name,
        "solve_sec": round(solve_sec, 3),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A = [p for p in points if solver.Value(x[p])]
        scan = complete_core_wang_scan(f"layer_{name}_solution", A, 19, records, max_head=20)
        fullscan = full_violation_scan(A, records, 19)
        out["solution"] = {
            "A_cols": A,
            "objective_value": float(solver.ObjectiveValue()),
            "complete_wang_violation_count": int(scan["complete_violation_count"]),
            "max_excess": scan.get("max_excess"),
            "violations_by_L": scan.get("violations_by_L"),
            "violations_by_dim8": scan.get("violations_by_dim8"),
            "first_violations": fullscan.get("violations", [])[:10],
        }
    out["elapsed_sec"] = round(time.time() - t0, 3)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--families", nargs="+", default=["Lge18", "Lge17", "Lge16", "Lge15", "d6d7", "d5d6d7", "primitive_like_high"])
    ap.add_argument("--solver-time", type=float, default=60.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=640264)
    args = ap.parse_args()
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    lut, lut_meta = load_lut(LUT_PATH)
    records, complete_meta = build_core_constraints(CoreQuotient(1), lut)
    results = []
    for i, name in enumerate(args.families):
        print("family", name, flush=True)
        res = solve_family(records, name, build_selector(name), args.solver_time, args.workers, args.seed + i)
        print(json.dumps({"name": name, "status": res["status"], "row_count": res["row_count"], "viol": res.get("solution", {}).get("complete_wang_violation_count"), "solve_sec": res["solve_sec"]}, sort_keys=True), flush=True)
        results.append(res)
    payload = {
        "schema": "global_layer_sweep_v1",
        "meaning": "Bounded global CP-SAT tests of simple Wang row layers on the distinct 19-point E11 support variables. FEASIBLE supports are rescanned against the complete table; statuses are not proofs without replayable certificates.",
        "parameters": {"families": args.families, "solver_time": args.solver_time, "workers": args.workers, "seed0": args.seed},
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "complete_meta": complete_meta,
        "results": results,
        "status_counts": {str(k): int(v) for k, v in sorted(Counter(r["status"] for r in results).items())},
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = OUTDIR / "global_layer_sweep.json"
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "status_counts": payload["status_counts"],
        "solutions": {r["name"]: r.get("solution", {}).get("complete_wang_violation_count") for r in results if "solution" in r},
        "elapsed_sec": payload["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
