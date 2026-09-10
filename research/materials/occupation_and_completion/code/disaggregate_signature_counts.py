#!/usr/bin/env python3
r"""analysis: disaggregate five-bit signature count solutions into actual A-supports.

Input count vectors come from signature_count_relaxation.py.  They satisfy the
min4 guarded shadow family and all Wang inequalities visible after quotienting
by the five incidence masks.  This script fixes one such 32-class count vector and asks
whether there is an actual 19-point support in F2^8 realizing it while satisfying the
full E11 Wang occupation table (or a chosen L threshold).  A feasible support would be
an A-side separation between complete Wang occupation and the shadow certificate; it
still would not imply B/C completion.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence

S0904_SCRIPTS = Path("scripts")
if str(S0904_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(S0904_SCRIPTS))
S0908_SCRIPTS = Path("scripts")
if str(S0908_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(S0908_SCRIPTS))

from shadow_guided_support_search import build_or_load_records, complete_scan  # type: ignore  # noqa:E402
from shadow_certificate_analysis import analyze_support, popparity  # type: ignore  # noqa:E402

ROOT = Path("research/research_record")
COUNT_PATH = ROOT / "workspace/data/shadow_certificate/signature_count_relaxation.json"
OUTDIR = ROOT / "workspace/data/shadow_certificate/signature_disaggregation"
MASKS = [9, 43, 53, 157, 234]
S = 19


def signature(p: int) -> int:
    sig = 0
    for i, m in enumerate(MASKS):
        if popparity(int(p) & int(m)):
            sig |= 1 << i
    return sig


def counts_from_dict(d: Dict[str, int]) -> List[int]:
    out = [0] * 32
    for k, v in d.items():
        out[int(k)] = int(v)
    return out


def load_count_vectors(path: Path) -> Dict[str, List[int]]:
    data = json.loads(path.read_text())
    vecs = {"source": counts_from_dict(data["source_signature_counts"])}
    for res in data["count_model_results"]:
        minL = int(res["min_L"])
        for i, sol in enumerate(res.get("solutions_recorded", [])[:10]):
            vecs[f"minL{minL}_sol{i}"] = counts_from_dict(sol["nonzero_counts"])
    return vecs


def solve_one(label: str, counts: Sequence[int], min_L: int, time_limit: float, workers: int, seed: int) -> dict:
    from ortools.sat.python import cp_model

    t0 = time.time()
    records, rmeta = build_or_load_records()
    model = cp_model.CpModel()
    points = list(range(1, 256))
    x = {p: model.NewBoolVar(f"x_{p}") for p in points}
    model.Add(sum(x.values()) == S)

    # Fix signature counts exactly.  Since x_p are Boolean and each class has enough
    # points according to the count relaxation, this is exact disaggregation.
    for sig in range(32):
        pts = [p for p in points if signature(p) == sig]
        model.Add(sum(x[p] for p in pts) == int(counts[sig]))

    wang_count = 0; wang_by_L = Counter(); wang_by_dim = Counter(); skipped = 0
    for rec in records:
        L = int(rec["L"])
        if min_L and L < min_L:
            skipped += 1
            continue
        cap = int(rec["cap"])
        if cap >= S:
            continue
        pts = [int(p) for p in rec["pts"] if p]
        if pts:
            model.Add(sum(x[p] for p in pts) <= cap)
            wang_count += 1; wang_by_L[L] += 1; wang_by_dim[int(rec["dim8"])] += 1

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = int(seed)
    ts = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - ts
    status_name = solver.StatusName(status)
    result = {
        "schema": "s0908_signature_count_disaggregation_v1",
        "field": "F2",
        "meaning": "Fixed-signature-count A-support disaggregation under full/threshold E11 Wang rows. Feasible is A-side support evidence only, not B/C completion.",
        "label": label,
        "counts": {str(i): int(v) for i, v in enumerate(counts) if int(v)},
        "min_L": int(min_L),
        "constraint_summary": {"wang_rows": int(wang_count), "wang_by_L": dict(sorted(wang_by_L.items())), "wang_by_dim8": dict(sorted(wang_by_dim.items())), "skipped_wang_rows": int(skipped)},
        "record_meta": rmeta,
        "time_limit": float(time_limit),
        "workers": int(workers),
        "seed": int(seed),
        "status": status_name,
        "solve_sec": round(solve_sec, 3),
        "total_elapsed_sec": round(time.time() - t0, 3),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        support = [p for p in points if solver.Value(x[p])]
        result["solution"] = {
            "support": support,
            "signature_counts": {str(i): sum(1 for p in support if signature(p) == i) for i in range(32) if sum(1 for p in support if signature(p) == i)},
            "complete_wang_scan": complete_scan(support, records),
            "shadow_summary": analyze_support("disaggregated_solution", support),
        }
    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--label", default="source", help="count-vector label; use --list to see labels")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--min-L", type=int, default=0, help="include all rows if 0, otherwise rows with L>=min_L")
    ap.add_argument("--time-limit", type=float, default=60.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=606)
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()
    vecs = load_count_vectors(COUNT_PATH)
    if args.list:
        print(json.dumps({"labels": sorted(vecs)}, indent=2))
        return
    if args.label not in vecs:
        raise SystemExit(f"unknown label {args.label}; available {sorted(vecs)[:20]} ...")
    res = solve_one(args.label, vecs[args.label], args.min_L, args.time_limit, args.workers, args.seed)
    out = args.out or (OUTDIR / f"disaggregate_{args.label}_L{args.min_L}_{int(args.time_limit)}s.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2, sort_keys=True) + "\n")
    short = {k: res[k] for k in ["label", "min_L", "status", "solve_sec", "constraint_summary"]}
    if "solution" in res:
        short["solution"] = {
            "support": res["solution"]["support"],
            "complete_wang_violation_count": res["solution"]["complete_wang_scan"]["violation_count"],
            "shadow_consistent": res["solution"]["shadow_summary"]["shadow_consistent"],
            "tight_rank9_count": res["solution"]["shadow_summary"]["tight_rank9_count"],
        }
    short["out"] = str(out)
    print(json.dumps(short, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
