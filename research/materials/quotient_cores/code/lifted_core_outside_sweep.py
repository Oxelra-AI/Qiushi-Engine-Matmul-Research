#!/usr/bin/env python3
"""analysis: sweep outside-J budgets for the lifted J65 proof-core rows.

This is a CP-SAT exploratory sweep, not a proof.  It uses the 9,469 lifted full
Wang rows extracted from the analysis J-face proof input core and tests whether a
19-support can satisfy them with at most k outside-J points.  Feasible supports
are rescanned against the complete 417,199-row table to see whether the proof-core
rows are only local or already near the full occupation problem.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from complete_core_and_transversal import ROOT, build_core_constraints, complete_core_wang_scan  # noqa: E402
from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from lifted_core_escape_analysis import load_row_list, solve_model  # noqa: E402

LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
OUTDIR = ROOT / "workspace/data/lifted_jcore"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=5)
    ap.add_argument("--time", type=float, default=90.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=631001)
    args = ap.parse_args()
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    J, outside, rows = load_row_list()
    lut, lut_meta = load_lut(LUT_PATH)
    records, complete_meta = build_core_constraints(CoreQuotient(1), lut)
    results = []
    for k in range(args.kmax + 1):
        print("testing k", k, flush=True)
        r = solve_model(rows, J, outside, "max_outside", k, None, args.time, args.seed + k, args.workers)
        if r.get("A_cols"):
            scan = complete_core_wang_scan(f"lifted_core_budget{k}_solution", r["A_cols"], 19, records, max_head=20)
            r["complete_wang_scan_brief"] = scan
        results.append({"k": k, **r})
        print({"k": k, "status": r.get("status"), "outside": r.get("outside_selected_count"), "selected": r.get("outside_selected"), "complete_violations": r.get("complete_wang_scan_brief", {}).get("complete_violation_count"), "solve_sec": r.get("solve_sec")}, flush=True)
    out = OUTDIR / "lifted_core_outside_sweep.json"
    payload = {
        "schema": "lifted_core_outside_sweep_v1",
        "meaning": "CP-SAT exploratory sweep over outside-J budgets for the 9,469 lifted Wang rows extracted from the J65 proof input core. Statuses are not replayable certificates; feasible rows are rescanned against the complete table.",
        "J_size": len(J),
        "outside_size": len(outside),
        "row_count": len(rows),
        "parameters": {"kmax": args.kmax, "time": args.time, "workers": args.workers, "seed": args.seed},
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "complete_meta": complete_meta,
        "results": results,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "summary": [{"k": r["k"], "status": r.get("status"), "outside": r.get("outside_selected_count"), "complete_violations": r.get("complete_wang_scan_brief", {}).get("complete_violation_count"), "solve_sec": r.get("solve_sec")} for r in results],
        "elapsed_sec": payload["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
