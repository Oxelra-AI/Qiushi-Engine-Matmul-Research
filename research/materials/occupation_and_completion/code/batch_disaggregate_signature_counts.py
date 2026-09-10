#!/usr/bin/env python3
"""Batch selected fixed signature count disaggregation tests for analysis."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from disaggregate_signature_counts import load_count_vectors, solve_one, COUNT_PATH

OUT = Path("data/shadow_certificate/signature_disaggregation/batch_disaggregate_selected.json")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prefixes", default="minL0_sol,minL12_sol,minL13_sol,minL14_sol,minL15_sol")
    ap.add_argument("--per-prefix", type=int, default=3)
    ap.add_argument("--min-L", type=int, default=0)
    ap.add_argument("--time-limit", type=float, default=45.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--out", type=Path, default=OUT)
    args = ap.parse_args()
    vecs = load_count_vectors(COUNT_PATH)
    labels = []
    for pref in [p.strip() for p in args.prefixes.split(',') if p.strip()]:
        labels.extend([lab for lab in sorted(vecs) if lab.startswith(pref)][:args.per_prefix])
    results = []
    for i, lab in enumerate(labels):
        print(f"[{i+1}/{len(labels)}] {lab}", flush=True)
        res = solve_one(lab, vecs[lab], args.min_L, args.time_limit, args.workers, 700+i)
        results.append(res)
        print(f"  {res['status']} in {res['solve_sec']}s", flush=True)
    summary = {
        "schema": "s0908_batch_signature_disaggregation_v1",
        "min_L": args.min_L,
        "time_limit_per_label": args.time_limit,
        "labels": labels,
        "status_counts": {},
        "results": results,
    }
    for r in results:
        summary["status_counts"][r["status"]] = summary["status_counts"].get(r["status"], 0) + 1
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(args.out), "status_counts": summary["status_counts"], "labels": labels}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
