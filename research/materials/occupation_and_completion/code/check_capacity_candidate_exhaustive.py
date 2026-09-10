#!/usr/bin/env python3
"""Exhaustively check a recorded occupation candidate against the full Wang LUT.

The lazy solvers normally check only subspaces spanned by subsets of the current
support.  That is enough after monotone lower-bound closure; for raw LUT values
an exhaustive scan is a useful guard.  This script scans all 8,283,458 subspaces
for a candidate saved in a lazy result JSON and reports any raw Wang constraint
violations.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import unpack_basis, in_rowspace  # noqa: E402


def load_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return payload["lut"], payload.get("meta", {})


def load_solution(result_path: Path, iteration: int | None):
    data = json.loads(result_path.read_text())
    iters = data.get("iterations", [])
    candidates = [e for e in iters if "solution" in e]
    if not candidates:
        raise ValueError("No solution candidates in result JSON")
    if iteration is None:
        entry = candidates[-1]
    else:
        entry = next(e for e in iters if e.get("iteration") == iteration and "solution" in e)
    sol = {int(k): int(v) for k, v in entry["solution"].items()}
    s = int(data.get("rank_s", sum(sol.values())))
    return data, entry, sol, s


def exhaustive_check(lut, sol, s, max_report):
    t0 = time.time()
    violations = []
    checked = 0
    by_dim_seen = Counter()
    by_lb_seen = Counter()
    occ_hist = Counter()
    support = list(sol.items())
    for key, lb in lut.items():
        basis = unpack_basis(key)
        occ = 0
        for p, mult in support:
            if in_rowspace(p, basis, n=9):
                occ += mult
        cap = s - lb
        occ_hist[(key & 0xF, lb, occ)] += 1
        by_dim_seen[key & 0xF] += 1
        by_lb_seen[lb] += 1
        if occ > cap:
            violations.append({
                "key": key,
                "dim": key & 0xF,
                "basis": list(basis),
                "lb": lb,
                "cap": cap,
                "occupancy": occ,
                "excess": occ - cap,
            })
        checked += 1
    violations.sort(key=lambda v: (v["excess"], v["lb"], v["occupancy"], -v["dim"]), reverse=True)
    stats = {
        "checked_subspaces": checked,
        "elapsed_sec": time.time() - t0,
        "violation_count": len(violations),
        "violations_by_dim": dict(Counter(v["dim"] for v in violations)),
        "violations_by_lb": dict(Counter(v["lb"] for v in violations)),
        "max_excess": max((v["excess"] for v in violations), default=0),
        "seen_by_dim": dict(by_dim_seen),
        "seen_by_lb": dict(by_lb_seen),
    }
    return violations[:max_report], stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("result_json", type=Path)
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--iteration", type=int, default=None)
    ap.add_argument("--max-report", type=int, default=200)
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()

    lut, meta = load_lut(args.lut)
    data, entry, sol, s = load_solution(args.result_json, args.iteration)
    print(f"Loaded LUT {len(lut):,}; candidate from iteration {entry.get('iteration')} with total multiplicity {sum(sol.values())}, support {len(sol)}, s={s}")
    violations, stats = exhaustive_check(lut, sol, s, args.max_report)
    print(json.dumps(stats, indent=2, sort_keys=True))
    payload = {
        "source_result_json": str(args.result_json),
        "source_iteration": entry.get("iteration"),
        "rank_s": s,
        "solution": {str(k): v for k, v in sorted(sol.items())},
        "stats": stats,
        "violations_head": violations,
        "lut_meta_brief": {"coverage_ok": meta.get("coverage_ok"), "conflict_count": meta.get("conflict_count"), "subspace_count": meta.get("subspace_count")},
    }
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"Saved {args.out}")


if __name__ == "__main__":
    main()
