#!/usr/bin/env python3
"""Run one lazy no-saturation support search for analysis with longer CP-SAT budget."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path("research/research_record")
for P in (ROOT / "workspace/scripts", Path("scripts")):
    if str(P) not in sys.path:
        sys.path.insert(0, str(P))

from trace_saturation_gate import (  # noqa: E402
    CORES,
    build_or_load_core_cache,
    contraction_ranks,
    core_raw_summary,
    load_lut,
    solve_lazy_support_problem,
)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--core", choices=list(CORES), default="E11")
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--solver-time", type=float, default=60.0)
    ap.add_argument("--max-iters", type=int, default=30)
    ap.add_argument("--max-add-per-iter", type=int, default=5000)
    ap.add_argument("--initial-dim", type=int, default=2)
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--cache-dir", type=Path, default=ROOT / "workspace/data/trace_saturation_gate/cache")
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()
    lut, _meta = load_lut(args.lut)
    cfg = CORES[args.core]
    raw, _T, c_ranks, inv_qs, nu = core_raw_summary(args.core, cfg["pivot_mask"])
    cache = build_or_load_core_cache(args.core, cfg["pivot_mask"], args.rank, lut, args.cache_dir, rebuild=False)
    res = solve_lazy_support_problem(
        args.core,
        "no_saturation_long_lazy",
        args.rank,
        cache,
        c_ranks,
        inv_qs,
        nu,
        max_iters=args.max_iters,
        solver_time=args.solver_time,
        max_add_per_iter=args.max_add_per_iter,
        initial_dim=args.initial_dim,
        include_direct_rank=True,
        no_saturation=True,
        objective=None,
    )
    out = args.out or (ROOT / f"workspace/data/trace_saturation_gate/no_saturation_long_lazy_{args.core}.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"raw_gate": raw, "search": res}, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "core": args.core,
        "status": res["final_status"],
        "elapsed_sec": res["elapsed_sec"],
        "iters": len(res["iterations"]),
        "cuts": res["total_wang_cuts_added"],
        "final_stats": None if res["final_support_stats"] is None else {
            "sum_nu": res["final_support_stats"]["sum_nu"],
            "rank9_saturated_count": res["final_support_stats"]["rank9_saturated_count"],
            "rank9_hit_histogram": res["final_support_stats"]["rank9_hit_histogram"],
        },
        "tail": res["iterations"][-3:],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
