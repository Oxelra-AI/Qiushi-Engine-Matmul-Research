#!/usr/bin/env python3
"""Positive and negative controls for the reusable E11 incremental fixed-A SAT model."""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path("scripts")
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from e11_capacity_incremental_sat import IncrementalFixedASAT  # noqa: E402


def row_terms(row, rank: int):
    vals = [int(x) for x in row.tolist()]
    return [tuple(vals[3 * i:3 * i + 3]) for i in range(rank)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--core", type=Path, default=Path("data/restricted_cores/mask_001_E11_core.npy"))
    ap.add_argument("--pool", type=Path, default=Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy"))
    ap.add_argument("--row", type=int, default=0)
    ap.add_argument("--solver", default="cadical195")
    ap.add_argument("--out", type=Path, default=Path("data/e11_capacity_sat/incremental_sat_controls.json"))
    args = ap.parse_args()
    t0 = time.time()

    pool = np.load(args.pool)
    rank21 = pool.shape[1] // 3
    terms = row_terms(pool[args.row], rank21)
    us21 = [u for u, v, w in terms]
    known_vs = [v for u, v, w in terms]
    known_ws = [w for u, v, w in terms]

    print(f"rank-21 positive support from {args.pool} row {args.row}: {us21}")
    sat21 = IncrementalFixedASAT(args.core, rank21, args.solver)
    known_ok, known_diff = sat21.verify(us21, known_vs, known_ws)
    res21 = sat21.solve_support(us21, None)
    if res21.get("status") == "SAT":
        out_npz = args.out.with_suffix(".rank21_control_solution.npz")
        sat21.save_npz(out_npz, res21["u_masks"], res21["v_masks"], res21["w_masks"])
        res21["solution_npz"] = str(out_npz)
    sat21.delete()
    print(f"rank-21 known assignment verified={known_ok} diff={known_diff}; solver status={res21.get('status')} verified={res21.get('verified')}")

    greedy19 = [1, 2, 3, 4, 8, 9, 12, 13, 16, 18, 20, 22, 24, 27, 28, 31, 32, 36, 42]
    sat19 = IncrementalFixedASAT(args.core, 19, args.solver)
    res19 = sat19.solve_support(greedy19, None)
    sat19.delete()
    print(f"rank-19 greedy fixed-A status={res19.get('status')} elapsed={res19.get('elapsed_sec'):.4f}s")

    result = {
        "purpose": "Control the reusable incremental fixed-A SAT model before using occupation-guided support enumeration.",
        "core": str(args.core),
        "solver": args.solver,
        "positive_rank21": {
            "pool": str(args.pool),
            "row": args.row,
            "rank": rank21,
            "u_masks": us21,
            "known_assignment_verified": known_ok,
            "known_assignment_diff_count": known_diff,
            "solver_result": {k: v for k, v in res21.items() if k not in ("v_masks", "w_masks")},
            "returned_v_masks": res21.get("v_masks"),
            "returned_w_masks": res21.get("w_masks"),
        },
        "negative_rank19_greedy": {
            "u_masks": greedy19,
            "solver_result": res19,
        },
        "elapsed_sec": time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"wrote {args.out}")

    if not known_ok or res21.get("status") != "SAT" or not res21.get("verified"):
        raise SystemExit("positive incremental SAT control failed")
    if res19.get("status") != "UNSAT":
        raise SystemExit("negative greedy control did not reproduce UNSAT")


if __name__ == "__main__":
    main()
