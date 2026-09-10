#!/usr/bin/env python3
"""Enumerate the last A mask for a length-18 E11 prefix using reusable fixed-A SAT.

For a fixed 18-term A prefix, a rank-19 E11 CPD completion has exactly one
remaining nonzero A mask p in 1..255.  This script tests each full fixed-A list
prefix+[p] with the IncrementalFixedASAT model from e11_capacity_incremental_sat,
which keeps the Brent CNF in one PySAT solver and changes only A-bit assumptions.

If every p is UNSAT, the entire prefix subtree is refuted (solver-only unless
proof traces are produced separately).  SAT gives an exact E11 witness after
independent tensor reconstruction.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))

from e11_capacity_incremental_sat import IncrementalFixedASAT  # noqa: E402


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--core", type=Path, default=Path("data/restricted_cores/mask_001_E11_core.npy"))
    ap.add_argument("--prefix", required=True)
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--solver", default="cadical195")
    ap.add_argument("--conflicts", type=int, default=200000, help="per-candidate PySAT conflict budget; <=0 unlimited")
    ap.add_argument("--max-candidates", type=int, default=255)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    prefix = [int(x) for x in args.prefix.split(",") if x.strip()]
    if len(prefix) != args.rank - 1:
        raise ValueError(f"expected prefix length {args.rank-1}, got {len(prefix)}")
    t0 = time.time()
    sat = IncrementalFixedASAT(args.core, args.rank, args.solver)
    records = []
    witness = None
    status_counts: dict[str, int] = {}
    for idx, p in enumerate(range(1, 256), start=1):
        if idx > args.max_candidates:
            break
        ms = prefix + [p]
        rec = sat.solve_support(ms, timeout_conflicts=(None if args.conflicts <= 0 else args.conflicts))
        rec2 = {k: v for k, v in rec.items() if k not in {"v_masks", "w_masks"}}
        rec2["candidate_p"] = p
        rec2["candidate_index"] = idx
        records.append(rec2)
        st = rec.get("status", "UNKNOWN")
        status_counts[st] = status_counts.get(st, 0) + 1
        print(f"p={p:3d} status={st} elapsed={rec.get('elapsed_sec', 0):.3f}s")
        if st == "SAT" and rec.get("verified"):
            witness = {"candidate_p": p, "u_masks": ms, "v_masks": rec["v_masks"], "w_masks": rec["w_masks"], "diff_count": rec.get("diff_count")}
            break
    sat.delete()
    result = {
        "purpose": "exact one-mask enumeration for E11 rank-19 prefix completion",
        "field": "F2",
        "rank": args.rank,
        "core": str(args.core),
        "prefix": prefix,
        "prefix_size": len(prefix),
        "solver": args.solver,
        "conflicts_per_candidate": args.conflicts,
        "tested_candidates": len(records),
        "status_counts": status_counts,
        "witness": witness,
        "all_255_unsat": len(records) == 255 and status_counts.get("UNSAT", 0) == 255,
        "records": records,
        "elapsed_sec": time.time() - t0,
        "meaning": "If all_255_unsat is true, this solver run refutes every rank-19 E11 CPD containing the 18-term prefix; without proof traces it is still a solver certificate surface rather than a final mathematical proof.",
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in ["tested_candidates", "status_counts", "all_255_unsat", "elapsed_sec"]}, indent=2, sort_keys=True))
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
