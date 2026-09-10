#!/usr/bin/env python3
"""Run CaDiCaL on a fixed-E11 branch CNF and decode a SAT witness to A-points.

The fixed-E11 CNFs use variables 1..m for the branch point universe, in the
same order as wang_capacity_cnf_e11_fixed.py: all projective points 1..511
except earlier Stab(E11)-orbit points.  Auxiliary variables from cardinality
encodings have indices > m and are ignored.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import List, Set

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_cnf_e11_fixed import stab_e11_orbits, E11  # noqa: E402
from wang_capacity_lazy import matrix_rank_of_mask  # noqa: E402


def branch_points(second_rep: int, exclude_orbits_before: bool = True) -> List[int]:
    fixed = {E11, second_rep}
    excluded: Set[int] = set()
    if exclude_orbits_before and second_rep != E11:
        seen = False
        for orb in stab_e11_orbits():
            if orb["rep"] == second_rep:
                seen = True
                break
            excluded.update(int(p) for p in orb["members"])
        if not seen:
            raise ValueError(f"{second_rep} is not a Stab(E11) representative")
        excluded -= fixed
    return [p for p in range(1, 512) if p not in excluded]


def parse_model(log_path: Path, points: List[int]) -> dict:
    positives = []
    status = None
    with log_path.open("r", errors="replace") as f:
        for line in f:
            if line.startswith("s "):
                status = line.strip()
            elif line.startswith("v "):
                for tok in line.split()[1:]:
                    if tok == "0":
                        continue
                    val = int(tok)
                    if val > 0 and val <= len(points):
                        positives.append(val)
    support = [points[v - 1] for v in sorted(set(positives))]
    return {
        "solver_status_line": status,
        "positive_original_vars": sorted(set(positives)),
        "support": support,
        "support_size": len(support),
        "support_rank_hist": dict(sorted(Counter(matrix_rank_of_mask(p) for p in support).items())),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cnf", type=Path, required=True)
    ap.add_argument("--second-rep", type=int, required=True)
    ap.add_argument("--log", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--time-limit", type=int, default=300)
    ap.add_argument("--reuse-log", action="store_true")
    args = ap.parse_args()

    pts = branch_points(args.second_rep, True)
    payload = {"cnf": str(args.cnf), "second_rep": args.second_rep, "variable_point_count": len(pts), "points_head": pts[:20], "points_tail": pts[-20:]}
    if not args.reuse_log:
        args.log.parent.mkdir(parents=True, exist_ok=True)
        cmd = ["cadical", "-t", str(args.time_limit), str(args.cnf)]
        t0 = time.time()
        with args.log.open("w") as log:
            proc = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, text=True)
        payload["cadical_exit"] = proc.returncode
        payload["cadical_elapsed_sec"] = time.time() - t0
    dec = parse_model(args.log, pts)
    payload.update(dec)
    payload["support_dict"] = {str(p): 1 for p in payload["support"]}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: payload[k] for k in ["cadical_exit", "cadical_elapsed_sec", "solver_status_line", "support_size", "support_rank_hist", "support"] if k in payload}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
