#!/usr/bin/env python3
"""Run corrected orbit-branch DFS for quotient Wang support searches.

Unlike the obsolete branch-binary generator, this script keeps the full quotient
row binary unchanged and passes earlier orbits as a forbidden initial domain to
wang_domain_dfs_safe.  It also forces the representative of the first occupied
orbit.  This preserves every Wang capacity row exactly.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
ORBIT_PATH = SESSION / "workspace/data/quotient_orbits/quotient_stabilizer_orbits.json"
BIN_DIR = SESSION / "workspace/data/wang_native/quotient_binaries"
DFS = SESSION / "workspace/scripts/wang_domain_dfs_safe"
OUT_DIR = SESSION / "workspace/data/wang_native/corrected_orbit_branch_runs"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def load_orbits(pivot_name: str) -> dict[str, Any]:
    data = json.loads(ORBIT_PATH.read_text())
    if pivot_name not in data:
        raise KeyError(pivot_name)
    return data[pivot_name]


def compile_dfs() -> None:
    cpp = SESSION / "workspace/scripts/wang_domain_dfs_safe.cpp"
    if not DFS.exists() or DFS.stat().st_mtime < cpp.stat().st_mtime:
        cmd = ["g++", "-O3", "-std=c++17", str(cpp), "-o", str(DFS)]
        subprocess.run(cmd, check=True)


def run_branch(pivot_name: str, target: int, branch: int, timeout: float, max_solutions: int) -> dict[str, Any]:
    pdata = load_orbits(pivot_name)
    orbits = pdata["orbits"]["orbits"]
    reps = pdata["orbits"]["representatives"]
    if branch < 0 or branch >= len(orbits):
        raise ValueError(f"bad branch {branch}")
    forbid = sorted({p for oi in range(branch) for p in orbits[oi]})
    rep = int(reps[branch])
    available = 255 - len(forbid)
    bin_path = BIN_DIR / f"{pivot_name}_all_n{target}.bin"
    if not bin_path.exists():
        raise FileNotFoundError(bin_path)
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    stem = f"{pivot_name}_n{target}_branch{branch}_corrected"
    out_json = OUT_DIR / f"{stem}.json"
    used_json = OUT_DIR / f"{stem}.used_rows.json"
    cmd = [
        str(DFS),
        "--constraints", str(bin_path),
        "--target", str(target),
        "--timeout", str(timeout),
        "--max-solutions", str(max_solutions),
        "--output", str(out_json),
        "--used-output", str(used_json),
        "--force-prefix", str(rep),
    ]
    if forbid:
        cmd.extend(["--forbid-set", ",".join(map(str, forbid))])
    t0 = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 30)
    elapsed = time.time() - t0
    result = json.loads(out_json.read_text()) if out_json.exists() else None
    rec: dict[str, Any] = {
        "pivot_name": pivot_name,
        "pivot": pdata["pivot"],
        "pivot_matrix_rank": pdata["pivot_matrix_rank"],
        "stabilizer_size": pdata["stabilizer_size"],
        "target": target,
        "branch": branch,
        "representative": rep,
        "orbit_size": len(orbits[branch]),
        "forbidden_count": len(forbid),
        "available_points_before_cap0": available,
        "constraints_binary": str(bin_path),
        "constraints_sha256": sha256(bin_path),
        "dfs_binary": str(DFS),
        "dfs_cpp_sha256": sha256(SESSION / "workspace/scripts/wang_domain_dfs_safe.cpp"),
        "command": cmd,
        "returncode": proc.returncode,
        "wall_elapsed_sec": elapsed,
        "stdout": proc.stdout[-4000:],
        "stderr": proc.stderr[-4000:],
        "result_json": str(out_json),
        "used_rows_json": str(used_json),
        "result": result,
    }
    return rec


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot-name", choices=["rank2", "rank3"], required=True)
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--branches", default="all", help="comma list or all")
    ap.add_argument("--timeout", type=float, default=120.0)
    ap.add_argument("--max-solutions", type=int, default=1)
    ap.add_argument("--out-name", default=None)
    args = ap.parse_args()

    compile_dfs()
    pdata = load_orbits(args.pivot_name)
    nbranches = len(pdata["orbits"]["orbits"])
    if args.branches == "all":
        branches = list(range(nbranches))
    else:
        branches = [int(x) for x in args.branches.split(",") if x.strip()]

    records = []
    for b in branches:
        print(f"Running {args.pivot_name} branch {b}/{nbranches-1} with corrected forbid-domain branching...", flush=True)
        rec = run_branch(args.pivot_name, args.target, b, args.timeout, args.max_solutions)
        r = rec.get("result") or {}
        print(f"  complete={r.get('complete')} timeout={r.get('timeout')} sols={r.get('solutions')} calls={r.get('dfs_calls')} max_depth={r.get('max_depth')} domain_after_forbid={r.get('initial_domain_after_forbid')}", flush=True)
        records.append(rec)

    summary = {
        "schema": "corrected_quotient_orbit_branch_dfs_v1",
        "pivot_name": args.pivot_name,
        "target": args.target,
        "branches_requested": branches,
        "records": records,
        "aggregate": {
            "branches": len(records),
            "complete_zero_solution": sum(1 for rec in records if rec.get("result", {}).get("complete") and rec.get("result", {}).get("solutions") == 0),
            "early_solution_stop": sum(1 for rec in records if rec.get("result", {}).get("early_solution_stop")),
            "timeouts": sum(1 for rec in records if rec.get("result", {}).get("timeout")),
            "solutions_seen": sum(int(rec.get("result", {}).get("solutions") or 0) for rec in records),
        },
    }
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    out_name = args.out_name or f"{args.pivot_name}_n{args.target}_branches_{args.branches.replace(',', '_')}_{int(args.timeout)}s_summary.json"
    out_path = OUT_DIR / out_name
    out_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(out_path), "aggregate": summary["aggregate"]}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
