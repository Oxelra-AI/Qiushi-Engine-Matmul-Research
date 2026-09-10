#!/usr/bin/env python3
"""Run bounded SAT pilots for E11 core rank-19 CNFs and record solver evidence.

This is not a proof-producing run. It is a triage experiment: detect quick SAT
witnesses or quick UNSAT branches and measure whether the sound certified/orbit
branch encodings are in easy or hard regimes. Any UNSAT that matters later must
be rerun with proof logging and verified independently.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import time
from pathlib import Path


def classify(stdout: str, returncode: int) -> str:
    if "s SATISFIABLE" in stdout:
        return "SAT"
    if "s UNSATISFIABLE" in stdout:
        return "UNSAT"
    if "UNKNOWN" in stdout or returncode == 0:
        return "UNKNOWN"
    return f"OTHER_{returncode}"


def run_one(solver: str, cnf: Path, seconds: int, outdir: Path) -> dict:
    stem = cnf.stem
    log = outdir / f"{stem}.{solver}.{seconds}s.log"
    t0 = time.time()
    if solver == "cadical":
        cmd = ["cadical", "-q", "-t", str(seconds), str(cnf)]
    elif solver == "kissat":
        # Kissat on this runtime does not expose a --time option; use the Python
        # subprocess timeout and suppress the satisfying assignment with -n.
        cmd = ["kissat", "-n", str(cnf)]
    else:
        raise ValueError(solver)
    try:
        p = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=seconds + 30)
        elapsed = time.time() - t0
        text = p.stdout + ("\nSTDERR:\n" + p.stderr if p.stderr else "")
        log.write_text(text)
        status = classify(p.stdout, p.returncode)
        return {"cnf": str(cnf), "solver": solver, "seconds_limit": seconds, "returncode": p.returncode,
                "status": status, "elapsed_sec": elapsed, "log": str(log)}
    except subprocess.TimeoutExpired as e:
        elapsed = time.time() - t0
        stdout = e.stdout.decode(errors="replace") if isinstance(e.stdout, (bytes, bytearray)) else (e.stdout or "")
        stderr = e.stderr.decode(errors="replace") if isinstance(e.stderr, (bytes, bytearray)) else (e.stderr or "")
        text = stdout + "\nPYTHON_TIMEOUT\n" + stderr
        log.write_text(text)
        return {"cnf": str(cnf), "solver": solver, "seconds_limit": seconds, "returncode": None,
                "status": "PYTHON_TIMEOUT", "elapsed_sec": elapsed, "log": str(log)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cnf-dir", type=Path, default=Path("data/core_sat/branches"))
    ap.add_argument("--base-cnf", type=Path, default=Path("data/core_sat/e11_rank19_certified.cnf"))
    ap.add_argument("--outdir", type=Path, required=True)
    ap.add_argument("--seconds", type=int, default=60)
    ap.add_argument("--solver", choices=["cadical", "kissat"], default="cadical")
    ap.add_argument("--include-base", action="store_true")
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    cnfs = []
    if args.include_base:
        cnfs.append(args.base_cnf)
    cnfs.extend(sorted(args.cnf_dir.glob("e11_rank19_branch*.cnf")))
    records = []
    t0 = time.time()
    for i, cnf in enumerate(cnfs, 1):
        print(f"[{i}/{len(cnfs)}] {args.solver} {args.seconds}s {cnf}", flush=True)
        rec = run_one(args.solver, cnf, args.seconds, args.outdir)
        print(json.dumps({k: rec[k] for k in ["status", "returncode", "elapsed_sec", "cnf"]}, sort_keys=True), flush=True)
        records.append(rec)
        summary = {"purpose": "bounded non-proof SAT pilot for E11 core rank-19 certified/orbit CNFs",
                   "solver": args.solver, "seconds_per_instance": args.seconds,
                   "completed": len(records), "total": len(cnfs), "records": records,
                   "elapsed_sec": time.time() - t0}
        (args.outdir / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
