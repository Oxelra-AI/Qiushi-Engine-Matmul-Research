#!/usr/bin/env python3
"""Run CaDiCaL with a non-binary DRAT trace on an existing CNF and verify it.

This small execution helper avoids shell redirection so managed/background runs
can write a stable proof object, logs, status JSON, and hashes.  It does not
interpret the mathematical formula; callers must connect the CNF metadata to the
research claim.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path


def sha256(path: Path) -> str | None:
    if not path.exists() or not path.is_file():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(4 * 1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_log(path: Path) -> dict:
    if not path.exists():
        return {"exists": False}
    text = path.read_text(errors="replace")
    out = {"exists": True}
    m = re.findall(r"^s (\S+)", text, re.M)
    if m:
        out["sat_status"] = m[-1]
    m = re.findall(r"c exit ([-0-9]+)", text)
    if m:
        out["exit_line"] = int(m[-1])
    m = re.search(r"found 'p cnf (\d+) (\d+)' header", text)
    if m:
        out["parsed_header"] = {"vars": int(m.group(1)), "clauses": int(m.group(2))}
    m = re.search(r"parsing input formula with (\d+) variables and (\d+) clauses", text)
    if m:
        out["trim_parsed_header"] = {"vars": int(m.group(1)), "clauses": int(m.group(2))}
    out["verified"] = "s VERIFIED" in text
    m = re.search(r"verification time:\s*([0-9.]+) seconds", text)
    if m:
        out["verification_time_sec"] = float(m.group(1))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cnf", type=Path, required=True)
    ap.add_argument("--outdir", type=Path, required=True)
    ap.add_argument("--stem", default=None)
    ap.add_argument("--meta", type=Path, default=None)
    ap.add_argument("--time-limit", type=int, default=0)
    ap.add_argument("--skip-solver", action="store_true")
    ap.add_argument("--skip-trim", action="store_true")
    args = ap.parse_args()

    args.outdir.mkdir(parents=True, exist_ok=True)
    stem = args.stem or args.cnf.stem
    drat = args.outdir / f"{stem}.drat"
    cad_log = args.outdir / f"{stem}.cadical.log"
    trim_log = args.outdir / f"{stem}.drat_trim.log"
    status_path = args.outdir / f"{stem}.status.json"

    status = {
        "cnf": str(args.cnf),
        "meta": None if args.meta is None else str(args.meta),
        "drat": str(drat),
        "cadical_log": str(cad_log),
        "drat_trim_log": str(trim_log),
    }

    if not args.skip_solver:
        cmd = ["cadical", "--unsat", "--binary=false", "-n"]
        if args.time_limit > 0:
            cmd.extend(["-t", str(args.time_limit)])
        cmd.extend([str(args.cnf), str(drat)])
        t0 = time.time()
        with cad_log.open("w") as log:
            proc = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, text=True)
        status["cadical_exit"] = proc.returncode
        status["cadical_elapsed_sec"] = time.time() - t0
    else:
        status["cadical_exit"] = None
        status["cadical_elapsed_sec"] = None

    if not args.skip_trim and drat.exists() and (args.skip_solver or status.get("cadical_exit") == 20):
        t1 = time.time()
        with trim_log.open("w") as log:
            trim = subprocess.run(["drat-trim", str(args.cnf), str(drat)], stdout=log, stderr=subprocess.STDOUT, text=True)
        status["drat_trim_exit"] = trim.returncode
        status["drat_trim_elapsed_sec"] = time.time() - t1
    else:
        status["drat_trim_exit"] = None
        status["drat_trim_elapsed_sec"] = None

    paths = [args.cnf, drat, cad_log, trim_log, status_path]
    if args.meta is not None:
        paths.append(args.meta)
    status["file_info"] = {
        str(p): {"exists": p.exists(), "size": p.stat().st_size if p.exists() else None, "sha256": sha256(p) if p.exists() else None}
        for p in paths
    }
    status["cadical_log_parse"] = parse_log(cad_log)
    status["drat_trim_log_parse"] = parse_log(trim_log)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps(status, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
