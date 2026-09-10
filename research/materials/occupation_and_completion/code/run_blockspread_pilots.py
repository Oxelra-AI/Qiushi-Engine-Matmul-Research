#!/usr/bin/env python3
"""Run CaDiCaL pilots on block-spread augmented E11 branch CNFs."""
import subprocess, json, time, sys
from pathlib import Path

BASE = Path("data/core_sat/branches")
OUTDIR = Path("data/core_sat/pilots_blockspread_300s")
OUTDIR.mkdir(parents=True, exist_ok=True)

SECONDS = 300
SOLVER = "cadical"

def run_one(cnf_path, seconds, outdir):
    logfile = outdir / f"{cnf_path.stem}.{SOLVER}.{seconds}s.log"
    t0 = time.time()
    try:
        p = subprocess.run(
            [SOLVER, "-t", str(seconds), "-q", str(cnf_path)],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=seconds + 60
        )
        elapsed = time.time() - t0
        # Parse status
        status = "UNKNOWN"
        for line in (p.stdout + p.stderr).split('\n'):
            if 's SATISFIABLE' in line: status = "SAT"
            elif 's UNSATISFIABLE' in line: status = "UNSAT"
        logfile.write_text(p.stdout + "\n" + p.stderr)
        return {"cnf": str(cnf_path), "status": status, "returncode": p.returncode,
                "elapsed_sec": elapsed, "log": str(logfile)}
    except subprocess.TimeoutExpired:
        elapsed = time.time() - t0
        return {"cnf": str(cnf_path), "status": "PYTHON_TIMEOUT",
                "elapsed_sec": elapsed, "log": str(logfile)}

results = []
# Run on first 3 branches (smallest orbits: sizes 3, 3, 9)
for br in range(3):
    cnf = BASE / f"e11_rank19_branch{br}_bs.cnf"
    if not cnf.exists():
        print(f"SKIP {cnf} (not found)")
        continue
    print(f"[{br+1}/3] {SOLVER} {SECONDS}s {cnf.name}")
    rec = run_one(cnf, SECONDS, OUTDIR)
    results.append(rec)
    print(json.dumps(rec))
    sys.stdout.flush()

summary = {"solver": SOLVER, "seconds_per_instance": SECONDS,
           "total": len(results), "results": results}
(OUTDIR / "summary.json").write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({"completed": len(results), "summary": str(OUTDIR / "summary.json")}))
