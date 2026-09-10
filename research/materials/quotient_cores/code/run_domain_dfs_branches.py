#!/usr/bin/env python3
"""Run domain-propagation DFS on all 8 orbit branches and collect results."""
import json, subprocess, time, sys
from pathlib import Path

DFS = Path("scripts/e11_domain_dfs")
CONS = Path("data/wang_native/e11_wang_cap5.bin")
ORBITS = Path("data/e11_orbits/e11_quotient_orbits.json")
OUTDIR = Path("data/wang_native/domain_dfs_cap5")
OUTDIR.mkdir(parents=True, exist_ok=True)

REPS = [1, 4, 5, 8, 10, 40, 42, 80]
TIMEOUT = int(sys.argv[1]) if len(sys.argv) > 1 else 3600

def main():
    results = []
    total_solutions = 0
    all_complete = True
    
    for branch, rep in enumerate(REPS):
        out = OUTDIR / f"branch{branch}_rep{rep}.json"
        cmd = [
            str(DFS),
            "--constraints", str(CONS),
            "--target", "19",
            "--branch", str(branch),
            "--branch-rep", str(rep),
            "--orbits", str(ORBITS),
            "--timeout", str(TIMEOUT),
            "--output", str(out),
        ]
        t0 = time.time()
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT + 60)
        wall = time.time() - t0
        
        try:
            with open(out) as f:
                r = json.load(f)
        except:
            r = {"branch": branch, "rep": rep, "error": "no output", 
                 "stderr": proc.stderr[-500:] if proc.stderr else ""}
        
        r["wall_sec"] = wall
        results.append(r)
        
        complete = r.get("complete", False)
        sols = r.get("solutions", -1)
        calls = r.get("dfs_calls", -1)
        elapsed = r.get("elapsed_sec", wall)
        md = r.get("max_depth", -1)
        
        total_solutions += max(0, sols)
        if not complete:
            all_complete = False
        
        status = "COMPLETE" if complete else "TIMEOUT"
        print(f"Branch {branch} (rep={rep:3d}): {status} {elapsed:10.3f}s, "
              f"calls={calls:>15,}, sols={sols}, max_depth={md}")
    
    summary = {
        "all_complete": all_complete,
        "total_solutions": total_solutions,
        "timeout_per_branch": TIMEOUT,
        "branches": len(results),
        "results": results,
    }
    
    sumpath = OUTDIR / "summary.json"
    with open(sumpath, "w") as f:
        json.dump(summary, f, indent=2)
    
    print(f"\nAll complete: {all_complete}")
    print(f"Total solutions: {total_solutions}")
    print(f"Saved {sumpath}")

if __name__ == "__main__":
    main()
