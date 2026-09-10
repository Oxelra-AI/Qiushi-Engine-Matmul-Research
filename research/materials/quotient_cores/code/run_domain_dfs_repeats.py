#!/usr/bin/env python3
"""Run domain-propagation DFS for all repeat-subset residual cases."""
import json, subprocess, time
from pathlib import Path

DFS = str(Path("scripts/e11_domain_dfs"))
REPEAT_DIR = Path("data/wang_native/repeats")
OUTDIR = Path("data/wang_native/domain_dfs_repeats")
OUTDIR.mkdir(parents=True, exist_ok=True)

with open(REPEAT_DIR / "residual_cap5_manifest.json") as f:
    manifest = json.load(f)

TIMEOUT = 120  # per case

def main():
    results = []
    all_empty = True
    total_time = 0.0
    
    for entry in manifest["summaries"]:
        subset = entry["repeat_subset"]
        target = entry["target_distinct_support_size"]
        bin_path = entry["binary_path"]
        valid = entry.get("valid_preload", True)
        
        name = "_".join(str(x) for x in subset)
        out = OUTDIR / f"repeat_{name}.json"
        exclude = ",".join(str(x) for x in subset)
        
        cmd = [
            DFS,
            "--constraints", bin_path,
            "--target", str(target),
            "--exclude", exclude,
            "--timeout", str(TIMEOUT),
            "--output", str(out),
        ]
        
        t0 = time.time()
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT + 30)
        wall = time.time() - t0
        total_time += wall
        
        try:
            with open(out) as f:
                r = json.load(f)
        except:
            r = {"error": "no output", "stderr": proc.stderr[-300:] if proc.stderr else ""}
        
        r["repeat_subset"] = subset
        r["wall_sec"] = wall
        results.append(r)
        
        complete = r.get("complete", False)
        sols = r.get("solutions", -1)
        calls = r.get("dfs_calls", -1)
        elapsed = r.get("elapsed_sec", wall)
        md = r.get("max_depth", -1)
        
        if sols > 0:
            all_empty = False
        
        status = "COMPLETE" if complete else "TIMEOUT"
        print(f"  R={str(subset):20s}: target={target:2d}, {status} {elapsed:8.4f}s, "
              f"calls={calls:>10}, sols={sols}, max_depth={md}")
    
    summary = {
        "all_empty": all_empty,
        "total_subsets": len(results),
        "total_time_sec": total_time,
        "results": results,
    }
    
    outpath = OUTDIR / "summary.json"
    with open(outpath, "w") as f:
        json.dump(summary, f, indent=2)
    
    print(f"\nAll empty: {all_empty}")
    print(f"Total time: {total_time:.3f}s")
    print(f"Saved {outpath}")

if __name__ == "__main__":
    main()
