#!/usr/bin/env python3
"""Write SCIP LP file from quotient Wang binary and run SCIP.

255 binary variables. All Wang rows as upper-bound constraints. Sum = target.
"""
import struct, sys, time, subprocess, json
from pathlib import Path
from collections import Counter

MAGIC = b"E11WANG1"

def load_binary(path):
    d = open(path, "rb").read()
    assert d[:8] == MAGIC
    n = struct.unpack("<I", d[8:12])[0]
    REC = struct.calcsize("<BBHQQQQ")
    rows = []
    off = 12
    for _ in range(n):
        cap, dim8, pad, w0, w1, w2, w3 = struct.unpack_from("<BBHQQQQ", d, off)
        off += REC
        pts = []
        for wi, w in enumerate([w0, w1, w2, w3]):
            for b in range(64):
                if (w >> b) & 1:
                    pts.append(64 * wi + b)
        rows.append((cap, dim8, pts))
    return rows

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot-name", required=True)
    ap.add_argument("--binary", required=True)
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--time-limit", type=int, default=600)
    ap.add_argument("--max-dim", type=int, default=8, help="max dim of Wang rows to include")
    ap.add_argument("--qcut-file", default=None, help="JSON file with precomputed qcuts")
    ap.add_argument("--min-req", type=int, default=6, help="min requirement for qcuts")
    args = ap.parse_args()
    
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    
    rows = load_binary(args.binary)
    print(f"Loaded {len(rows)} rows from {args.binary}")
    
    cap_hist = Counter()
    binding = 0
    for c, d, p in rows:
        cap_hist[c] += 1
        if 0 < c < args.target:
            binding += 1
    print(f"Cap histogram: {dict(sorted(cap_hist.items()))}")
    print(f"Binding rows: {binding}")
    
    # Load qcuts if provided
    cuts = []
    if args.qcut_file:
        qdata = json.loads(open(args.qcut_file).read())
        for rec in qdata.get("top_cuts", []):
            if rec["req"] >= args.min_req:
                cuts.append(rec)
        print(f"Loaded {len(cuts)} qcuts with req >= {args.min_req}")
    
    # Write LP file
    lp_path = outdir / f"{args.pivot_name}_n{args.target}_d{args.max_dim}.lp"
    t0 = time.time()
    with open(lp_path, "w") as f:
        f.write(f"\\ {args.pivot_name} n={args.target} maxdim={args.max_dim}\n")
        f.write("Minimize\n obj: x1\n")
        f.write("Subject To\n")
        
        # Cardinality
        f.write(f" card: " + " + ".join(f"x{p}" for p in range(1, 256)) + f" = {args.target}\n")
        
        # Wang rows
        nw = 0
        for idx, (cap, dim8, pts) in enumerate(rows):
            if cap >= args.target or cap <= 0:
                continue
            if dim8 > args.max_dim:
                continue
            f.write(f" w{idx}: " + " + ".join(f"x{p}" for p in pts) + f" <= {cap}\n")
            nw += 1
        
        # Qcuts: sum_{p not in source_span} x_p >= R
        for ci, cut in enumerate(cuts):
            src = cut.get("source_span", [])
            outside = [p for p in range(1, 256) if p not in src and p not in [0]]
            R = cut["req"]
            f.write(f" qc{ci}: " + " + ".join(f"x{p}" for p in outside) + f" >= {R}\n")
        
        f.write("Bounds\n")
        f.write("Binary\n " + " ".join(f"x{p}" for p in range(1, 256)) + "\n")
        f.write("End\n")
    
    build_sec = time.time() - t0
    print(f"LP file: {lp_path} ({nw} Wang constraints, {len(cuts)} qcuts, {build_sec:.1f}s)")
    
    # Write SCIP settings
    set_path = outdir / "scip.set"
    with open(set_path, "w") as f:
        f.write(f"limits/time = {args.time_limit}\n")
        f.write("display/verblevel = 4\n")
        f.write("presolving/maxrounds = -1\n")
        # Enable aggressive cutting
        f.write("separating/maxroundsroot = -1\n")
        f.write("separating/maxstallroundsroot = 20\n")
    
    print(f"\nRunning SCIP (time limit {args.time_limit}s)...")
    t0 = time.time()
    result = subprocess.run(
        ["scip", "-s", str(set_path), "-f", str(lp_path)],
        capture_output=True, text=True, timeout=args.time_limit + 120,
    )
    elapsed = time.time() - t0
    
    stdout = result.stdout
    # Parse status
    status = "unknown"
    for line in stdout.split("\n"):
        ll = line.lower().strip()
        if "infeasible" in ll and "problem is solved" in ll:
            status = "infeasible"
        elif "optimal solution found" in ll and "problem is solved" in ll:
            status = "optimal"
        elif "time limit reached" in ll:
            status = "time_limit"
        elif "node limit reached" in ll:
            status = "node_limit"
    
    # Extract primal bound and dual bound
    primal = dual = None
    for line in stdout.split("\n"):
        if "Primal Bound" in line:
            primal = line.strip()
        if "Dual Bound" in line:
            dual = line.strip()
    
    # Extract solution
    sol_points = None
    if status == "optimal":
        sol_points = []
        for line in stdout.split("\n"):
            parts = line.strip().split()
            if len(parts) >= 2 and parts[0].startswith("x") and parts[0][1:].isdigit():
                try:
                    val = float(parts[1])
                    if val > 0.5:
                        sol_points.append(int(parts[0][1:]))
                except:
                    pass
    
    out = {
        "pivot_name": args.pivot_name,
        "target": args.target,
        "max_dim": args.max_dim,
        "status": status,
        "elapsed_sec": elapsed,
        "wang_constraints": nw,
        "qcut_constraints": len(cuts),
        "solution": sol_points,
        "primal_bound": primal,
        "dual_bound": dual,
        "stdout_tail": stdout[-6000:],
    }
    out_path = outdir / f"{args.pivot_name}_n{args.target}_d{args.max_dim}_result.json"
    with open(out_path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    
    print(f"\nStatus: {status}")
    print(f"Elapsed: {elapsed:.1f}s")
    if primal: print(f"  {primal}")
    if dual: print(f"  {dual}")
    if sol_points: print(f"  Solution: {sol_points}")
    print(f"Saved: {out_path}")


if __name__ == "__main__":
    main()
