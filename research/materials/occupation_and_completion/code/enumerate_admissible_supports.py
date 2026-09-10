#!/usr/bin/env python3
"""Enumerate multiple Wang-admissible supports via randomized CEGAR.

For each trial, randomize CP-SAT search to find diverse supports.
Then check each against all Wang rows.
"""
import struct, sys, time, json, random
from collections import Counter
from pathlib import Path

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
                if (w >> b) & 1: pts.append(64*wi+b)
        rows.append((cap, dim8, pts))
    return rows

def check_support(sol_set, rows, target):
    viols = []
    for idx, (cap, dim8, pts) in enumerate(rows):
        if cap <= 0 or cap >= target: continue
        occ = sum(1 for p in pts if p in sol_set)
        if occ > cap: viols.append(idx)
    return viols

def find_admissible_support(rows, target, time_limit, seed, known_supports=None):
    """CEGAR to find one Wang-admissible support with random seed."""
    from ortools.sat.python import cp_model
    
    # Build initial active set (cap<=3)
    active = set()
    for idx, (cap, dim8, pts) in enumerate(rows):
        if 0 < cap <= 3 and cap < target:
            active.add(idx)
    
    t0 = time.time()
    for rnd in range(100):
        if time.time() - t0 > time_limit:
            return None, "timeout"
        
        model = cp_model.CpModel()
        x = {p: model.new_bool_var(f"x{p}") for p in range(1, 256)}
        model.add(sum(x[p] for p in range(1, 256)) == target)
        
        for idx in active:
            cap, dim8, pts = rows[idx]
            model.add(sum(x[p] for p in pts) <= cap)
        
        # Exclude known supports
        if known_supports:
            for ks in known_supports:
                # Hamming distance >= 1
                model.add(sum(x[p] for p in ks) <= len(ks) - 1)
        
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = min(120, time_limit - (time.time() - t0))
        solver.parameters.num_workers = 4
        solver.parameters.random_seed = seed + rnd
        
        status = solver.solve(model)
        
        if status == 3:  # INFEASIBLE
            return None, "infeasible"
        if status not in (2, 4):  # not FEASIBLE/OPTIMAL
            continue
        
        sol = sorted(p for p in range(1, 256) if solver.value(x[p]) == 1)
        sol_set = set(sol)
        
        viols = check_support(sol_set, rows, target)
        if len(viols) == 0:
            return sol, "admissible"
        
        for v in viols:
            active.add(v)
    
    return None, "rounds_exhausted"


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot-name", required=True)
    ap.add_argument("--binary", required=True)
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--n-trials", type=int, default=20)
    ap.add_argument("--time-per-trial", type=int, default=120)
    args = ap.parse_args()
    
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    
    rows = load_binary(args.binary)
    print(f"Loaded {len(rows)} rows")
    
    found_supports = []
    t0 = time.time()
    
    for trial in range(args.n_trials):
        seed = 42 + trial * 7
        print(f"\nTrial {trial} (seed={seed})...")
        sol, status = find_admissible_support(
            rows, args.target, args.time_per_trial, seed,
            known_supports=found_supports
        )
        print(f"  Status: {status}")
        if sol:
            print(f"  Support: {sol}")
            found_supports.append(sol)
        
        if status == "infeasible":
            print(f"\n*** INFEASIBLE: No more Wang-admissible supports ***")
            break
    
    elapsed = time.time() - t0
    print(f"\n=== Found {len(found_supports)} Wang-admissible supports in {elapsed:.1f}s ===")
    
    result = {
        "pivot_name": args.pivot_name,
        "target": args.target,
        "n_trials": args.n_trials,
        "supports_found": len(found_supports),
        "supports": found_supports,
        "elapsed_sec": elapsed,
    }
    out_path = outdir / f"{args.pivot_name}_n{args.target}_multi.json"
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2, sort_keys=True)
    print(f"Saved: {out_path}")


if __name__ == "__main__":
    main()
