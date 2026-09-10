#!/usr/bin/env python3
"""CEGAR loop for quotient support feasibility.

Start with cap<=3 rows, iteratively add violated rows until
either INFEASIBLE or a fully Wang-admissible support is found.
"""
import struct, sys, time, json, argparse
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
                if (w >> b) & 1:
                    pts.append(64 * wi + b)
        rows.append((cap, dim8, pts))
    return rows


def check_support(sol_set, rows, target):
    """Check solution against all rows. Return list of violated row indices."""
    violations = []
    for idx, (cap, dim8, pts) in enumerate(rows):
        if cap <= 0 or cap >= target:
            continue
        occ = sum(1 for p in pts if p in sol_set)
        if occ > cap:
            violations.append(idx)
    return violations


def solve_round(rows, target, active_indices, time_limit, prev_sol=None):
    """Run CP-SAT on active constraints."""
    from ortools.sat.python import cp_model
    
    model = cp_model.CpModel()
    x = {}
    for p in range(1, 256):
        x[p] = model.new_bool_var(f"x{p}")
    
    model.add(sum(x[p] for p in range(1, 256)) == target)
    
    for idx in active_indices:
        cap, dim8, pts = rows[idx]
        model.add(sum(x[p] for p in pts) <= cap)
    
    # If previous solution exists, add diversity cut to avoid it
    if prev_sol:
        # Force at least one change
        model.add(
            sum(x[p] for p in prev_sol) + sum(1 - x[p] for p in range(1, 256) if p not in prev_sol) <= 
            len(prev_sol) + (255 - len(prev_sol)) - 1
        )
    
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = 4
    
    t0 = time.time()
    status = solver.solve(model)
    elapsed = time.time() - t0
    
    status_name = {0: "UNKNOWN", 1: "MODEL_INVALID", 2: "FEASIBLE", 3: "INFEASIBLE", 4: "OPTIMAL"}
    sn = status_name.get(status, f"STATUS_{status}")
    
    sol = None
    if status in (2, 4):  # FEASIBLE or OPTIMAL
        sol = sorted(p for p in range(1, 256) if solver.value(x[p]) == 1)
    
    return {
        "status": sn,
        "elapsed_sec": elapsed,
        "active_constraints": len(active_indices),
        "conflicts": solver.num_conflicts,
        "branches": solver.num_branches,
        "solution": sol,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot-name", required=True)
    ap.add_argument("--binary", required=True)
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--initial-cap", type=int, default=3)
    ap.add_argument("--max-rounds", type=int, default=50)
    ap.add_argument("--time-limit-per-round", type=int, default=120)
    ap.add_argument("--total-time-limit", type=int, default=1200)
    args = ap.parse_args()
    
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    
    rows = load_binary(args.binary)
    print(f"Loaded {len(rows)} rows")
    
    # Initial active set: all rows with cap <= initial_cap
    active = set()
    for idx, (cap, dim8, pts) in enumerate(rows):
        if 0 < cap <= args.initial_cap and cap < args.target:
            active.add(idx)
    
    print(f"Initial active constraints (cap<={args.initial_cap}): {len(active)}")
    
    rounds = []
    total_t0 = time.time()
    
    for rnd in range(args.max_rounds):
        total_elapsed = time.time() - total_t0
        if total_elapsed > args.total_time_limit:
            print(f"Total time limit reached ({total_elapsed:.0f}s)")
            break
        
        remaining = args.total_time_limit - total_elapsed
        tl = min(args.time_limit_per_round, remaining)
        
        print(f"\n--- Round {rnd} ({len(active)} constraints, {tl:.0f}s budget) ---")
        result = solve_round(rows, args.target, active, tl)
        print(f"  Status: {result['status']}, elapsed: {result['elapsed_sec']:.1f}s, conflicts: {result['conflicts']}")
        
        if result['status'] == 'INFEASIBLE':
            print(f"\n*** INFEASIBLE at round {rnd}! ***")
            print(f"  Active constraints: {len(active)}")
            rounds.append({"round": rnd, **result, "violations_added": 0})
            break
        
        if result['status'] in ('UNKNOWN', 'MODEL_INVALID'):
            print(f"  Solver returned {result['status']}, stopping")
            rounds.append({"round": rnd, **result, "violations_added": 0})
            break
        
        sol = result['solution']
        if sol is None:
            rounds.append({"round": rnd, **result, "violations_added": 0})
            break
        
        print(f"  Solution: {sol}")
        
        # Check against ALL rows
        sol_set = set(sol)
        violations = check_support(sol_set, rows, args.target)
        print(f"  Full check: {len(violations)} violations")
        
        if len(violations) == 0:
            print(f"\n*** FULLY WANG-ADMISSIBLE SUPPORT FOUND at round {rnd}! ***")
            print(f"  Support: {sol}")
            rounds.append({"round": rnd, **result, "violations_added": 0, "fully_admissible": True})
            break
        
        # Add violated rows
        new_added = 0
        for v in violations:
            if v not in active:
                active.add(v)
                new_added += 1
        print(f"  Added {new_added} new constraints (total active: {len(active)})")
        
        # Record violation distribution
        viol_caps = Counter(rows[v][0] for v in violations)
        print(f"  Violation cap hist: {dict(sorted(viol_caps.items()))}")
        
        rounds.append({
            "round": rnd,
            **result,
            "violations_total": len(violations),
            "violations_added": new_added,
            "violation_cap_hist": dict(sorted(viol_caps.items())),
        })
    
    total_elapsed = time.time() - total_t0
    final_status = rounds[-1]["status"] if rounds else "no_rounds"
    fully_admissible = any(r.get("fully_admissible") for r in rounds)
    
    summary = {
        "pivot_name": args.pivot_name,
        "target": args.target,
        "initial_cap": args.initial_cap,
        "total_rounds": len(rounds),
        "final_status": final_status,
        "fully_admissible": fully_admissible,
        "final_active_constraints": len(active),
        "total_elapsed_sec": total_elapsed,
        "rounds": rounds,
    }
    
    out_path = outdir / f"{args.pivot_name}_n{args.target}_cegar.json"
    with open(out_path, "w") as f:
        json.dump(summary, f, indent=2, sort_keys=True)
    
    print(f"\n=== Summary ===")
    print(f"Rounds: {len(rounds)}")
    print(f"Final status: {final_status}")
    print(f"Fully admissible: {fully_admissible}")
    print(f"Total elapsed: {total_elapsed:.1f}s")
    print(f"Saved: {out_path}")


if __name__ == "__main__":
    main()
