#!/usr/bin/env python3
"""Quotient support feasibility via CP-SAT and PySAT/CaDiCaL.

255 binary variables. All Wang rows as cardinality constraints. Sum = target.
Uses OR-Tools CP-SAT for native cardinality propagation.
Also generates CNF via PySAT for CaDiCaL + DRAT proof.
"""
import struct, sys, time, json, argparse, subprocess
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


def solve_cpsat(rows, target, max_cap, time_limit):
    """Solve with OR-Tools CP-SAT."""
    from ortools.sat.python import cp_model
    
    model = cp_model.CpModel()
    x = {}
    for p in range(1, 256):
        x[p] = model.new_bool_var(f"x{p}")
    
    # Cardinality = target
    model.add(sum(x[p] for p in range(1, 256)) == target)
    
    # Wang rows
    nconstr = 0
    for cap, dim8, pts in rows:
        if cap <= 0 or cap >= target:
            continue
        if cap > max_cap:
            continue
        model.add(sum(x[p] for p in pts) <= cap)
        nconstr += 1
    
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = 4
    
    t0 = time.time()
    status = solver.solve(model)
    elapsed = time.time() - t0
    
    status_name = {
        cp_model.OPTIMAL: "OPTIMAL",
        cp_model.FEASIBLE: "FEASIBLE", 
        cp_model.INFEASIBLE: "INFEASIBLE",
        cp_model.MODEL_INVALID: "MODEL_INVALID",
        cp_model.UNKNOWN: "UNKNOWN",
    }.get(status, f"STATUS_{status}")
    
    sol = None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = [p for p in range(1, 256) if solver.value(x[p]) == 1]
    
    return {
        "status": status_name,
        "elapsed_sec": elapsed,
        "constraints": nconstr,
        "solution": sol,
        "num_booleans": solver.num_booleans,
        "num_conflicts": solver.num_conflicts,
        "num_branches": solver.num_branches,
        "wall_time": solver.wall_time,
    }


def generate_cnf_sequential(rows, target, max_cap, cnf_path):
    """Generate CNF with Sinz sequential counter for cardinality constraints.
    Returns (nvars, nclauses).
    """
    clauses = []
    next_var = 256  # vars 1..255 are point vars
    
    def at_most_k(pts, k):
        nonlocal next_var
        n = len(pts)
        if k >= n:
            return  # trivially satisfied
        if k == 0:
            for p in pts:
                clauses.append([-p])
            return
        if k == 1:
            # Pairwise exclusion
            for i in range(n):
                for j in range(i + 1, n):
                    clauses.append([-pts[i], -pts[j]])
            return
        # For small n and k close to n, direct encoding
        if n - k == 1:
            # At most n-1 of n: not all can be true
            clauses.append([-p for p in pts])
            return
        
        # Sinz sequential counter: register vars r[i][j] for i=0..n-1, j=0..k-1
        # r[i][j] = 1 iff at least j+1 of pts[0..i] are true
        r = [[0] * k for _ in range(n)]
        for i in range(n):
            for j in range(k):
                r[i][j] = next_var
                next_var += 1
        
        # Clauses:
        # 1. pts[0] => r[0][0]
        clauses.append([-pts[0], r[0][0]])
        # 2. NOT r[0][j] for j >= 1
        for j in range(1, k):
            clauses.append([-r[0][j]])
        
        for i in range(1, n):
            # pts[i] => r[i][0]
            clauses.append([-pts[i], r[i][0]])
            # r[i-1][0] => r[i][0]
            clauses.append([-r[i - 1][0], r[i][0]])
            
            for j in range(1, k):
                # pts[i] AND r[i-1][j-1] => r[i][j]
                clauses.append([-pts[i], -r[i - 1][j - 1], r[i][j]])
                # r[i-1][j] => r[i][j]
                clauses.append([-r[i - 1][j], r[i][j]])
            
            # pts[i] AND r[i-1][k-1] => false
            clauses.append([-pts[i], -r[i - 1][k - 1]])
    
    def exactly_k_of_all(k):
        """Encode sum(x1..x255) = k using two sequential counters."""
        nonlocal next_var
        pts = list(range(1, 256))
        # At most k
        at_most_k(pts, k)
        # At least k = at most (255-k) of negations
        # Encode: NOT(sum negx <= 255-k) = sum x >= k
        # Use: introduce negx[i] = NOT x[i] via Tseytin
        neg = []
        for p in pts:
            nv = next_var; next_var += 1
            clauses.append([-p, -nv])  # x => NOT negx
            clauses.append([p, nv])    # NOT x => negx
            neg.append(nv)
        at_most_k(neg, 255 - k)
    
    # Cardinality = target
    exactly_k_of_all(target)
    
    # Wang rows
    nwang = 0
    for cap, dim8, pts in rows:
        if cap <= 0 or cap >= target:
            continue
        if cap > max_cap:
            continue
        at_most_k(pts, cap)
        nwang += 1
    
    # Write CNF
    nvars = next_var - 1
    nclauses = len(clauses)
    with open(cnf_path, "w") as f:
        f.write(f"p cnf {nvars} {nclauses}\n")
        for c in clauses:
            f.write(" ".join(str(l) for l in c) + " 0\n")
    
    return nvars, nclauses, nwang


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot-name", required=True)
    ap.add_argument("--binary", required=True)
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--max-cap", type=int, default=18)
    ap.add_argument("--time-limit", type=int, default=300)
    ap.add_argument("--mode", choices=["cpsat", "sat", "both"], default="both")
    ap.add_argument("--max-dim", type=int, default=8)
    args = ap.parse_args()
    
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    
    rows = load_binary(args.binary)
    # Filter by max_dim
    if args.max_dim < 8:
        rows = [(c, d, p) for c, d, p in rows if d <= args.max_dim]
    print(f"Loaded {len(rows)} rows (max_dim={args.max_dim})")
    
    cap_hist = Counter(c for c, d, p in rows)
    print(f"Cap hist: {dict(sorted(cap_hist.items()))}")
    
    result = {"pivot_name": args.pivot_name, "target": args.target, "max_cap": args.max_cap}
    
    if args.mode in ("cpsat", "both"):
        print(f"\n=== CP-SAT (max_cap={args.max_cap}, time_limit={args.time_limit}s) ===")
        cpsat_result = solve_cpsat(rows, args.target, args.max_cap, args.time_limit)
        print(f"Status: {cpsat_result['status']}")
        print(f"Elapsed: {cpsat_result['elapsed_sec']:.1f}s")
        print(f"Constraints: {cpsat_result['constraints']}")
        print(f"Conflicts: {cpsat_result.get('num_conflicts')}")
        print(f"Branches: {cpsat_result.get('num_branches')}")
        if cpsat_result['solution']:
            print(f"Solution ({len(cpsat_result['solution'])} points): {cpsat_result['solution']}")
        result["cpsat"] = cpsat_result
    
    if args.mode in ("sat", "both"):
        # Use smaller max_cap for SAT to keep clause count manageable
        sat_max_cap = min(args.max_cap, 5)
        cnf_path = outdir / f"{args.pivot_name}_n{args.target}_cap{sat_max_cap}.cnf"
        drat_path = outdir / f"{args.pivot_name}_n{args.target}_cap{sat_max_cap}.drat"
        
        print(f"\n=== SAT/CNF (max_cap={sat_max_cap}) ===")
        nvars, nclauses, nwang = generate_cnf_sequential(rows, args.target, sat_max_cap, cnf_path)
        print(f"CNF: {nvars} vars, {nclauses} clauses, {nwang} Wang constraints")
        print(f"File: {cnf_path}")
        
        print(f"Running CaDiCaL (timeout {args.time_limit}s)...")
        t0 = time.time()
        try:
            proc = subprocess.run(
                ["cadical", str(cnf_path), str(drat_path)],
                capture_output=True, text=True, timeout=args.time_limit + 30,
            )
            elapsed = time.time() - t0
            sat = None
            if proc.returncode == 10:
                sat = True
            elif proc.returncode == 20:
                sat = False
            
            # Extract stats
            stats = {}
            for line in proc.stdout.split("\n"):
                for key in ["conflicts", "decisions", "propagations"]:
                    if f"c {key}" in line.lower():
                        stats[key] = line.strip()
            
            cadical_result = {
                "satisfiable": sat,
                "returncode": proc.returncode,
                "elapsed_sec": elapsed,
                "stats": stats,
            }
            print(f"CaDiCaL: sat={sat}, elapsed={elapsed:.1f}s, rc={proc.returncode}")
            for k, v in stats.items():
                print(f"  {v}")
            
            if sat is False:
                print("Running drat-trim for proof verification...")
                t0v = time.time()
                try:
                    vproc = subprocess.run(
                        ["drat-trim", str(cnf_path), str(drat_path)],
                        capture_output=True, text=True, timeout=600,
                    )
                    velapsed = time.time() - t0v
                    verified = "s VERIFIED" in vproc.stdout
                    cadical_result["drat_verified"] = verified
                    cadical_result["drat_elapsed_sec"] = velapsed
                    print(f"drat-trim: verified={verified}, elapsed={velapsed:.1f}s")
                except subprocess.TimeoutExpired:
                    cadical_result["drat_verified"] = None
                    cadical_result["drat_elapsed_sec"] = 600
                    print("drat-trim: timeout")
            
            if sat is True:
                # Extract solution
                sol = []
                for line in proc.stdout.split("\n"):
                    if line.startswith("v "):
                        for tok in line[2:].split():
                            v = int(tok)
                            if 1 <= v <= 255:
                                sol.append(v)
                cadical_result["solution"] = sol
                print(f"Solution ({len(sol)} points): {sol}")
            
            result["cadical"] = cadical_result
        
        except subprocess.TimeoutExpired:
            result["cadical"] = {"satisfiable": None, "elapsed_sec": args.time_limit, "error": "timeout"}
            print("CaDiCaL: timeout")
    
    out_path = outdir / f"{args.pivot_name}_n{args.target}_result.json"
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2, sort_keys=True)
    print(f"\nSaved: {out_path}")


if __name__ == "__main__":
    main()
