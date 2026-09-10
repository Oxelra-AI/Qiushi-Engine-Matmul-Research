#!/usr/bin/env python3
"""Point-level MILP: 510 binary variables for pivot-fixed full Wang + rank constraint.

Uses original Wang constraints (not orbit-averaged) for selected rows,
plus the rank-sum lower bound from the flattening. This is the EXACT
necessary condition at the point level, not a relaxation.

Strategy: start with cap<=3 rows (~2.6M), solve MILP, check full rows, CEGAR.
"""
from __future__ import annotations
import argparse, json, os, struct, sys, time
from pathlib import Path
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds as SPBounds, linprog
from scipy.sparse import lil_matrix, csr_matrix

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from quotient_line_caps_and_controls import bits_to_mat, gf2_rank_mat

MAGIC = b"WANG512\x01"

def bit_in(words, p):
    return bool((int(words[p >> 6]) >> (p & 63)) & 1)

def points_in_words(words):
    pts = []
    for wi, w0 in enumerate(words):
        w = int(w0)
        while w:
            lb = w & -w; b = lb.bit_length()-1; p = wi*64+b
            if 1 <= p <= 511: pts.append(p)
            w ^= lb
    return pts

def load_binary_rows(path, max_cap=None):
    with path.open("rb") as f:
        magic = f.read(8); assert magic == MAGIC
        nrows = struct.unpack("<I", f.read(4))[0]
        for idx in range(nrows):
            cap, dim, _res = struct.unpack("<BBH", f.read(4))
            words = struct.unpack("<8Q", f.read(64))
            if max_cap is not None and cap > max_cap:
                continue
            yield idx, int(cap), int(dim), tuple(int(w) for w in words)

def matrix_rank(a):
    return int(gf2_rank_mat(bits_to_mat(int(a))))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", type=Path, required=True)
    ap.add_argument("--pivot", type=int, required=True)
    ap.add_argument("--length", type=int, default=20)
    ap.add_argument("--max-cap-initial", type=int, default=3)
    ap.add_argument("--milp-time", type=int, default=120)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    pivot = args.pivot
    length = args.length
    pivot_rank = matrix_rank(pivot)
    rank_threshold = 27 - pivot_rank

    # Map non-pivot points to variable indices 0..509
    all_points = [a for a in range(1, 512) if a != pivot]
    pt2var = {a: i for i, a in enumerate(all_points)}
    nvar = len(all_points)
    ranks = np.array([matrix_rank(a) for a in all_points], dtype=float)

    print(f"Pivot={pivot}, rank={pivot_rank}, threshold={rank_threshold}, vars={nvar}")
    print(f"  Rank distribution: rank1={int(np.sum(ranks==1))}, rank2={int(np.sum(ranks==2))}, rank3={int(np.sum(ranks==3))}")

    # Load Wang rows with cap <= max_cap_initial
    print(f"Loading rows with cap <= {args.max_cap_initial}...")
    # Use lil_matrix for efficient row-by-row construction
    row_data = []  # (cap, dim, point_set) for full check later
    A_rows = []
    b_vals = []
    for idx, cap, dim, words in load_binary_rows(args.binary, max_cap=args.max_cap_initial):
        pcont = bit_in(words, pivot)
        rhs = cap - (1 if pcont else 0)
        pts = [a for a in points_in_words(words) if a != pivot]
        if not pts and rhs >= 0:
            continue
        if rhs < 0:
            print(f"  Negative RHS: row {idx}, cap={cap}, dim={dim}, p_contains={pcont}")
            continue
        row = np.zeros(nvar, dtype=np.int8)
        for a in pts:
            row[pt2var[a]] = 1
        A_rows.append(row)
        b_vals.append(float(rhs))

    A_wang = np.array(A_rows, dtype=float)
    b_wang = np.array(b_vals, dtype=float)
    print(f"  Loaded {len(A_rows)} constraints in {time.time()-t0:.1f}s")

    # === LP relaxation: minimize rank sum ===
    A_eq = np.ones((1, nvar), dtype=float)
    b_eq = np.array([float(length - 1)], dtype=float)
    bounds = [(0.0, 1.0)] * nvar
    
    t1 = time.time()
    res_lp = linprog(ranks, A_ub=A_wang, b_ub=b_wang, A_eq=A_eq, b_eq=b_eq,
                     bounds=bounds, method="highs")
    lp_time = time.time() - t1
    print(f"\n=== LP min rank sum (cap<={args.max_cap_initial}) ===")
    print(f"  Status: {res_lp.message}")
    if res_lp.success:
        min_rs = float(res_lp.fun)
        print(f"  Min rank sum: {min_rs:.4f} (threshold {rank_threshold})")
        print(f"  Gap: {min_rs - rank_threshold:.4f}")
    print(f"  Time: {lp_time:.1f}s")

    # === LP with rank constraint ===
    A_rank = -ranks.reshape(1, -1)
    A_ub_full = np.vstack([A_wang, A_rank])
    b_ub_full = np.append(b_wang, -float(rank_threshold))
    c_zero = np.zeros(nvar)
    
    res_lp2 = linprog(c_zero, A_ub=A_ub_full, b_ub=b_ub_full, A_eq=A_eq, b_eq=b_eq,
                      bounds=bounds, method="highs")
    print(f"\n=== LP Wang + rank >= {rank_threshold} ===")
    print(f"  Feasible: {res_lp2.success}")
    if res_lp2.success and res_lp2.x is not None:
        rs2 = float(ranks @ res_lp2.x)
        print(f"  Rank sum: {rs2:.4f}")

    # === MILP: Wang + rank ===
    print(f"\n=== MILP Wang (cap<={args.max_cap_initial}) + rank >= {rank_threshold} (time {args.milp_time}s) ===")
    integrality = np.ones(nvar)
    wang_constr = LinearConstraint(A_wang, ub=b_wang)
    eq_constr = LinearConstraint(A_eq, lb=b_eq, ub=b_eq)
    rank_constr = LinearConstraint(ranks.reshape(1, -1), lb=float(rank_threshold))
    int_bounds = SPBounds(lb=0, ub=1)
    
    t2 = time.time()
    try:
        res_milp = milp(c_zero, constraints=[wang_constr, eq_constr, rank_constr],
                        integrality=integrality, bounds=int_bounds,
                        options={"time_limit": args.milp_time})
        milp_time = time.time() - t2
        print(f"  Status: {res_milp.message}")
        print(f"  Feasible: {res_milp.success}")
        print(f"  Time: {milp_time:.1f}s")
        
        if res_milp.success and res_milp.x is not None:
            sol = np.round(res_milp.x).astype(int)
            support = [all_points[i] for i in range(nvar) if sol[i]]
            rs_sol = sum(matrix_rank(a) for a in support)
            print(f"  Support size: {len(support)}, Rank sum: {rs_sol}")
            print(f"  Support: {sorted(support)[:20]}...")
            
            # Check against full binary
            print(f"  Checking against full binary...")
            violations = 0
            for idx, cap, dim, words in load_binary_rows(args.binary):
                pcont = bit_in(words, pivot)
                rhs = cap - (1 if pcont else 0)
                occ = sum(1 for a in support if bit_in(words, a))
                if occ > rhs:
                    violations += 1
            print(f"  Full-row violations: {violations}")
            
            result = {
                "status": "feasible",
                "support": sorted(support),
                "support_with_pivot": sorted([pivot] + support),
                "rank_sum_nonpivot": rs_sol,
                "rank_sum_full": rs_sol + pivot_rank,
                "wang_violations_full": violations,
                "milp_time_sec": milp_time,
            }
        else:
            result = {
                "status": "infeasible" if "infeasible" in str(res_milp.message).lower() else "unknown",
                "message": str(res_milp.message),
                "milp_time_sec": milp_time,
            }
    except Exception as e:
        result = {"status": "error", "error": str(e)}
    
    output = {
        "schema": "point_level_milp_v1",
        "pivot": pivot, "pivot_rank": pivot_rank,
        "length": length, "rank_threshold": rank_threshold,
        "max_cap_initial": args.max_cap_initial,
        "n_wang_rows": len(A_rows), "n_var": nvar,
        "lp_min_rank": float(res_lp.fun) if res_lp.success else None,
        "lp_with_rank_feasible": bool(res_lp2.success),
        "milp_result": result,
        "elapsed_sec": time.time() - t0,
    }
    args.out.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    print(f"\nTotal: {time.time()-t0:.1f}s -> {args.out}")

if __name__ == "__main__":
    main()
