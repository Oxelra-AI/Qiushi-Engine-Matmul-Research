#!/usr/bin/env python3
"""CEGAR MILP: iteratively add violated Wang rows with rank constraint.

Start from dim<=2 constraints (trivially feasible), find integer solution,
check against all rows, add violated rows, re-solve. The rank constraint
is present throughout.
"""
from __future__ import annotations
import argparse, json, os, struct, sys, time
from pathlib import Path
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds as SPBounds
from scipy.sparse import csr_matrix, vstack as sp_vstack, lil_matrix

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from quotient_line_caps_and_controls import bits_to_mat, gf2_rank_mat

MAGIC = b"WANG512\x01"

def bit_in(words, p):
    return bool((int(words[p >> 6]) >> (p & 63)) & 1)

def matrix_rank(a):
    return int(gf2_rank_mat(bits_to_mat(int(a))))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", type=Path, required=True)
    ap.add_argument("--pivot", type=int, required=True)
    ap.add_argument("--length", type=int, default=20)
    ap.add_argument("--milp-time-per-round", type=int, default=120)
    ap.add_argument("--max-rounds", type=int, default=20)
    ap.add_argument("--max-violated-per-round", type=int, default=2000)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    pivot = args.pivot
    length = args.length
    pivot_rank = matrix_rank(pivot)
    rank_threshold = 27 - pivot_rank
    
    all_points = sorted([a for a in range(1, 512) if a != pivot])
    pt2var = {a: i for i, a in enumerate(all_points)}
    nvar = len(all_points)
    ranks = np.array([matrix_rank(a) for a in all_points], dtype=float)
    
    print(f"Pivot={pivot} rank={pivot_rank} threshold={rank_threshold} vars={nvar}")
    
    # Precompute for fast full-binary check
    # Read and store all rows in memory-efficient form
    print(f"Pre-reading full binary...")
    all_rows = []  # (rhs, point_set_as_frozenset)
    with args.binary.open("rb") as f:
        magic = f.read(8); assert magic == MAGIC
        nrows_total = struct.unpack("<I", f.read(4))[0]
        for idx in range(nrows_total):
            cap, dim, _res = struct.unpack("<BBH", f.read(4))
            words = struct.unpack("<8Q", f.read(64))
            pcont = bit_in(words, pivot)
            rhs = int(cap) - (1 if pcont else 0)
            if rhs < 0:
                continue
            # Collect non-pivot points
            pts = []
            for wi, w0 in enumerate(words):
                w = int(w0)
                while w:
                    lb = w & -w; b = lb.bit_length()-1; p = wi*64+b
                    if 1 <= p <= 511 and p != pivot:
                        pts.append(pt2var[p])
                    w ^= lb
            if not pts:
                continue
            all_rows.append((rhs, frozenset(pts), dim))
    print(f"  {len(all_rows)} usable rows")
    
    # Initialize with dim<=2 rows
    active_indices = []
    for ri, (rhs, pts, dim) in enumerate(all_rows):
        if dim <= 2:
            active_indices.append(ri)
    print(f"  Initial active (dim<=2): {len(active_indices)}")
    
    rounds = []
    for rnd in range(args.max_rounds):
        t_rnd = time.time()
        
        # Build active constraint matrix
        n_active = len(active_indices)
        row_i, col_j, val_v = [], [], []
        rhs_arr = []
        for ri_new, ri_orig in enumerate(active_indices):
            rhs, pts, dim = all_rows[ri_orig]
            for v in pts:
                row_i.append(ri_new)
                col_j.append(v)
                val_v.append(1.0)
            rhs_arr.append(float(rhs))
        
        A_active = csr_matrix((val_v, (row_i, col_j)), shape=(n_active, nvar))
        b_active = np.array(rhs_arr, dtype=float)
        
        # Solve MILP
        wang_constr = LinearConstraint(A_active, ub=b_active)
        eq_constr = LinearConstraint(
            csr_matrix(np.ones((1, nvar))), 
            lb=float(length-1), ub=float(length-1))
        rank_constr = LinearConstraint(
            csr_matrix(ranks.reshape(1,-1)), 
            lb=float(rank_threshold))
        
        t_solve = time.time()
        res = milp(np.zeros(nvar), 
                   constraints=[wang_constr, eq_constr, rank_constr],
                   integrality=np.ones(nvar),
                   bounds=SPBounds(lb=0, ub=1),
                   options={"time_limit": args.milp_time_per_round})
        solve_time = time.time() - t_solve
        
        if not res.success:
            status = "infeasible" if "infeasible" in str(res.message).lower() else "timeout"
            print(f"Round {rnd}: {status} ({res.message}), {n_active} constraints, {solve_time:.1f}s")
            rounds.append({"round": rnd, "status": status, "n_active": n_active, 
                          "solve_sec": solve_time, "message": str(res.message)})
            if status == "infeasible":
                break
            continue
        
        sol = np.round(res.x).astype(int)
        support = sorted([all_points[i] for i in range(nvar) if sol[i]])
        rs = sum(matrix_rank(a) for a in support)
        support_set_var = set(i for i in range(nvar) if sol[i])
        
        # Check all rows
        violations = []
        for ri, (rhs, pts, dim) in enumerate(all_rows):
            occ = len(pts & support_set_var)
            if occ > rhs:
                violations.append((occ - rhs, ri, dim))
        
        violations.sort(reverse=True)
        n_viol = len(violations)
        
        print(f"Round {rnd}: feasible, |S|={len(support)}, rank_sum={rs}, violations={n_viol}, "
              f"{n_active} active, {solve_time:.1f}s")
        
        if n_viol == 0:
            print(f"  *** ZERO VIOLATIONS! Valid Wang-admissible rank-valid support!")
            rounds.append({"round": rnd, "status": "wang_admissible", "n_active": n_active,
                          "violations": 0, "rank_sum": rs, "support": support,
                          "solve_sec": solve_time})
            break
        
        # Add top violated rows
        added = 0
        active_set = set(active_indices)
        for excess, ri, dim in violations[:args.max_violated_per_round]:
            if ri not in active_set:
                active_indices.append(ri)
                active_set.add(ri)
                added += 1
        
        dim_hist = {}
        for _, ri, dim in violations[:args.max_violated_per_round]:
            dim_hist[dim] = dim_hist.get(dim, 0) + 1
        
        print(f"  Added {added} violated rows (dim dist: {sorted(dim_hist.items())})")
        rounds.append({"round": rnd, "status": "violated", "n_active": n_active,
                       "violations": n_viol, "rank_sum": rs, "added": added,
                       "dim_hist": dim_hist, "solve_sec": solve_time,
                       "support_head": support[:10]})
    
    output = {
        "schema": "cegar_milp_rank_v1",
        "pivot": pivot, "pivot_rank": pivot_rank,
        "length": length, "rank_threshold": rank_threshold,
        "total_rows": len(all_rows), "final_active": len(active_indices),
        "rounds": rounds,
        "elapsed_sec": time.time()-t0,
    }
    args.out.write_text(json.dumps(output, indent=2, sort_keys=True)+"\n")
    print(f"\nTotal: {time.time()-t0:.1f}s -> {args.out}")

if __name__ == "__main__":
    main()
