#!/usr/bin/env python3
"""Point-level MILP for pivot-fixed Wang + rank using SPARSE matrices.

510 binary variables x_a for a != pivot.
Original (not orbit-averaged) Wang constraints from the binary.
Sparse construction for memory efficiency.
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

def matrix_rank(a):
    return int(gf2_rank_mat(bits_to_mat(int(a))))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", type=Path, required=True)
    ap.add_argument("--pivot", type=int, required=True)
    ap.add_argument("--length", type=int, default=20)
    ap.add_argument("--max-dim", type=int, default=3, help="max subspace dim to include")
    ap.add_argument("--milp-time", type=int, default=300)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    pivot = args.pivot
    length = args.length
    pivot_rank = matrix_rank(pivot)
    rank_threshold = 27 - pivot_rank

    # Variable mapping: non-pivot points -> indices 0..509
    all_points = sorted([a for a in range(1, 512) if a != pivot])
    pt2var = {a: i for i, a in enumerate(all_points)}
    nvar = len(all_points)
    ranks = np.array([matrix_rank(a) for a in all_points], dtype=float)
    print(f"Pivot={pivot} rank={pivot_rank} threshold={rank_threshold} vars={nvar}")

    # Stream binary and build sparse constraint matrix
    print(f"Loading rows with dim <= {args.max_dim}...")
    row_indices = []; col_indices = []; values = []; rhs_list = []
    nr = 0; neg_rhs = 0; skipped_dim = 0; total_read = 0
    
    with args.binary.open("rb") as f:
        magic = f.read(8); assert magic == MAGIC
        nrows = struct.unpack("<I", f.read(4))[0]
        for idx in range(nrows):
            cap, dim, _res = struct.unpack("<BBH", f.read(4))
            words = struct.unpack("<8Q", f.read(64))
            total_read += 1
            if dim > args.max_dim:
                skipped_dim += 1
                continue
            pcont = bit_in(words, pivot)
            rhs = int(cap) - (1 if pcont else 0)
            if rhs < 0:
                neg_rhs += 1
                continue
            pts_novp = []
            for wi, w0 in enumerate(words):
                w = int(w0)
                while w:
                    lb = w & -w; b = lb.bit_length()-1; p = wi*64+b
                    if 1 <= p <= 511 and p != pivot:
                        pts_novp.append(p)
                    w ^= lb
            if not pts_novp:
                continue
            for a in pts_novp:
                row_indices.append(nr)
                col_indices.append(pt2var[a])
                values.append(1.0)
            rhs_list.append(float(rhs))
            nr += 1
    
    print(f"  Read {total_read} rows, kept {nr}, skipped {skipped_dim} (dim), {neg_rhs} (neg rhs)")
    print(f"  Nonzeros: {len(values)}")
    
    A_wang = csr_matrix((values, (row_indices, col_indices)), shape=(nr, nvar))
    b_wang = np.array(rhs_list, dtype=float)
    
    # Equality and rank
    A_eq_dense = np.ones((1, nvar), dtype=float)
    rank_vec = ranks.reshape(1, -1)
    c_zero = np.zeros(nvar)
    
    # LP: minimize rank sum
    t1 = time.time()
    res_lp = linprog(ranks, A_ub=A_wang, b_ub=b_wang, 
                     A_eq=A_eq_dense, b_eq=np.array([float(length-1)]),
                     bounds=[(0,1)]*nvar, method="highs")
    print(f"\n=== LP min rank sum (dim<={args.max_dim}, {nr} rows) ===")
    print(f"  {res_lp.message}")
    if res_lp.success:
        print(f"  Min rank: {res_lp.fun:.4f}, gap from {rank_threshold}: {res_lp.fun-rank_threshold:.4f}")
    print(f"  Time: {time.time()-t1:.1f}s")
    
    # LP with rank constraint
    from scipy.sparse import vstack as sp_vstack
    A_rank_row = csr_matrix(-rank_vec)
    A_ub_full = sp_vstack([A_wang, A_rank_row])
    b_ub_full = np.append(b_wang, -float(rank_threshold))
    
    t2 = time.time()
    res_lp2 = linprog(c_zero, A_ub=A_ub_full, b_ub=b_ub_full,
                      A_eq=A_eq_dense, b_eq=np.array([float(length-1)]),
                      bounds=[(0,1)]*nvar, method="highs")
    print(f"\n=== LP Wang + rank >= {rank_threshold} ===")
    print(f"  Feasible: {res_lp2.success}, Time: {time.time()-t2:.1f}s")
    if res_lp2.success and res_lp2.x is not None:
        print(f"  Rank sum: {ranks@res_lp2.x:.4f}")
    
    # MILP
    print(f"\n=== MILP Wang (dim<={args.max_dim}) + rank >= {rank_threshold} ({args.milp_time}s) ===")
    wang_constr = LinearConstraint(A_wang, ub=b_wang)
    eq_constr = LinearConstraint(csr_matrix(A_eq_dense), lb=float(length-1), ub=float(length-1))
    rank_constr = LinearConstraint(csr_matrix(rank_vec), lb=float(rank_threshold))
    int_bounds = SPBounds(lb=0, ub=1)
    integrality = np.ones(nvar)
    
    t3 = time.time()
    try:
        res_milp = milp(c_zero, constraints=[wang_constr, eq_constr, rank_constr],
                        integrality=integrality, bounds=int_bounds,
                        options={"time_limit": args.milp_time})
        milp_time = time.time() - t3
        print(f"  Status: {res_milp.message}")
        print(f"  Feasible: {res_milp.success}")
        print(f"  Time: {milp_time:.1f}s")
        
        milp_result = {"status": str(res_milp.message), "feasible": bool(res_milp.success),
                       "time_sec": milp_time}
        
        if res_milp.success and res_milp.x is not None:
            sol = np.round(res_milp.x).astype(int)
            support = sorted([all_points[i] for i in range(nvar) if sol[i]])
            rs_sol = sum(matrix_rank(a) for a in support)
            print(f"  Support({len(support)}): {support}")
            print(f"  Rank sum: {rs_sol}")
            
            # Check local Wang violations
            wang_lhs = A_wang.dot(sol.astype(float))
            local_viol = int(np.sum(wang_lhs > b_wang + 0.5))
            print(f"  Local violations (dim<={args.max_dim}): {local_viol}")
            
            # Check full binary
            print(f"  Checking full binary...")
            full_viol = 0; tight = 0
            support_set = set(support)
            with args.binary.open("rb") as f:
                magic = f.read(8); nrows = struct.unpack("<I", f.read(4))[0]
                for idx in range(nrows):
                    cap, dim, _res = struct.unpack("<BBH", f.read(4))
                    words = struct.unpack("<8Q", f.read(64))
                    pcont = bit_in(words, pivot)
                    rhs = int(cap) - (1 if pcont else 0)
                    occ = sum(1 for a in support_set if bit_in(words, a))
                    if occ > rhs: full_viol += 1
                    elif occ == rhs: tight += 1
            print(f"  Full violations: {full_viol}, tight: {tight}")
            milp_result["support"] = support
            milp_result["rank_sum"] = rs_sol
            milp_result["local_violations"] = local_viol
            milp_result["full_violations"] = full_viol
            milp_result["full_tight"] = tight
        
    except Exception as e:
        milp_result = {"error": str(e)}
        print(f"  Error: {e}")
    
    output = {
        "schema": "point_milp_sparse_v1",
        "pivot": pivot, "pivot_rank": pivot_rank,
        "length": length, "rank_threshold": rank_threshold,
        "max_dim": args.max_dim, "n_constraints": nr, "n_var": nvar,
        "lp_min_rank": float(res_lp.fun) if res_lp.success else None,
        "lp_rank_feasible": bool(res_lp2.success),
        "milp": milp_result,
        "elapsed_sec": time.time()-t0,
    }
    args.out.write_text(json.dumps(output, indent=2, sort_keys=True)+"\n")
    print(f"\nTotal: {time.time()-t0:.1f}s -> {args.out}")

if __name__ == "__main__":
    main()
