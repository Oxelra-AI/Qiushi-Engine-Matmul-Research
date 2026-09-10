#!/usr/bin/env python3
"""Orbit-averaged LP with flattening rank-sum and column/row containment constraints.

For pivot-fixed full Wang occupation plus the A-slot split flattening:
  1. Minimize Sigma rank(a_t) over the Wang polytope
  2. Add rank-sum >= threshold (27 - rank(p))
  3. Add column-containment: for every nonzero u in F_2^3,
       #{t : u in col(a_t)} <= Sigma rank(a_t) - 18
     and row-containment analogues.
  4. Check LP feasibility of the combined system.

If combined LP is infeasible, the Farkas certificate proves R >= 21.
"""
from __future__ import annotations
import argparse, json, os, struct, sys, time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Tuple
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix, vstack as sp_vstack

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from quotient_line_caps_and_controls import bits_to_mat, mat_to_bits, gf2_inv, gl3, gf2_rank_mat

MAGIC = b"WANG512\x01"

def bit_in(words, p):
    return bool((int(words[p >> 6]) >> (p & 63)) & 1)

def points_in_words(words):
    pts = []
    for wi, w0 in enumerate(words):
        w = int(w0)
        while w:
            lb = w & -w
            b = lb.bit_length() - 1
            p = wi * 64 + b
            if 1 <= p <= 511:
                pts.append(p)
            w ^= lb
    return pts

def load_binary_rows(path):
    with path.open("rb") as f:
        magic = f.read(8)
        assert magic == MAGIC, f"bad magic {magic!r}"
        nrows = struct.unpack("<I", f.read(4))[0]
        for idx in range(nrows):
            cap, dim, _res = struct.unpack("<BBH", f.read(4))
            words = struct.unpack("<8Q", f.read(64))
            yield idx, int(cap), int(dim), tuple(int(w) for w in words)

def full_transform_point(a, P, Q):
    A = bits_to_mat(int(a))
    QinvT = gf2_inv(Q).T % 2
    B = (P.T @ A @ QinvT) % 2
    return int(mat_to_bits(B))

def compute_stabilizer(pivot):
    G = gl3()
    return [(P.copy(), Q.copy()) for P in G for Q in G
            if full_transform_point(pivot, P, Q) == pivot]

def full_point_orbits(pivot):
    stab = compute_stabilizer(pivot)
    visited = set()
    orbits = []
    for a in range(1, 512):
        if a in visited:
            continue
        orb = set()
        queue = [a]
        while queue:
            x = queue.pop()
            if x in orb:
                continue
            orb.add(x)
            for P, Q in stab:
                y = full_transform_point(x, P, Q)
                if y not in orb:
                    queue.append(y)
        orbits.append(sorted(orb))
        visited |= orb
    orbits.sort(key=lambda o: (0 if pivot in o else 1, len(o), o[0]))
    p2o = {}
    for i, o in enumerate(orbits):
        for a in o:
            p2o[a] = i
    return orbits, p2o, stab

def matrix_rank(a):
    return int(gf2_rank_mat(bits_to_mat(int(a))))

def col_space(a):
    """Return column space of 3x3 GF2 matrix as set of nonzero vectors in F_2^3."""
    M = bits_to_mat(int(a))
    # columns of M
    cols = [M[:, j] % 2 for j in range(3)]
    # generate span
    span = set()
    for mask in range(1, 8):
        v = np.zeros(3, dtype=int)
        for j in range(3):
            if mask & (1 << j):
                v = (v + cols[j]) % 2
        key = int(v[0]) | (int(v[1]) << 1) | (int(v[2]) << 2)
        if key:
            span.add(key)
    return span

def row_space(a):
    """Return row space of 3x3 GF2 matrix as set of nonzero vectors in F_2^3."""
    M = bits_to_mat(int(a))
    rows = [M[i, :] % 2 for i in range(3)]
    span = set()
    for mask in range(1, 8):
        v = np.zeros(3, dtype=int)
        for j in range(3):
            if mask & (1 << j):
                v = (v + rows[j]) % 2
        key = int(v[0]) | (int(v[1]) << 1) | (int(v[2]) << 2)
        if key:
            span.add(key)
    return span

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", type=Path, required=True)
    ap.add_argument("--pivot", type=int, required=True)
    ap.add_argument("--length", type=int, default=20)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    pivot = args.pivot
    length = args.length
    pivot_rank = matrix_rank(pivot)
    rank_threshold = 27 - pivot_rank  # remaining terms rank sum must be >= this

    print(f"Pivot={pivot}, rank(pivot)={pivot_rank}, threshold={rank_threshold}")

    # Compute orbits
    orbits, p2o, stab = full_point_orbits(pivot)
    pivot_orbit = p2o[pivot]
    var_orbits = [i for i in range(len(orbits)) if i != pivot_orbit]
    orbit_to_var = {o: i for i, o in enumerate(var_orbits)}
    nvar = len(var_orbits)
    var_sizes = [len(orbits[o]) for o in var_orbits]
    var_ranks = [matrix_rank(orbits[o][0]) for o in var_orbits]
    print(f"  {len(orbits)} orbits, {nvar} var orbits, stab size {len(stab)}")

    # Compute column/row containment counts per orbit per direction u in F_2^3\{0}
    directions = list(range(1, 8))  # u=1..7 as 3-bit vectors
    col_counts = np.zeros((7, nvar), dtype=int)  # col_counts[u_idx][var_idx]
    row_counts = np.zeros((7, nvar), dtype=int)
    for vi, oi in enumerate(var_orbits):
        for a in orbits[oi]:
            cs = col_space(a)
            rs = row_space(a)
            for ui, u in enumerate(directions):
                if u in cs:
                    col_counts[ui, vi] += 1
                if u in rs:
                    row_counts[ui, vi] += 1

    # Pivot column/row containment
    pivot_col = col_space(pivot)
    pivot_row = row_space(pivot)

    print(f"  Column containment counts computed")
    for ui, u in enumerate(directions):
        print(f"    u={u}: col_counts={list(col_counts[ui])}, pivot_in_col={u in pivot_col}")

    # Stream binary and aggregate Wang rows by orbit coefficient
    print(f"Loading {args.binary}...")
    constraints = {}  # coeff_tuple -> min_rhs
    raw_rows = 0
    for idx, cap, dim, words in load_binary_rows(args.binary):
        raw_rows += 1
        pcont = bit_in(words, pivot)
        rhs = int(cap) - (1 if pcont else 0)
        coeff = [0] * nvar
        for a in points_in_words(words):
            if a == pivot:
                continue
            oi = p2o[a]
            vi = orbit_to_var.get(oi)
            if vi is not None:
                coeff[vi] += 1
        tup = tuple(coeff)
        if not any(coeff) and rhs >= 0:
            continue
        rec = constraints.get(tup)
        if rec is None or rhs < rec:
            constraints[tup] = int(rhs)
    print(f"  {raw_rows} rows -> {len(constraints)} unique orbit-coeff rows")

    # Build Wang constraint matrix
    wang_coeffs = list(constraints.keys())
    wang_rhs = [constraints[k] for k in wang_coeffs]
    n_wang = len(wang_coeffs)

    # LP setup: minimize/check feasibility over orbit variables X_o in [0,1]
    # Equality: sum size_o * X_o = length - 1
    # Wang: sum coeff[j] * X_o <= rhs for each row

    A_eq = np.array([var_sizes], dtype=float)
    b_eq = np.array([float(length - 1)], dtype=float)
    bounds = [(0.0, 1.0)] * nvar

    # Build Wang A_ub from sparse
    rows_i, cols_j, vals_v = [], [], []
    for ri, coeff in enumerate(wang_coeffs):
        for j, v in enumerate(coeff):
            if v:
                rows_i.append(ri); cols_j.append(j); vals_v.append(float(v))
    A_wang = coo_matrix((vals_v, (rows_i, cols_j)), shape=(n_wang, nvar)).tocsr()
    b_wang = np.array(wang_rhs, dtype=float)

    results = {}

    # ---- Test 1: Minimize rank sum over Wang polytope ----
    rank_obj = np.array([var_ranks[i] * var_sizes[i] for i in range(nvar)], dtype=float)
    res1 = linprog(rank_obj, A_ub=A_wang, b_ub=b_wang, A_eq=A_eq, b_eq=b_eq,
                   bounds=bounds, method="highs")
    min_rank_sum = float(res1.fun) if res1.success else None
    print(f"\n=== Test 1: Minimize rank sum ===")
    print(f"  Status: {res1.message}")
    print(f"  Min rank sum (non-pivot): {min_rank_sum}")
    print(f"  Full min rank sum: {min_rank_sum + pivot_rank if min_rank_sum is not None else None}")
    print(f"  Threshold: {rank_threshold} (full: 27)")
    if min_rank_sum is not None:
        print(f"  Margin: {min_rank_sum - rank_threshold:.6f}")
    results["test1_min_rank_sum"] = {
        "status": int(res1.status), "message": str(res1.message),
        "min_rank_sum_nonpivot": min_rank_sum,
        "min_rank_sum_full": min_rank_sum + pivot_rank if min_rank_sum is not None else None,
        "threshold_nonpivot": rank_threshold,
        "margin": min_rank_sum - rank_threshold if min_rank_sum is not None else None,
        "solution": [float(x) for x in res1.x] if res1.x is not None else None,
    }

    # ---- Test 2: Maximize rank sum over Wang polytope ----
    res1b = linprog(-rank_obj, A_ub=A_wang, b_ub=b_wang, A_eq=A_eq, b_eq=b_eq,
                    bounds=bounds, method="highs")
    max_rank_sum = -float(res1b.fun) if res1b.success else None
    print(f"\n=== Test 1b: Maximize rank sum ===")
    print(f"  Max rank sum (non-pivot): {max_rank_sum}")
    results["test1b_max_rank_sum"] = {
        "max_rank_sum_nonpivot": max_rank_sum,
        "max_rank_sum_full": max_rank_sum + pivot_rank if max_rank_sum is not None else None,
    }

    # ---- Test 3: Wang + rank-sum >= threshold ----
    # Add: -sum rank_o * size_o * X_o <= -threshold
    rank_row = -rank_obj.reshape(1, -1)
    A_ub3 = sp_vstack([A_wang, coo_matrix(rank_row)]).tocsr()
    b_ub3 = np.append(b_wang, -float(rank_threshold))
    c_zero = np.zeros(nvar)
    res3 = linprog(c_zero, A_ub=A_ub3, b_ub=b_ub3, A_eq=A_eq, b_eq=b_eq,
                   bounds=bounds, method="highs")
    print(f"\n=== Test 3: Wang + rank-sum >= {rank_threshold} ===")
    print(f"  Status: {res3.message}")
    print(f"  Feasible: {res3.success}")
    if res3.success and res3.x is not None:
        actual_rs = float(rank_obj @ res3.x)
        print(f"  Rank sum at feasible point: {actual_rs:.4f}")
    results["test3_wang_plus_rank"] = {
        "status": int(res3.status), "message": str(res3.message),
        "feasible": bool(res3.success),
        "rank_threshold": rank_threshold,
        "solution": [float(x) for x in res3.x] if res3.x is not None else None,
        "rank_sum": float(rank_obj @ res3.x) if res3.success and res3.x is not None else None,
    }

    # ---- Test 4: Wang + rank-sum + column containment ----
    # For each direction u: sum_o col_u(o) * X_o + [u in col(p)] <= rank(p) + sum_o r_o*s_o*X_o - 18
    # Rearranged: sum_o (col_u(o) - r_o*s_o) * X_o <= rank(p) - 18 - [u in col(p)]
    # Similarly for row containment
    extra_rows = []
    extra_rhs = []
    extra_labels = []
    for ui, u in enumerate(directions):
        # Column containment
        coeff_col = col_counts[ui].astype(float) - rank_obj  # col_u(o) - r_o*s_o
        rhs_col = float(pivot_rank - 18 - (1 if u in pivot_col else 0))
        extra_rows.append(coeff_col.reshape(1, -1))
        extra_rhs.append(rhs_col)
        extra_labels.append(f"col_u={u}")
        # Row containment
        coeff_row = row_counts[ui].astype(float) - rank_obj
        rhs_row = float(pivot_rank - 18 - (1 if u in pivot_row else 0))
        extra_rows.append(coeff_row.reshape(1, -1))
        extra_rhs.append(rhs_row)
        extra_labels.append(f"row_u={u}")

    if extra_rows:
        A_extra = np.vstack(extra_rows)
        A_ub4 = sp_vstack([A_ub3, coo_matrix(A_extra)]).tocsr()
        b_ub4 = np.append(b_ub3, extra_rhs)
    else:
        A_ub4, b_ub4 = A_ub3, b_ub3

    res4 = linprog(c_zero, A_ub=A_ub4, b_ub=b_ub4, A_eq=A_eq, b_eq=b_eq,
                   bounds=bounds, method="highs")
    print(f"\n=== Test 4: Wang + rank-sum + col/row containment ===")
    print(f"  Status: {res4.message}")
    print(f"  Feasible: {res4.success}")
    if res4.success and res4.x is not None:
        actual_rs = float(rank_obj @ res4.x)
        print(f"  Rank sum at feasible point: {actual_rs:.4f}")
        # Check containment constraint slack
        for i, label in enumerate(extra_labels):
            lhs = float(A_extra[i] @ res4.x)
            slack = extra_rhs[i] - lhs
            if slack < 0.01:
                print(f"  BINDING: {label}, lhs={lhs:.4f}, rhs={extra_rhs[i]:.1f}, slack={slack:.6f}")
    results["test4_wang_rank_containment"] = {
        "status": int(res4.status), "message": str(res4.message),
        "feasible": bool(res4.success),
        "n_extra_constraints": len(extra_labels),
        "extra_labels": extra_labels,
        "extra_rhs": extra_rhs,
        "solution": [float(x) for x in res4.x] if res4.x is not None else None,
        "rank_sum": float(rank_obj @ res4.x) if res4.success and res4.x is not None else None,
    }

    # ---- Test 5: Only col/row containment (no rank-sum), check if they interact with Wang ----
    if extra_rows:
        A_ub5 = sp_vstack([A_wang, coo_matrix(A_extra)]).tocsr()
        b_ub5 = np.append(b_wang, extra_rhs)
        res5 = linprog(rank_obj, A_ub=A_ub5, b_ub=b_ub5, A_eq=A_eq, b_eq=b_eq,
                       bounds=bounds, method="highs")
        min_rs5 = float(res5.fun) if res5.success else None
        print(f"\n=== Test 5: Wang + col/row containment, minimize rank sum ===")
        print(f"  Status: {res5.message}")
        print(f"  Min rank sum: {min_rs5}")
        results["test5_wang_containment_minrank"] = {
            "status": int(res5.status), "message": str(res5.message),
            "min_rank_sum_nonpivot": min_rs5,
            "feasible": bool(res5.success),
        }

    # ---- Test 6: Integer LP (small enough for direct solve) ----
    # With only 12-20 variables, try integer feasibility
    from scipy.optimize import milp, LinearConstraint, Bounds as SPBounds
    integrality = np.ones(nvar)  # all integer
    # Wang: A_wang @ x <= b_wang
    # Rank: rank_obj @ x >= threshold
    # col/row containment: A_extra @ x <= extra_rhs
    # Equality: A_eq @ x == b_eq
    wang_constr = LinearConstraint(A_wang, ub=b_wang)
    eq_constr = LinearConstraint(A_eq, lb=b_eq, ub=b_eq)
    rank_constr = LinearConstraint(rank_obj.reshape(1, -1), lb=float(rank_threshold))
    contain_constr = LinearConstraint(coo_matrix(A_extra), ub=np.array(extra_rhs, dtype=float)) if extra_rows else None
    all_constrs = [wang_constr, eq_constr, rank_constr]
    if contain_constr is not None:
        all_constrs.append(contain_constr)
    int_bounds = SPBounds(lb=0, ub=np.array([min(s, length-1) for s in var_sizes], dtype=float))
    
    print(f"\n=== Test 6: Integer LP (MILP) with rank + containment ===")
    try:
        res6 = milp(c_zero, constraints=all_constrs, integrality=integrality,
                     bounds=int_bounds, options={"time_limit": 60})
        print(f"  Status: {res6.message}")
        print(f"  Feasible: {res6.success}")
        if res6.success and res6.x is not None:
            sol = [int(round(x)) for x in res6.x]
            actual_rs = sum(var_ranks[i] * var_sizes[i] * sol[i] for i in range(nvar))
            actual_pts = sum(var_sizes[i] * sol[i] for i in range(nvar))
            print(f"  Solution: {sol}")
            print(f"  Points: {actual_pts}, Rank sum: {actual_rs}")
        results["test6_milp"] = {
            "status": str(res6.message),
            "feasible": bool(res6.success),
            "solution": [int(round(x)) for x in res6.x] if res6.success and res6.x is not None else None,
        }
    except Exception as e:
        print(f"  MILP error: {e}")
        results["test6_milp"] = {"error": str(e)}

    elapsed = time.time() - t0
    output = {
        "schema": "rank_constrained_orbit_lp_v1",
        "pivot": pivot, "pivot_rank": pivot_rank,
        "length": length, "rank_threshold": rank_threshold,
        "n_wang_rows": n_wang, "n_var": nvar,
        "var_sizes": var_sizes, "var_ranks": var_ranks,
        "var_orbit_reps": [orbits[o][0] for o in var_orbits],
        "stabilizer_size": len(stab),
        "elapsed_sec": elapsed,
        "results": results,
    }
    args.out.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    print(f"\nTotal elapsed: {elapsed:.1f}s")
    print(f"Output: {args.out}")

if __name__ == "__main__":
    main()
