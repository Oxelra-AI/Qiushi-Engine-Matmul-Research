#!/usr/bin/env python3
"""Correctly formulated orbit-averaged MILP for pivot-fixed full Wang + rank constraint.

Variables Y_o = integer number of points selected from orbit o (0 ≤ Y_o ≤ |orbit_o|).
Wang constraints use orbit-averaged coefficients: Σ (c_o / s_o) * Y_o ≤ rhs.
This is a valid RELAXATION of the point-level IP: infeasibility here implies infeasibility
of the point-level problem (proven by stabilizer averaging argument).

Tests:
1. LP relaxation: minimize rank sum over Wang polytope (Y continuous)
2. LP relaxation: check Wang + rank-sum feasibility  
3. MILP: check Wang + rank-sum integer feasibility
4. LP check with column/row containment (informational only, not necessarily valid relaxation)
"""
from __future__ import annotations
import argparse, json, os, struct, sys, time
from collections import Counter
from pathlib import Path
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds as SPBounds
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
        assert magic == MAGIC
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
    M = bits_to_mat(int(a))
    span = set()
    for mask in range(1, 8):
        v = np.zeros(3, dtype=int)
        for j in range(3):
            if mask & (1 << j):
                v = (v + M[:, j]) % 2
        key = int(v[0]) | (int(v[1]) << 1) | (int(v[2]) << 2)
        if key:
            span.add(key)
    return span

def row_space(a):
    M = bits_to_mat(int(a))
    span = set()
    for mask in range(1, 8):
        v = np.zeros(3, dtype=int)
        for j in range(3):
            if mask & (1 << j):
                v = (v + M[j, :]) % 2
        key = int(v[0]) | (int(v[1]) << 1) | (int(v[2]) << 2)
        if key:
            span.add(key)
    return span

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", type=Path, required=True)
    ap.add_argument("--pivot", type=int, required=True)
    ap.add_argument("--length", type=int, default=20)
    ap.add_argument("--milp-time", type=int, default=120)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    pivot = args.pivot
    length = args.length
    pivot_rank = matrix_rank(pivot)
    rank_threshold = 27 - pivot_rank  # non-pivot rank sum must be >= this

    print(f"Pivot={pivot}, rank(pivot)={pivot_rank}, rank_threshold={rank_threshold}")

    # Compute orbits
    orbits, p2o, stab = full_point_orbits(pivot)
    pivot_orbit = p2o[pivot]
    var_orbits = [i for i in range(len(orbits)) if i != pivot_orbit]
    orbit_to_var = {o: i for i, o in enumerate(var_orbits)}
    nvar = len(var_orbits)
    var_sizes = np.array([len(orbits[o]) for o in var_orbits], dtype=float)
    var_ranks = np.array([matrix_rank(orbits[o][0]) for o in var_orbits], dtype=float)
    print(f"  {len(orbits)} orbits, {nvar} variables, stab size {len(stab)}")
    print(f"  Orbit sizes: {[int(s) for s in var_sizes]}")
    print(f"  Orbit ranks: {[int(r) for r in var_ranks]}")

    # Stream binary and aggregate Wang rows
    # For Y_o (count) variables, Wang coeff is c_o/s_o
    print(f"Loading {args.binary}...")
    # Aggregate by orbit-level coefficient vector (scaled by 1/s_o)
    # Store raw c_o and compute c_o/s_o for the LP
    raw_constraints = {}  # tuple of c_o -> min rhs
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
        rec = raw_constraints.get(tup)
        if rec is None or rhs < rec:
            raw_constraints[tup] = int(rhs)
    print(f"  {raw_rows} rows -> {len(raw_constraints)} unique orbit-coeff rows")

    # Build scaled constraint matrix for Y variables
    wang_coeffs = list(raw_constraints.keys())
    wang_rhs = np.array([raw_constraints[k] for k in wang_coeffs], dtype=float)
    n_wang = len(wang_coeffs)

    # A_wang[i,j] = c_o[j] / s_o[j] for Y_o variables
    rows_i, cols_j, vals_v = [], [], []
    for ri, coeff in enumerate(wang_coeffs):
        for j, c in enumerate(coeff):
            if c:
                rows_i.append(ri)
                cols_j.append(j)
                vals_v.append(float(c) / float(var_sizes[j]))
    A_wang = coo_matrix((vals_v, (rows_i, cols_j)), shape=(n_wang, nvar)).tocsr()

    # Equality: Σ Y_o = length - 1
    A_eq = np.ones((1, nvar), dtype=float)
    b_eq = np.array([float(length - 1)], dtype=float)

    # Bounds: Y_o ∈ [0, s_o] (continuous) or {0,...,s_o} (integer)
    cont_bounds = [(0.0, float(s)) for s in var_sizes]

    # Rank objective: Σ r_o * Y_o
    rank_obj = var_ranks.copy()

    results = {}

    # === Test 1: LP minimize rank sum ===
    res1 = linprog(rank_obj, A_ub=A_wang, b_ub=wang_rhs, A_eq=A_eq, b_eq=b_eq,
                   bounds=cont_bounds, method="highs")
    min_rs = float(res1.fun) if res1.success else None
    print(f"\n=== Test 1: LP minimize rank sum ===")
    print(f"  Status: {res1.message}")
    print(f"  Min rank sum (non-pivot): {min_rs}")
    print(f"  Full min rank sum: {min_rs + pivot_rank if min_rs else None}")
    print(f"  Threshold: {rank_threshold}")
    if min_rs is not None:
        print(f"  Gap: {min_rs - rank_threshold:.6f}")
        if res1.x is not None:
            print(f"  Solution Y: {[f'{y:.3f}' for y in res1.x]}")
            print(f"  Total points: {sum(res1.x):.3f}")
    results["lp_min_rank"] = {
        "feasible": bool(res1.success),
        "min_rank_nonpivot": min_rs,
        "min_rank_full": min_rs + pivot_rank if min_rs else None,
        "gap": min_rs - rank_threshold if min_rs else None,
    }

    # === Test 2: LP maximize rank sum ===
    res1b = linprog(-rank_obj, A_ub=A_wang, b_ub=wang_rhs, A_eq=A_eq, b_eq=b_eq,
                    bounds=cont_bounds, method="highs")
    max_rs = -float(res1b.fun) if res1b.success else None
    print(f"\n=== Test 1b: LP max rank sum: {max_rs}")
    results["lp_max_rank"] = {"max_rank_nonpivot": max_rs}

    # === Test 3: LP with rank constraint ===
    rank_row = -rank_obj.reshape(1, -1)  # -Σ r_o Y_o <= -threshold
    A_ub3 = sp_vstack([A_wang, coo_matrix(rank_row)]).tocsr()
    b_ub3 = np.append(wang_rhs, -float(rank_threshold))
    c_zero = np.zeros(nvar)
    res3 = linprog(c_zero, A_ub=A_ub3, b_ub=b_ub3, A_eq=A_eq, b_eq=b_eq,
                   bounds=cont_bounds, method="highs")
    print(f"\n=== Test 3: LP Wang + rank >= {rank_threshold} ===")
    print(f"  Feasible: {res3.success}")
    if res3.success and res3.x is not None:
        rs3 = float(rank_obj @ res3.x)
        print(f"  Rank sum: {rs3:.4f}, points: {sum(res3.x):.4f}")
        print(f"  Y: {[f'{y:.3f}' for y in res3.x]}")
    results["lp_wang_rank"] = {
        "feasible": bool(res3.success),
        "message": str(res3.message),
        "rank_sum": float(rank_obj @ res3.x) if res3.success and res3.x is not None else None,
    }

    # === Test 4: MILP Wang + rank (CORRECT: Y_o integer, bounds [0, s_o]) ===
    print(f"\n=== Test 4: MILP Wang + rank >= {rank_threshold} (time limit {args.milp_time}s) ===")
    integrality = np.ones(nvar)
    wang_constr = LinearConstraint(A_wang, ub=wang_rhs)
    eq_constr = LinearConstraint(A_eq, lb=b_eq, ub=b_eq)
    rank_constr = LinearConstraint(rank_obj.reshape(1, -1), lb=float(rank_threshold))
    int_bounds = SPBounds(lb=0, ub=var_sizes)
    try:
        res4 = milp(c_zero, constraints=[wang_constr, eq_constr, rank_constr],
                     integrality=integrality, bounds=int_bounds,
                     options={"time_limit": args.milp_time})
        print(f"  Status: {res4.message}")
        print(f"  Feasible: {res4.success}")
        if res4.success and res4.x is not None:
            sol4 = [int(round(y)) for y in res4.x]
            rs4 = sum(int(var_ranks[i]) * sol4[i] for i in range(nvar))
            pts4 = sum(sol4)
            print(f"  Y: {sol4}")
            print(f"  Points: {pts4}, Rank sum: {rs4}")
            # Verify Wang constraints
            wang_lhs = A_wang.dot(np.array(sol4, dtype=float))
            wang_viol = int(np.sum(wang_lhs > wang_rhs + 1e-9))
            print(f"  Wang violations: {wang_viol}")
        results["milp_wang_rank"] = {
            "status": str(res4.message),
            "feasible": bool(res4.success),
            "solution": [int(round(y)) for y in res4.x] if res4.success and res4.x is not None else None,
            "rank_sum": rs4 if res4.success and res4.x is not None else None,
            "wang_violations": wang_viol if res4.success and res4.x is not None else None,
        }
    except Exception as e:
        print(f"  Error: {e}")
        results["milp_wang_rank"] = {"error": str(e)}

    # === Test 5: MILP Wang only (no rank constraint) ===
    print(f"\n=== Test 5: MILP Wang only (no rank) ===")
    try:
        res5 = milp(rank_obj, constraints=[wang_constr, eq_constr],
                     integrality=integrality, bounds=int_bounds,
                     options={"time_limit": args.milp_time})
        print(f"  Status: {res5.message}")
        if res5.success and res5.x is not None:
            sol5 = [int(round(y)) for y in res5.x]
            rs5 = sum(int(var_ranks[i]) * sol5[i] for i in range(nvar))
            print(f"  Y: {sol5}")
            print(f"  Rank sum: {rs5}, Points: {sum(sol5)}")
        results["milp_wang_only_minrank"] = {
            "feasible": bool(res5.success),
            "min_rank_sum": rs5 if res5.success and res5.x is not None else None,
            "solution": [int(round(y)) for y in res5.x] if res5.success and res5.x is not None else None,
        }
    except Exception as e:
        print(f"  Error: {e}")

    # === Test 6: MILP Wang + rank with tighter thresholds ===
    for thr in [rank_threshold, rank_threshold + 1, rank_threshold + 2]:
        print(f"\n=== Test 6: MILP Wang + rank >= {thr} ===")
        rc = LinearConstraint(rank_obj.reshape(1, -1), lb=float(thr))
        try:
            r6 = milp(c_zero, constraints=[wang_constr, eq_constr, rc],
                       integrality=integrality, bounds=int_bounds,
                       options={"time_limit": args.milp_time})
            print(f"  Feasible: {r6.success}, Status: {r6.message}")
            if r6.success and r6.x is not None:
                s6 = [int(round(y)) for y in r6.x]
                rs6 = sum(int(var_ranks[i]) * s6[i] for i in range(nvar))
                print(f"  Y: {s6}, Rank: {rs6}, Pts: {sum(s6)}")
        except Exception as e:
            print(f"  Error: {e}")

    elapsed = time.time() - t0
    output = {
        "schema": "rank_orbit_milp_v2",
        "pivot": pivot, "pivot_rank": pivot_rank,
        "length": length, "rank_threshold": rank_threshold,
        "n_wang_rows": n_wang, "n_var": nvar,
        "var_sizes": [int(s) for s in var_sizes],
        "var_ranks": [int(r) for r in var_ranks],
        "var_orbit_reps": [orbits[o][0] for o in var_orbits],
        "elapsed_sec": elapsed,
        "results": results,
    }
    args.out.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    print(f"\nTotal: {elapsed:.1f}s -> {args.out}")

if __name__ == "__main__":
    main()
