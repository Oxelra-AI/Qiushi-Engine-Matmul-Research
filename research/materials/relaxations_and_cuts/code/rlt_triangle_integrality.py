#!/usr/bin/env python3
"""analysis: strengthen and interrogate the E11 Wang SA/RLT pair lift.

This script continues analysis.  It keeps the full 103-coordinate orbit-averaged
pair-correlation relaxation, tests whether the zero-objective solution's support
on point orbits 4+5 is forced by optimizing mass on the omitted point orbits,
adds orbit-deduplicated triangle/Fortet inequalities, and tests invariant-count
integrality for point and pair orbit counts.

The output is computational evidence for the E11 distinct projected-A branch over
F2.  A feasible relaxation is only a necessary-condition witness; an infeasible
MILP/LP from floating solvers is not a theorem without an exact proof artifact.
When an integer orbit-count witness is found, the script rechecks the continuous
linear constraints exactly from the rounded integer counts.
"""
from __future__ import annotations

import json
import math
import sys
import time
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import numpy as np
from scipy import sparse
from scipy.optimize import Bounds, LinearConstraint, linprog, milp

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import build_core_constraints  # noqa: E402
from rlt_pair_lift import (  # noqa: E402
    LUT_PATH,
    build_lp,
    build_stabilizer,
    compute_pair_orbits,
    compute_point_orbits,
)

OUT = ROOT / "workspace/data/rlt_triangle_integrality"


def dense_rows_to_csr(rows: List[List[float]], ncols: int) -> sparse.csr_matrix:
    data: List[float] = []
    indices: List[int] = []
    indptr = [0]
    for row in rows:
        for i, v in enumerate(row):
            if abs(v) > 0:
                data.append(float(v))
                indices.append(i)
        indptr.append(len(data))
    return sparse.csr_matrix((data, indices, indptr), shape=(len(rows), ncols), dtype=float)


def residual_stats(A_eq, b_eq, A_ub, b_ub, x: np.ndarray) -> dict:
    eq_res = np.array([]) if A_eq.shape[0] == 0 else A_eq @ x - b_eq
    ub_res = np.array([]) if A_ub.shape[0] == 0 else A_ub @ x - b_ub
    return {
        "max_abs_eq_residual": float(np.max(np.abs(eq_res))) if eq_res.size else 0.0,
        "max_ub_violation": float(max(0.0, np.max(ub_res))) if ub_res.size else 0.0,
        "min_ub_slack": float(np.min(-ub_res)) if ub_res.size else None,
        "tight_ub_count_1e-8": int(np.sum(np.abs(ub_res) <= 1e-8)) if ub_res.size else 0,
        "violated_ub_count_1e-8": int(np.sum(ub_res > 1e-8)) if ub_res.size else 0,
    }


def solution_record(label: str, res, c: np.ndarray, sense: str, point_orbits, pair_sizes,
                    pair_meta, A_eq, b_eq, A_ub, b_ub, K: int, M: int) -> dict:
    rec = {
        "label": label,
        "status_code": int(res.status),
        "status_message": str(res.message),
        "success": bool(res.status == 0),
        "sense": sense,
    }
    if res.status == 0 and res.x is not None:
        x = np.array(res.x, dtype=float)
        raw_obj = float(c @ x)
        if sense == "maximize_negative_c":
            objective_value = -raw_obj
        else:
            objective_value = raw_obj
        rec.update({
            "objective_value": objective_value,
            "raw_minimize_value": raw_obj,
            "residual_stats": residual_stats(A_eq, b_eq, A_ub, b_ub, x),
            "x_by_point_orbit": [float(x[a]) for a in range(K)],
            "n_mass_by_point_orbit": [float(len(point_orbits[a]) * x[a]) for a in range(K)],
            "y_by_pair_orbit": [float(x[K + j]) for j in range(M)],
            "m_mass_by_pair_orbit": [float(pair_sizes[j] * x[K + j]) for j in range(M)],
            "nonzero_y_orbits_1e-10": int(sum(1 for j in range(M) if x[K + j] > 1e-10)),
        })
        # Compact nonzero pair list for human inspection.
        nz = []
        for j in range(M):
            val = float(x[K + j])
            if val > 1e-10:
                meta = pair_meta[j]
                nz.append({
                    "pair_orbit": j,
                    "rep_pair": meta["rep_pair"],
                    "endpoint_orbits": meta["endpoint_orbits"],
                    "size": meta["size"],
                    "y": val,
                    "m_float": float(meta["size"] * val),
                })
        rec["nonzero_pair_details"] = nz
    return rec


def solve_lp_model(label: str, A_eq, b_eq, A_ub, b_ub, c: np.ndarray, sense: str,
                   point_orbits, pair_sizes, pair_meta, K: int, M: int,
                   time_limit_note: str = "") -> dict:
    n = K + M
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(0.0, 1.0)] * n, method="highs")
    rec = solution_record(label, res, c, sense, point_orbits, pair_sizes, pair_meta,
                          A_eq, b_eq, A_ub, b_ub, K, M)
    if time_limit_note:
        rec["note"] = time_limit_note
    return rec


def add_sparse_key(seen: set, rows: List[Tuple[List[int], List[float]]], coeffs: Dict[int, int]):
    clean = tuple(sorted((i, c) for i, c in coeffs.items() if c != 0))
    if clean and clean not in seen:
        seen.add(clean)
        rows.append(([i for i, _ in clean], [float(c) for _, c in clean]))


def build_triangle_constraints(pt_orb: List[int], pair_orb: Dict[Tuple[int, int], int],
                               K: int, M: int) -> Tuple[sparse.csr_matrix, np.ndarray, dict]:
    """Build unique invariant-variable triangle inequalities.

    For each distinct triple {p,q,r}, add the three Boolean-quadric inequalities
        y_pq + y_pr - y_qr <= x_p,
        y_pq + y_qr - y_pr <= x_q,
        y_pr + y_qr - y_pq <= x_r.
    In invariant variables many triples give identical coefficient vectors; we
    deduplicate by the final sparse coefficient pattern.
    """
    t0 = time.time()
    seen = set()
    rows: List[Tuple[List[int], List[float]]] = []
    raw = 0
    points = range(1, 256)
    for p in points:
        op = pt_orb[p]
        for q in range(p + 1, 256):
            oq = pt_orb[q]
            jpq = pair_orb[(p, q)]
            for r in range(q + 1, 256):
                orr = pt_orb[r]
                jpr = pair_orb[(p, r)]
                jqr = pair_orb[(q, r)]
                # Focus p.  Coefficients must be accumulated because two
                # unordered pairs in a labelled triangle may lie in the same
                # invariant pair orbit.
                coeff: Dict[int, int] = {}
                for idx, val in ((op, -1), (K + jpq, 1), (K + jpr, 1), (K + jqr, -1)):
                    coeff[idx] = coeff.get(idx, 0) + val
                add_sparse_key(seen, rows, coeff); raw += 1
                # Focus q.
                coeff = {}
                for idx, val in ((oq, -1), (K + jpq, 1), (K + jqr, 1), (K + jpr, -1)):
                    coeff[idx] = coeff.get(idx, 0) + val
                add_sparse_key(seen, rows, coeff); raw += 1
                # Focus r.
                coeff = {}
                for idx, val in ((orr, -1), (K + jpr, 1), (K + jqr, 1), (K + jpq, -1)):
                    coeff[idx] = coeff.get(idx, 0) + val
                add_sparse_key(seen, rows, coeff); raw += 1
    data: List[float] = []
    indices: List[int] = []
    indptr = [0]
    for cols, vals in rows:
        data.extend(vals); indices.extend(cols); indptr.append(len(data))
    A_tri = sparse.csr_matrix((data, indices, indptr), shape=(len(rows), K + M), dtype=float)
    meta = {
        "raw_triangle_inequalities": raw,
        "unique_triangle_inequalities": len(rows),
        "elapsed_sec": round(time.time() - t0, 3),
    }
    return A_tri, np.zeros(len(rows), dtype=float), meta


def make_pair_metadata(pair_orb: Dict[Tuple[int, int], int], pair_sizes: List[int], pair_ep) -> List[dict]:
    reps = [None] * len(pair_sizes)
    for pair, j in pair_orb.items():
        if reps[j] is None or pair < reps[j]:
            reps[j] = pair
    return [
        {
            "pair_orbit": j,
            "rep_pair": [int(reps[j][0]), int(reps[j][1])],
            "endpoint_orbits": [int(pair_ep[j][0]), int(pair_ep[j][1])],
            "size": int(pair_sizes[j]),
        }
        for j in range(len(pair_sizes))
    ]


def build_linear_constraint(A_eq, b_eq, A_ub, b_ub) -> LinearConstraint:
    A = sparse.vstack([A_eq, A_ub], format="csr")
    lb = np.concatenate([b_eq, np.full(A_ub.shape[0], -np.inf)])
    ub = np.concatenate([b_eq, b_ub])
    return LinearConstraint(A, lb, ub)


def solve_point_count_milp(label: str, A_eq, b_eq, A_ub, b_ub, point_orbits, K: int, M: int,
                           maximize_omitted: bool, time_limit: float) -> dict:
    """MILP with x_a = n_a/|O_a| and integer n_a; y remains continuous."""
    N = K + M
    sizes = np.array([len(o) for o in point_orbits], dtype=float)
    zero_eq_n = sparse.csr_matrix((A_eq.shape[0], K))
    zero_ub_n = sparse.csr_matrix((A_ub.shape[0], K))
    Aeq_aug = sparse.hstack([A_eq, zero_eq_n], format="csr")
    Aub_aug = sparse.hstack([A_ub, zero_ub_n], format="csr")
    link_rows = []
    link_cols = []
    link_data = []
    for a in range(K):
        link_rows.extend([a, a])
        link_cols.extend([a, N + a])
        link_data.extend([sizes[a], -1.0])
    A_link = sparse.csr_matrix((link_data, (link_rows, link_cols)), shape=(K, N + K))
    Aeq_aug = sparse.vstack([Aeq_aug, A_link], format="csr")
    b_eq_aug = np.concatenate([b_eq, np.zeros(K)])
    constraint = build_linear_constraint(Aeq_aug, b_eq_aug, Aub_aug, b_ub)
    lb = np.zeros(N + K)
    ub = np.concatenate([np.ones(N), sizes])
    integrality = np.zeros(N + K, dtype=int)
    integrality[N:N + K] = 1
    c = np.zeros(N + K)
    if maximize_omitted:
        c[N:N + 4] = -1.0
    t0 = time.time()
    res = milp(c=c, integrality=integrality, bounds=Bounds(lb, ub),
               constraints=constraint,
               options={"time_limit": time_limit, "mip_rel_gap": 0.0, "disp": False})
    rec = {
        "label": label,
        "model": "point_count_integrality_y_continuous",
        "maximize_omitted": maximize_omitted,
        "status_code": int(res.status),
        "status_message": str(res.message),
        "success": bool(res.success),
        "elapsed_sec": round(time.time() - t0, 3),
        "time_limit_sec": time_limit,
    }
    if res.x is not None:
        z = np.array(res.x, dtype=float)
        n_vals = [int(round(z[N + a])) for a in range(K)]
        rec.update({
            "objective_value": float(res.fun) if res.fun is not None else None,
            "n_by_point_orbit_rounded": n_vals,
            "n_total": int(sum(n_vals)),
            "omitted_n_0_3": int(sum(n_vals[:4])),
            "x_by_point_orbit_from_solution": [float(z[a]) for a in range(K)],
            "continuous_residual_stats": residual_stats(A_eq, b_eq, A_ub, b_ub, z[:N]),
        })
    return rec


def solve_pair_count_milp(label: str, A_eq, b_eq, A_ub, b_ub, point_orbits, pair_sizes,
                          K: int, M: int, maximize_omitted: bool, time_limit: float) -> dict:
    """MILP with integer orbit counts n_a and m_j, linked to x,y."""
    N = K + M
    sizes = np.array([len(o) for o in point_orbits], dtype=float)
    psizes = np.array(pair_sizes, dtype=float)
    extra = K + M
    zero_eq = sparse.csr_matrix((A_eq.shape[0], extra))
    zero_ub = sparse.csr_matrix((A_ub.shape[0], extra))
    Aeq_aug = sparse.hstack([A_eq, zero_eq], format="csr")
    Aub_aug = sparse.hstack([A_ub, zero_ub], format="csr")

    # Links: |O_a| x_a - n_a = 0 and |P_j| y_j - m_j = 0.
    rows = []
    cols = []
    data = []
    row = 0
    for a in range(K):
        rows.extend([row, row]); cols.extend([a, N + a]); data.extend([sizes[a], -1.0]); row += 1
    for j in range(M):
        rows.extend([row, row]); cols.extend([K + j, N + K + j]); data.extend([psizes[j], -1.0]); row += 1
    # Pair-total count, redundant for true supports but useful for numerical consistency.
    for j in range(M):
        rows.append(row); cols.append(N + K + j); data.append(1.0)
    A_link = sparse.csr_matrix((data, (rows, cols)), shape=(K + M + 1, N + extra))
    b_link = np.concatenate([np.zeros(K + M), np.array([171.0])])

    Aeq_aug = sparse.vstack([Aeq_aug, A_link], format="csr")
    b_eq_aug = np.concatenate([b_eq, b_link])
    constraint = build_linear_constraint(Aeq_aug, b_eq_aug, Aub_aug, b_ub)
    lb = np.zeros(N + extra)
    ub = np.concatenate([np.ones(N), sizes, psizes])
    integrality = np.zeros(N + extra, dtype=int)
    integrality[N:N + extra] = 1
    c = np.zeros(N + extra)
    if maximize_omitted:
        c[N:N + 4] = -1.0
    t0 = time.time()
    res = milp(c=c, integrality=integrality, bounds=Bounds(lb, ub),
               constraints=constraint,
               options={"time_limit": time_limit, "mip_rel_gap": 0.0, "disp": False})
    rec = {
        "label": label,
        "model": "point_and_pair_count_integrality",
        "maximize_omitted": maximize_omitted,
        "status_code": int(res.status),
        "status_message": str(res.message),
        "success": bool(res.success),
        "elapsed_sec": round(time.time() - t0, 3),
        "time_limit_sec": time_limit,
    }
    if res.x is not None:
        z = np.array(res.x, dtype=float)
        n_vals = [int(round(z[N + a])) for a in range(K)]
        m_vals = [int(round(z[N + K + j])) for j in range(M)]
        xy = np.zeros(N, dtype=float)
        for a in range(K):
            xy[a] = n_vals[a] / sizes[a]
        for j in range(M):
            xy[K + j] = m_vals[j] / psizes[j]
        rec.update({
            "objective_value": float(res.fun) if res.fun is not None else None,
            "n_by_point_orbit_rounded": n_vals,
            "n_total": int(sum(n_vals)),
            "omitted_n_0_3": int(sum(n_vals[:4])),
            "nonzero_pair_count_orbits": int(sum(1 for m in m_vals if m != 0)),
            "m_total": int(sum(m_vals)),
            "m_by_pair_orbit_rounded": m_vals,
            "continuous_residual_stats_from_solver_xy": residual_stats(A_eq, b_eq, A_ub, b_ub, z[:N]),
            "continuous_residual_stats_from_rounded_counts": residual_stats(A_eq, b_eq, A_ub, b_ub, xy),
        })
        rec["exact_fraction_check"] = exact_fraction_check(A_eq, b_eq, A_ub, b_ub, n_vals, m_vals,
                                                            [int(s) for s in sizes], [int(s) for s in psizes], K, M)
    return rec


def exact_fraction_check(A_eq, b_eq, A_ub, b_ub, n_vals: List[int], m_vals: List[int],
                         sizes: List[int], pair_sizes: List[int], K: int, M: int) -> dict:
    z: List[Fraction] = []
    for a in range(K):
        z.append(Fraction(int(n_vals[a]), int(sizes[a])))
    for j in range(M):
        z.append(Fraction(int(m_vals[j]), int(pair_sizes[j])))

    def row_value(A, i: int) -> Fraction:
        start, end = A.indptr[i], A.indptr[i + 1]
        s = Fraction(0, 1)
        for idx, val in zip(A.indices[start:end], A.data[start:end]):
            c = int(round(float(val)))
            if c:
                s += c * z[int(idx)]
        return s

    max_eq_abs = Fraction(0, 1)
    first_eq_bad = None
    for i in range(A_eq.shape[0]):
        diff = row_value(A_eq, i) - Fraction(int(round(float(b_eq[i]))), 1)
        if abs(diff) > max_eq_abs:
            max_eq_abs = abs(diff)
        if diff != 0 and first_eq_bad is None:
            first_eq_bad = {"row": i, "diff": str(diff)}
    max_ub_viol = Fraction(0, 1)
    first_ub_bad = None
    violated = 0
    for i in range(A_ub.shape[0]):
        diff = row_value(A_ub, i) - Fraction(int(round(float(b_ub[i]))), 1)
        if diff > 0:
            violated += 1
            if diff > max_ub_viol:
                max_ub_viol = diff
            if first_ub_bad is None:
                first_ub_bad = {"row": i, "diff": str(diff)}
    return {
        "checked": True,
        "max_abs_eq_residual": str(max_eq_abs),
        "first_eq_bad": first_eq_bad,
        "max_ub_violation": str(max_ub_viol),
        "violated_ub_count": int(violated),
        "first_ub_bad": first_ub_bad,
        "is_exact_feasible": bool(max_eq_abs == 0 and max_ub_viol == 0),
    }


def main():
    t0 = time.time()
    OUT.mkdir(parents=True, exist_ok=True)
    print("analysis: RLT mass optimization, triangles, and invariant-count integrality")

    print("  1. Build stabilizer/orbits")
    t = time.time()
    perms = build_stabilizer()
    pt_orb, point_orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, M = compute_pair_orbits(perms, pt_orb)
    K = len(point_orbits)
    pair_meta = make_pair_metadata(pair_orb, pair_sizes, pair_ep)
    print(f"     |G|={len(perms)}, point orbit sizes={[len(o) for o in point_orbits]}, pair_orbits={M}, elapsed={time.time()-t:.1f}s")

    print("  2. Build complete E11 Wang RLT LP")
    t = time.time()
    lut, _ = load_lut(LUT_PATH)
    records, wmeta = build_core_constraints(CoreQuotient(1), lut)
    eq_rows, eq_b_list, ub_rows, ub_b_list, K2, M2, N, n_aj = build_lp(records, pt_orb, point_orbits, pair_orb, M, pair_ep)
    assert K2 == K and M2 == M and N == K + M
    A_eq = dense_rows_to_csr(eq_rows, N)
    A_ub = dense_rows_to_csr(ub_rows, N)
    b_eq = np.array(eq_b_list, dtype=float)
    b_ub = np.array(ub_b_list, dtype=float)
    print(f"     records={len(records)}, A_eq={A_eq.shape}, A_ub={A_ub.shape}, elapsed={time.time()-t:.1f}s")

    sizes = np.array([len(o) for o in point_orbits], dtype=float)
    metadata = {
        "schema": "rlt_triangle_integrality_v1",
        "point_orbit_reps": [int(o[0]) for o in point_orbits],
        "point_orbit_sizes": [int(len(o)) for o in point_orbits],
        "pair_orbit_size_histogram": {str(k): int(v) for k, v in sorted(Counter(pair_sizes).items())},
        "pair_metadata": pair_meta,
        "wang_record_count": len(records),
        "base_n_eq": int(A_eq.shape[0]),
        "base_n_ub": int(A_ub.shape[0]),
        "base_n_variables": int(N),
    }

    print("  3. Base LP objectives: test whether orbits 0-3 are forced to zero")
    lp_results = []
    zero = np.zeros(N)
    lp_results.append(solve_lp_model("base_zero_objective_full_witness", A_eq, b_eq, A_ub, b_ub, zero, "minimize", point_orbits, pair_sizes, pair_meta, K, M))
    c = np.zeros(N); c[:4] = -sizes[:4]
    lp_results.append(solve_lp_model("base_max_total_mass_orbits_0_3", A_eq, b_eq, A_ub, b_ub, c, "maximize_negative_c", point_orbits, pair_sizes, pair_meta, K, M))
    c = np.zeros(N); c[:4] = sizes[:4]
    lp_results.append(solve_lp_model("base_min_total_mass_orbits_0_3", A_eq, b_eq, A_ub, b_ub, c, "minimize", point_orbits, pair_sizes, pair_meta, K, M))
    for a in range(4):
        c = np.zeros(N); c[a] = -sizes[a]
        lp_results.append(solve_lp_model(f"base_max_mass_orbit_{a}", A_eq, b_eq, A_ub, b_ub, c, "maximize_negative_c", point_orbits, pair_sizes, pair_meta, K, M))
    print("     base LP objective summary:")
    for r in lp_results:
        print(f"       {r['label']}: success={r['success']} objective={r.get('objective_value')}")

    print("  4. Build and add triangle inequalities")
    t = time.time()
    A_tri, b_tri, tri_meta = build_triangle_constraints(pt_orb, pair_orb, K, M)
    A_ub_tri = sparse.vstack([A_ub, A_tri], format="csr")
    b_ub_tri = np.concatenate([b_ub, b_tri])
    print(f"     raw={tri_meta['raw_triangle_inequalities']}, unique={tri_meta['unique_triangle_inequalities']}, elapsed={time.time()-t:.1f}s")

    print("  5. Triangle-strengthened LP objectives")
    tri_lp_results = []
    tri_lp_results.append(solve_lp_model("triangle_zero_objective_full_witness", A_eq, b_eq, A_ub_tri, b_ub_tri, zero, "minimize", point_orbits, pair_sizes, pair_meta, K, M))
    c = np.zeros(N); c[:4] = -sizes[:4]
    tri_lp_results.append(solve_lp_model("triangle_max_total_mass_orbits_0_3", A_eq, b_eq, A_ub_tri, b_ub_tri, c, "maximize_negative_c", point_orbits, pair_sizes, pair_meta, K, M))
    c = np.zeros(N); c[:4] = sizes[:4]
    tri_lp_results.append(solve_lp_model("triangle_min_total_mass_orbits_0_3", A_eq, b_eq, A_ub_tri, b_ub_tri, c, "minimize", point_orbits, pair_sizes, pair_meta, K, M))
    for a in range(4):
        c = np.zeros(N); c[a] = -sizes[a]
        tri_lp_results.append(solve_lp_model(f"triangle_max_mass_orbit_{a}", A_eq, b_eq, A_ub_tri, b_ub_tri, c, "maximize_negative_c", point_orbits, pair_sizes, pair_meta, K, M))
    print("     triangle LP objective summary:")
    for r in tri_lp_results:
        print(f"       {r['label']}: success={r['success']} objective={r.get('objective_value')}")

    print("  6. Invariant point-count integrality MILPs")
    point_milp_results = []
    point_milp_results.append(solve_point_count_milp("base_point_counts_feasibility", A_eq, b_eq, A_ub, b_ub, point_orbits, K, M, False, 180.0))
    point_milp_results.append(solve_point_count_milp("base_point_counts_max_omitted", A_eq, b_eq, A_ub, b_ub, point_orbits, K, M, True, 180.0))
    point_milp_results.append(solve_point_count_milp("triangle_point_counts_feasibility", A_eq, b_eq, A_ub_tri, b_ub_tri, point_orbits, K, M, False, 180.0))
    point_milp_results.append(solve_point_count_milp("triangle_point_counts_max_omitted", A_eq, b_eq, A_ub_tri, b_ub_tri, point_orbits, K, M, True, 180.0))
    for r in point_milp_results:
        print(f"       {r['label']}: status={r['status_message']} n={r.get('n_by_point_orbit_rounded')} omitted={r.get('omitted_n_0_3')}")

    print("  7. Invariant point+pair-count integrality MILPs")
    pair_milp_results = []
    pair_milp_results.append(solve_pair_count_milp("base_pair_counts_feasibility", A_eq, b_eq, A_ub, b_ub, point_orbits, pair_sizes, K, M, False, 240.0))
    pair_milp_results.append(solve_pair_count_milp("triangle_pair_counts_feasibility", A_eq, b_eq, A_ub_tri, b_ub_tri, point_orbits, pair_sizes, K, M, False, 240.0))
    for r in pair_milp_results:
        print(f"       {r['label']}: status={r['status_message']} n={r.get('n_by_point_orbit_rounded')} exact={r.get('exact_fraction_check',{}).get('is_exact_feasible')}")

    result = {
        **metadata,
        "triangle_meta": tri_meta,
        "base_lp_results": lp_results,
        "triangle_lp_results": tri_lp_results,
        "point_count_milp_results": point_milp_results,
        "pair_count_milp_results": pair_milp_results,
        "elapsed_sec": round(time.time() - t0, 3),
        "interpretation_note": (
            "LP/MILP solver infeasibility here is computational evidence only unless converted to a replayable exact proof. "
            "A pair-count MILP witness with exact_fraction_check.is_exact_feasible=true is an exact rational witness for this relaxation, "
            "not a Wang support or tensor decomposition."
        ),
    }
    out_path = OUT / "rlt_triangle_integrality_result.json"
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"  saved {out_path}")
    compact = {
        "triangle_meta": tri_meta,
        "base_objectives": [(r["label"], r["success"], r.get("objective_value"), r.get("n_mass_by_point_orbit")) for r in lp_results],
        "triangle_objectives": [(r["label"], r["success"], r.get("objective_value"), r.get("n_mass_by_point_orbit")) for r in tri_lp_results],
        "point_count_statuses": [(r["label"], r["status_message"], r.get("n_by_point_orbit_rounded"), r.get("omitted_n_0_3")) for r in point_milp_results],
        "pair_count_statuses": [(r["label"], r["status_message"], r.get("n_by_point_orbit_rounded"), r.get("omitted_n_0_3"), r.get("exact_fraction_check",{}).get("is_exact_feasible")) for r in pair_milp_results],
        "elapsed_sec": result["elapsed_sec"],
    }
    print(json.dumps(compact, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
