#!/usr/bin/env python3
"""analysis: enumerate invariant point-count branches for the E11 Wang pair lift.

For an actual 19-point support S, the E11 stabilizer point orbits O_a have
integer counts n_a=|S∩O_a|.  Averaging over the stabilizer gives x_a=n_a/|O_a|
while retaining shared pair-correlation variables y_j.  This script enumerates
all feasible six-tuples n_a with sum 19, fixes x accordingly, and tests whether
there exist continuous y_j satisfying the analysis pair RLT constraints.  It can
also include analysis triangle inequalities.

The scan gives a branch map for the invariant necessary conditions.  Feasible
branches are not supports.  LP infeasibility is floating evidence unless later
converted into exact/replayable proof, but exact rational residual checks are
reported for any displayed feasible branch.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
from scipy import sparse
from scipy.optimize import linprog

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import build_core_constraints  # noqa: E402
from rlt_pair_lift import LUT_PATH, build_lp, build_stabilizer, compute_pair_orbits, compute_point_orbits  # noqa: E402
from rlt_triangle_integrality import build_triangle_constraints, dense_rows_to_csr, make_pair_metadata  # noqa: E402

OUT = ROOT / "workspace/data/point_count_branches"


def enumerate_count_vectors(sizes: List[int]) -> List[List[int]]:
    out = []
    # The sizes are all >= the possible counts except n_total=19, so only cap by min(size,19).
    limits = [min(s, 19) for s in sizes]
    for vals in product(*(range(lim + 1) for lim in limits)):
        if sum(vals) == 19:
            out.append(list(vals))
    return out


def fixed_x_lp(A_eq, b_eq, A_ub, b_ub, sizes: List[int], counts: List[int], K: int, M: int):
    N = K + M
    fixed_x = np.array([counts[a] / sizes[a] for a in range(K)], dtype=float)
    # Eliminate x variables, leaving y variables only.
    Aeq_y = A_eq[:, K:]
    beq_y = b_eq - A_eq[:, :K] @ fixed_x
    Aub_y = A_ub[:, K:]
    bub_y = b_ub - A_ub[:, :K] @ fixed_x
    res = linprog(np.zeros(M), A_ub=Aub_y, b_ub=bub_y, A_eq=Aeq_y, b_eq=beq_y,
                  bounds=[(0.0, 1.0)] * M, method="highs")
    return res, fixed_x, Aeq_y, beq_y, Aub_y, bub_y


def exact_residuals_for_branch(A_eq, b_eq, A_ub, b_ub, sizes: List[int], pair_sizes: List[int],
                               counts: List[int], y_float: np.ndarray, K: int, M: int) -> dict:
    # Convert y to a bounded rational approximation.  This is not a proof of exact LP feasibility;
    # it is a reproducibility check on displayed numerical witnesses.
    z = []
    for a in range(K):
        z.append(Fraction(counts[a], sizes[a]))
    for j in range(M):
        z.append(Fraction(float(y_float[j])).limit_denominator(10**9))

    def row_val(A, i):
        start, end = A.indptr[i], A.indptr[i + 1]
        s = Fraction(0, 1)
        for idx, coeff in zip(A.indices[start:end], A.data[start:end]):
            c = int(round(float(coeff)))
            if c:
                s += c * z[int(idx)]
        return s

    max_eq = Fraction(0, 1); first_eq = None
    for i in range(A_eq.shape[0]):
        diff = row_val(A_eq, i) - Fraction(int(round(float(b_eq[i]))), 1)
        if abs(diff) > max_eq:
            max_eq = abs(diff)
        if diff != 0 and first_eq is None:
            first_eq = {"row": i, "diff": str(diff)}
    max_ub = Fraction(0, 1); first_ub = None; nbad = 0
    for i in range(A_ub.shape[0]):
        diff = row_val(A_ub, i) - Fraction(int(round(float(b_ub[i]))), 1)
        if diff > 0:
            nbad += 1
            if diff > max_ub:
                max_ub = diff
            if first_ub is None:
                first_ub = {"row": i, "diff": str(diff)}
    return {
        "rationalized_y_denominator_limit": 10**9,
        "max_abs_eq_residual": str(max_eq),
        "max_ub_violation": str(max_ub),
        "violated_ub_count": nbad,
        "first_eq_bad": first_eq,
        "first_ub_bad": first_ub,
        "rationalized_exact_feasible": bool(max_eq == 0 and max_ub == 0),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--triangles", action="store_true", help="include triangle/Fortet inequalities")
    ap.add_argument("--max-records", type=int, default=0, help="optional limit on number of branches scanned")
    ap.add_argument("--sample-feasible", type=int, default=10)
    args = ap.parse_args()

    OUT.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    print(f"analysis point-count branch scan triangles={args.triangles}")

    print("  building orbits and full RLT base")
    perms = build_stabilizer()
    pt_orb, point_orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, M = compute_pair_orbits(perms, pt_orb)
    K = len(point_orbits); N = K + M
    lut, _ = load_lut(LUT_PATH)
    records, wmeta = build_core_constraints(CoreQuotient(1), lut)
    eq_rows, eq_b_list, ub_rows, ub_b_list, K2, M2, N2, n_aj = build_lp(records, pt_orb, point_orbits, pair_orb, M, pair_ep)
    assert (K2, M2, N2) == (K, M, N)
    A_eq = dense_rows_to_csr(eq_rows, N)
    A_ub = dense_rows_to_csr(ub_rows, N)
    b_eq = np.array(eq_b_list, dtype=float)
    b_ub = np.array(ub_b_list, dtype=float)
    tri_meta = None
    if args.triangles:
        A_tri, b_tri, tri_meta = build_triangle_constraints(pt_orb, pair_orb, K, M)
        A_ub = sparse.vstack([A_ub, A_tri], format="csr")
        b_ub = np.concatenate([b_ub, b_tri])

    sizes = [len(o) for o in point_orbits]
    branches = enumerate_count_vectors(sizes)
    if args.max_records and args.max_records < len(branches):
        branches = branches[:args.max_records]
    print(f"  point orbit reps {[o[0] for o in point_orbits]}, sizes {sizes}; branches={len(branches)}")

    status_counts = {}
    feasible = []
    infeasible = []
    omitted_hist = {}
    per_orbit_max_feasible = [None] * K
    per_orbit_min_feasible = [None] * K

    for idx, counts in enumerate(branches):
        res, fixed_x, Aeq_y, beq_y, Aub_y, bub_y = fixed_x_lp(A_eq, b_eq, A_ub, b_ub, sizes, counts, K, M)
        status = "feasible" if res.status == 0 else ("infeasible" if res.status == 2 else f"status_{res.status}")
        status_counts[status] = status_counts.get(status, 0) + 1
        if status == "feasible":
            omitted = sum(counts[:4])
            omitted_hist[str(omitted)] = omitted_hist.get(str(omitted), 0) + 1
            for a, val in enumerate(counts):
                if per_orbit_max_feasible[a] is None or val > per_orbit_max_feasible[a]:
                    per_orbit_max_feasible[a] = val
                if per_orbit_min_feasible[a] is None or val < per_orbit_min_feasible[a]:
                    per_orbit_min_feasible[a] = val
            rec = {
                "branch_index": idx,
                "counts": counts,
                "omitted_n_0_3": omitted,
                "status_message": res.message,
                "nonzero_y_orbits_1e-10": int(np.sum(np.array(res.x) > 1e-10)) if res.x is not None else None,
            }
            if len(feasible) < args.sample_feasible and res.x is not None:
                rec["y_by_pair_orbit"] = [float(v) for v in res.x]
                rec["m_float_by_pair_orbit"] = [float(pair_sizes[j] * res.x[j]) for j in range(M)]
                rec["exact_residuals_after_rationalizing_y"] = exact_residuals_for_branch(
                    A_eq, b_eq, A_ub, b_ub, sizes, pair_sizes, counts, np.array(res.x), K, M)
            feasible.append(rec)
        else:
            if len(infeasible) < 20:
                infeasible.append({"branch_index": idx, "counts": counts, "status": status, "status_message": str(res.message)})
        if idx and idx % 100 == 0:
            print(f"    processed {idx}/{len(branches)} status_counts={status_counts}")

    result = {
        "schema": "point_count_branch_scan_v1",
        "triangles": bool(args.triangles),
        "triangle_meta": tri_meta,
        "point_orbit_reps": [int(o[0]) for o in point_orbits],
        "point_orbit_sizes": sizes,
        "pair_orbit_count": M,
        "pair_orbit_size_histogram": {str(k): int(v) for k, v in sorted(__import__('collections').Counter(pair_sizes).items())},
        "wang_records": len(records),
        "n_eq_constraints": int(A_eq.shape[0]),
        "n_ub_constraints": int(A_ub.shape[0]),
        "branch_count": len(branches),
        "status_counts": status_counts,
        "feasible_branch_count": len(feasible),
        "feasible_omitted_n_0_3_histogram": dict(sorted(omitted_hist.items(), key=lambda kv: int(kv[0]))),
        "per_orbit_min_feasible_count": per_orbit_min_feasible,
        "per_orbit_max_feasible_count": per_orbit_max_feasible,
        "first_feasible_branches": feasible[:args.sample_feasible],
        "first_infeasible_branches": infeasible,
        "elapsed_sec": round(time.time() - t0, 3),
        "interpretation_note": "Feasible branches are invariant pair-relaxation branches, not actual supports. Floating infeasibility is not a theorem without exact proof.",
    }
    name = "point_count_branch_scan_triangles.json" if args.triangles else "point_count_branch_scan_base.json"
    path = OUT / name
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"saved {path}")
    print(json.dumps({k: result[k] for k in ["triangles", "branch_count", "status_counts", "feasible_omitted_n_0_3_histogram", "per_orbit_min_feasible_count", "per_orbit_max_feasible_count", "elapsed_sec"]}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
