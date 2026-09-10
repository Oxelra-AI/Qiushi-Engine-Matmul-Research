#!/usr/bin/env python3
"""analysis: exact invariant block-count CP-SAT for E11 shared-pair relaxation.

An actual 19-point support S induces integer point-orbit counts n_a and integer
pair-orbit counts m_j.  In addition to the analysis linear RLT constraints,
these counts obey graph block equations:
    sum_{P_j inside O_a x O_b} m_j = n_a n_b       (a<b)
    sum_{P_j inside O_a}       m_j = n_a(n_a-1)/2 (a=a)
This script adds those exact nonlinear integer equations using CP-SAT integer
multiplication, after scaling all orbit-averaged LP inequalities by lcm=1152.
Feasibility still does not construct a support; it is a stronger necessary
condition on invariant counts.
"""
from __future__ import annotations

import argparse, json, sys, time
from collections import Counter, defaultdict
from pathlib import Path
from typing import List, Tuple

import numpy as np
from scipy import sparse

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import build_core_constraints  # noqa: E402
from rlt_pair_lift import LUT_PATH, build_lp, build_stabilizer, compute_pair_orbits, compute_point_orbits  # noqa: E402
from rlt_triangle_integrality import (  # noqa: E402
    build_triangle_constraints,
    dense_rows_to_csr,
    exact_fraction_check,
    make_pair_metadata,
)

OUT = ROOT / "workspace/data/invariant_pair_block"
SCALE = 1152


def add_scaled_linear_constraints(model, A, b, n_vars, m_vars, point_sizes, pair_sizes, equality: bool,
                                  name_prefix: str, max_rows: int | None = None) -> int:
    """Substitute x=n/|O|, y=m/|P| and scale by 1152."""
    rows_added = 0
    for r in range(A.shape[0]):
        if max_rows is not None and rows_added >= max_rows:
            break
        start, end = A.indptr[r], A.indptr[r + 1]
        terms = []
        for idx, coeff in zip(A.indices[start:end], A.data[start:end]):
            c = int(round(float(coeff)))
            if c == 0:
                continue
            idx = int(idx)
            if idx < len(n_vars):
                denom = int(point_sizes[idx]); var = n_vars[idx]
            else:
                denom = int(pair_sizes[idx - len(n_vars)]); var = m_vars[idx - len(n_vars)]
            mult = SCALE // denom
            if SCALE % denom != 0:
                raise ValueError((idx, denom))
            terms.append(c * mult * var)
        rhs = int(round(float(b[r]) * SCALE))
        if equality:
            model.Add(sum(terms) == rhs)
        else:
            model.Add(sum(terms) <= rhs)
        rows_added += 1
    return rows_added


def exact_count_check(A_eq, b_eq, A_ub, b_ub, n_vals, m_vals, point_sizes, pair_sizes, K, M):
    return exact_fraction_check(A_eq, b_eq, A_ub, b_ub, n_vals, m_vals, point_sizes, pair_sizes, K, M)


def solve_model(label: str, A_eq, b_eq, A_ub, b_ub, point_orbits, pair_sizes, pair_ep,
                K: int, M: int, solver_time: float, workers: int, seed: int,
                objective: str, force_zero_omitted: bool) -> dict:
    from ortools.sat.python import cp_model
    point_sizes = [len(o) for o in point_orbits]
    model = cp_model.CpModel()
    n = [model.NewIntVar(0, min(point_sizes[a], 19), f"n_{a}") for a in range(K)]
    m = [model.NewIntVar(0, min(int(pair_sizes[j]), 171), f"m_{j}") for j in range(M)]
    model.Add(sum(n) == 19)
    model.Add(sum(m) == 171)
    if force_zero_omitted:
        for a in range(4):
            model.Add(n[a] == 0)

    # Actual support block pair totals.
    by_block = defaultdict(list)
    for j, (a, b) in enumerate(pair_ep):
        by_block[(int(a), int(b))].append(j)
    diag_products = []
    cross_products = []
    for a in range(K):
        block_sum = sum(m[j] for j in by_block[(a, a)])
        sq = model.NewIntVar(0, point_sizes[a] * point_sizes[a], f"sq_{a}")
        model.AddMultiplicationEquality(sq, [n[a], n[a]])
        model.Add(2 * block_sum == sq - n[a])
        diag_products.append(sq)
    for a in range(K):
        for b in range(a + 1, K):
            block_sum = sum(m[j] for j in by_block[(a, b)])
            prod = model.NewIntVar(0, point_sizes[a] * point_sizes[b], f"prod_{a}_{b}")
            model.AddMultiplicationEquality(prod, [n[a], n[b]])
            model.Add(block_sum == prod)
            cross_products.append(prod)

    rows_eq = add_scaled_linear_constraints(model, A_eq, b_eq, n, m, point_sizes, pair_sizes, True, "eq")
    rows_ub = add_scaled_linear_constraints(model, A_ub, b_ub, n, m, point_sizes, pair_sizes, False, "ub")

    if objective == "max_omitted":
        model.Maximize(sum(n[:4]))
    elif objective == "min_omitted":
        model.Minimize(sum(n[:4]))
    elif objective == "lex_small":
        model.Minimize(sum((a + 1) * n[a] for a in range(K)) + sum(((j * 37 + seed) % 997) * m[j] for j in range(M)))
    elif objective == "none":
        pass
    else:
        raise ValueError(objective)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(solver_time)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = int(seed)
    t0 = time.time()
    status = solver.Solve(model)
    elapsed = time.time() - t0
    status_name = solver.StatusName(status)
    rec = {
        "label": label,
        "objective": objective,
        "force_zero_omitted": force_zero_omitted,
        "status": status_name,
        "solve_sec": round(elapsed, 3),
        "parameters": {"solver_time": solver_time, "workers": workers, "seed": seed},
        "scaled_rows_eq": rows_eq,
        "scaled_rows_ub": rows_ub,
        "cp_sat_objective_value": float(solver.ObjectiveValue()) if status in (cp_model.OPTIMAL, cp_model.FEASIBLE) and objective != "none" else None,
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        n_vals = [int(solver.Value(v)) for v in n]
        m_vals = [int(solver.Value(v)) for v in m]
        chk = exact_count_check(A_eq, b_eq, A_ub, b_ub, n_vals, m_vals, point_sizes, [int(x) for x in pair_sizes], K, M)
        # Verify block sums independently.
        block_checks = []
        for a in range(K):
            val = sum(m_vals[j] for j in by_block[(a, a)])
            target = n_vals[a] * (n_vals[a] - 1) // 2
            block_checks.append({"block": [a, a], "sum_m": val, "target": target, "ok": val == target})
        for a in range(K):
            for b in range(a + 1, K):
                val = sum(m_vals[j] for j in by_block[(a, b)])
                target = n_vals[a] * n_vals[b]
                block_checks.append({"block": [a, b], "sum_m": val, "target": target, "ok": val == target})
        rec.update({
            "n_by_point_orbit": n_vals,
            "omitted_n_0_3": int(sum(n_vals[:4])),
            "m_by_pair_orbit": m_vals,
            "m_total": int(sum(m_vals)),
            "nonzero_m_orbits": int(sum(1 for v in m_vals if v)),
            "exact_fraction_check": chk,
            "block_checks_all_ok": all(bc["ok"] for bc in block_checks),
            "block_checks": block_checks,
            "nonzero_m_details": [
                {"pair_orbit": j, "m": m_vals[j], "endpoint_orbits": [int(pair_ep[j][0]), int(pair_ep[j][1])], "size": int(pair_sizes[j])}
                for j in range(M) if m_vals[j]
            ],
        })
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--triangles", action="store_true")
    ap.add_argument("--solver-time", type=float, default=300.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=660666)
    args = ap.parse_args()
    t0 = time.time()
    OUT.mkdir(parents=True, exist_ok=True)

    print(f"analysis invariant pair block CP-SAT triangles={args.triangles}")
    t = time.time()
    perms = build_stabilizer()
    pt_orb, point_orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, M = compute_pair_orbits(perms, pt_orb)
    K = len(point_orbits); N = K + M
    print(f"  orbits built: K={K}, M={M}, elapsed={time.time()-t:.1f}s")
    t = time.time()
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
    print(f"  constraints built: eq={A_eq.shape[0]}, ub={A_ub.shape[0]}, elapsed={time.time()-t:.1f}s")

    jobs = [
        ("feasibility_lex", "lex_small", False),
        ("max_omitted", "max_omitted", False),
        ("min_omitted", "min_omitted", False),
        ("force_zero_omitted", "lex_small", True),
    ]
    results = []
    for i, (label, obj, zero) in enumerate(jobs):
        print(f"  solve {label}", flush=True)
        rec = solve_model(label, A_eq, b_eq, A_ub, b_ub, point_orbits, pair_sizes, pair_ep, K, M,
                          args.solver_time, args.workers, args.seed + i, obj, zero)
        print(json.dumps({"label": label, "status": rec["status"], "n": rec.get("n_by_point_orbit"), "omitted": rec.get("omitted_n_0_3"), "exact": rec.get("exact_fraction_check", {}).get("is_exact_feasible"), "block": rec.get("block_checks_all_ok"), "solve_sec": rec["solve_sec"]}, sort_keys=True), flush=True)
        results.append(rec)

    payload = {
        "schema": "invariant_pair_block_cpsat_v1",
        "triangles": bool(args.triangles),
        "meaning": "Exact integer invariant point/pair count model with block pair totals, plus orbit-averaged Wang RLT constraints; feasible is only a necessary-condition witness, not a support.",
        "scale": SCALE,
        "point_orbit_reps": [int(o[0]) for o in point_orbits],
        "point_orbit_sizes": [len(o) for o in point_orbits],
        "pair_orbit_size_histogram": {str(k): int(v) for k, v in sorted(Counter(pair_sizes).items())},
        "pair_metadata": make_pair_metadata(pair_orb, pair_sizes, pair_ep),
        "wang_record_count": len(records),
        "n_eq_constraints": int(A_eq.shape[0]),
        "n_ub_constraints": int(A_ub.shape[0]),
        "triangle_meta": tri_meta,
        "results": results,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    name = "pair_block_triangles.json" if args.triangles else "pair_block_base.json"
    path = OUT / name
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(path), "triangles": args.triangles, "statuses": [(r["label"], r["status"], r.get("n_by_point_orbit"), r.get("omitted_n_0_3"), r.get("exact_fraction_check", {}).get("is_exact_feasible")) for r in results], "elapsed_sec": payload["elapsed_sec"]}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
