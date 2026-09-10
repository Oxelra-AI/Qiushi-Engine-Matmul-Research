#!/usr/bin/env python3
"""analysis: direct global SDP feasibility test for orbit-averaged Wang RLT + PSD.

This tests the continuous question restored by the analysis review note:
can the labelled moment matrix PSD condition coexist with the complete E11
Wang RLT constraints (and optional triangle/Fortet inequalities), with the six
first moments free?

The script uses the raw integer analysis RLT rows.  It does not infer an exact
mathematical theorem from numerical solver status.  A feasible SDP moment is not
a 19-point support; an infeasible numerical status would need exact certificate
work before entering the lower-bound chain.

To avoid the known cardinality kernel u=(-19,1,...,1), the PSD cone is imposed on
a 255-dimensional basis of u^perp.  The linear equalities should enforce M u=0;
the output checks this on any returned solution.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import cvxpy as cp
import numpy as np
from scipy import sparse

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
from rlt_triangle_integrality import dense_rows_to_csr, build_triangle_constraints  # noqa: E402
from global_psd_cut_loop import make_pair_var_matrix, build_moment_matrix, moment_kernel_residual  # noqa: E402

OUT = ROOT / "workspace/data/global_sdp"


def build_coefficient_matrices(orbits, pair_orb, K, Mpair):
    """Dense coefficient matrices for M = C0 + sum_i z_i C_i."""
    C0 = np.zeros((256, 256), dtype=float)
    C0[0, 0] = 1.0
    Cs = np.zeros((K + Mpair, 256, 256), dtype=float)
    for a, orb in enumerate(orbits):
        for p in orb:
            Cs[a, 0, p] = 1.0
            Cs[a, p, 0] = 1.0
            Cs[a, p, p] = 1.0
    for (p, q), j in pair_orb.items():
        Cs[K + j, p, q] = 1.0
        Cs[K + j, q, p] = 1.0
    return C0, Cs


def quotient_basis():
    """Columns form a basis for u^perp where u=(-19,1,...,1)."""
    B = np.zeros((256, 255), dtype=float)
    # e_p - e_255 for p=1..254.
    for c in range(254):
        p = c + 1
        B[p, c] = 1.0
        B[255, c] = -1.0
    # e_0 + 19 e_255.
    B[0, 254] = 1.0
    B[255, 254] = 19.0
    return B


def residual_stats(Aeq, beq, Aub, bub, z):
    eq = Aeq @ z - beq
    ub = Aub @ z - bub
    return {
        "max_abs_eq": float(np.max(np.abs(eq))) if eq.size else 0.0,
        "max_ub_violation": float(max(0.0, np.max(ub))) if ub.size else 0.0,
        "violated_ub_count_1e-7": int(np.sum(ub > 1e-7)) if ub.size else 0,
        "min_ub_slack": float(np.min(-ub)) if ub.size else None,
    }


def make_z_summary(z, orbits, pair_sizes, K, Mpair):
    y = z[K:]
    nz = []
    for j in range(Mpair):
        if y[j] > 1e-8:
            nz.append({"pair_orbit": int(j), "y": float(y[j]), "m_float": float(pair_sizes[j] * y[j])})
    nz.sort(key=lambda d: -d["m_float"])
    return {
        "x_by_point_orbit": [float(z[a]) for a in range(K)],
        "n_mass_by_point_orbit": [float(len(orbits[a]) * z[a]) for a in range(K)],
        "nonzero_pair_orbits_1e-8": len(nz),
        "top_pair_masses": nz[:40],
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--solver", choices=["CLARABEL", "SCS"], default="CLARABEL")
    ap.add_argument("--no-triangles", action="store_true")
    ap.add_argument("--max-iter", type=int, default=1000)
    ap.add_argument("--eps", type=float, default=1e-5)
    args = ap.parse_args()

    t0 = time.time()
    OUT.mkdir(parents=True, exist_ok=True)
    print("analysis: direct global RLT(+triangle)+PSD SDP feasibility", flush=True)
    print("  1. Build orbits", flush=True)
    perms = build_stabilizer()
    pt_orb, orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, Mpair = compute_pair_orbits(perms, pt_orb)
    pair_var = make_pair_var_matrix(pair_orb)
    K = len(orbits)
    N = K + Mpair
    print(f"     |G|={len(perms)}, point_sizes={[len(o) for o in orbits]}, pair_orbits={Mpair} ({time.time()-t0:.1f}s)", flush=True)

    print("  2. Load Wang and build raw RLT", flush=True)
    lut, _ = load_lut(LUT_PATH)
    records, wmeta = build_core_constraints(CoreQuotient(1), lut)
    eq_A, eq_b, ub_A, ub_b, K2, M2, N2, n_aj = build_lp(records, pt_orb, orbits, pair_orb, Mpair, pair_ep)
    assert (K2, M2, N2) == (K, Mpair, N)
    Aeq = dense_rows_to_csr(eq_A, N)
    beq = np.array(eq_b, dtype=float)
    Aub = dense_rows_to_csr(ub_A, N)
    bub = np.array(ub_b, dtype=float)
    base_ub = Aub.shape[0]
    tri_meta = None
    if not args.no_triangles:
        print("  3. Add triangle rows", flush=True)
        Atri, btri, tri_meta = build_triangle_constraints(pt_orb, pair_orb, K, Mpair)
        Aub = sparse.vstack([Aub, Atri], format="csr")
        bub = np.concatenate([bub, btri])
    print(f"     linear constraints: {Aeq.shape[0]} eq, {Aub.shape[0]} ub ({time.time()-t0:.1f}s)", flush=True)

    print("  4. Build quotient PSD coefficient matrices", flush=True)
    C0, Cs = build_coefficient_matrices(orbits, pair_orb, K, Mpair)
    B = quotient_basis()
    C0q = B.T @ C0 @ B
    Csq = np.empty((N, 255, 255), dtype=float)
    for i in range(N):
        Csq[i] = B.T @ Cs[i] @ B
    print(f"     PSD matrices ready ({time.time()-t0:.1f}s)", flush=True)

    z = cp.Variable(N)
    t = cp.Variable()
    P = cp.Constant(C0q)
    # Loop avoids high-dimensional CVXPY expressions and compiles reliably.
    for i in range(N):
        P = P + z[i] * Csq[i]
    constraints = [Aeq @ z == beq, Aub @ z <= bub, z >= 0, z <= 1, P - t * np.eye(255) >> 0]
    objective = cp.Maximize(t)
    prob = cp.Problem(objective, constraints)
    print(f"  5. Solve with {args.solver}", flush=True)
    solve_kwargs = {"verbose": True}
    if args.solver == "CLARABEL":
        solve_kwargs.update({"max_iter": args.max_iter})
    else:
        solve_kwargs.update({"max_iters": args.max_iter, "eps": args.eps})
    try:
        value = prob.solve(solver=args.solver, **solve_kwargs)
        solve_error = None
    except Exception as e:
        value = None
        solve_error = repr(e)
        print("SOLVE_ERROR", solve_error, flush=True)

    rec = {
        "schema": "global_sdp_feasibility_v1",
        "meaning": "Numerical direct conic test of continuous orbit-averaged complete-Wang RLT plus labelled moment PSD, with free first moments. Numerical feasibility is not a support; numerical infeasibility requires exact certificate work.",
        "elapsed_sec": round(time.time() - t0, 3),
        "solver": args.solver,
        "solver_status": prob.status,
        "solver_value_max_min_eigen_lb": None if value is None else float(value),
        "solve_error": solve_error,
        "point_orbit_sizes": [len(o) for o in orbits],
        "n_pair_orbits": Mpair,
        "n_variables": N,
        "n_eq_constraints": int(Aeq.shape[0]),
        "n_ub_constraints_base_rlt": int(base_ub),
        "triangle_meta": tri_meta,
        "n_ub_constraints_total": int(Aub.shape[0]),
    }
    if z.value is not None:
        zv = np.array(z.value, dtype=float).reshape(-1)
        Mmat = build_moment_matrix(zv, pt_orb, pair_var, K)
        eig = np.linalg.eigvalsh(Mmat)
        Pnum = C0q.copy()
        for i in range(N):
            Pnum += zv[i] * Csq[i]
        peig = np.linalg.eigvalsh(Pnum)
        rec.update({
            "linear_residuals": residual_stats(Aeq, beq, Aub, bub, zv),
            "labelled_M_min_eigenvalue": float(eig[0]),
            "labelled_M_negative_count_1e-7": int(np.sum(eig < -1e-7)),
            "quotient_P_min_eigenvalue": float(peig[0]),
            "quotient_P_negative_count_1e-7": int(np.sum(peig < -1e-7)),
            "kernel_residual": moment_kernel_residual(Mmat),
            "z_summary": make_z_summary(zv, orbits, pair_sizes, K, Mpair),
        })
        np.save(OUT / f"solution_{args.solver.lower()}.npy", zv)
    out = OUT / f"global_sdp_{args.solver.lower()}_{'notri' if args.no_triangles else 'tri'}.json"
    out.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    print("Saved", out, flush=True)
    print(json.dumps({
        "status": rec["solver_status"],
        "value": rec["solver_value_max_min_eigen_lb"],
        "labelled_min_eig": rec.get("labelled_M_min_eigenvalue"),
        "linear_max_ub_violation": rec.get("linear_residuals", {}).get("max_ub_violation"),
        "out": str(out),
    }, indent=2), flush=True)


if __name__ == "__main__":
    main()
