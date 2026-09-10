#!/usr/bin/env python3
"""analysis: Test integer count vectors near the continuous block-SDP optimum.

After the block SDP showed continuous Wang+RLT+tri+PSD feasibility,
test whether specific integer count vectors (n_0,...,n_5) with sum 19
also admit PSD-feasible pair distributions.
"""
import json, time, sys
import numpy as np
from pathlib import Path
from scipy import sparse
from scipy.linalg import eigh
from itertools import product as iprod

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from rlt_pair_lift import (
    build_stabilizer, compute_point_orbits, compute_pair_orbits,
    build_lp, LUT_PATH,
)
from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints
from rlt_triangle_integrality import (
    build_triangle_constraints, dense_rows_to_csr,
)
from block_sdp_v2 import (
    build_orbit_coeff_matrices, form_group_algebra_element, cluster_eigenvalues,
)

OUT = ROOT / "workspace/data/block_sdp"


def generate_nearby_count_vectors(target_mass, sizes, total=19, max_vectors=50):
    """Generate integer count vectors sorted by L1 distance to target."""
    K = len(sizes)
    bounds = [min(s, total) for s in sizes]
    candidates = []
    # Generate all compositions of `total` into K parts with bounds
    def recurse(depth, remaining, partial):
        if depth == K:
            if remaining == 0:
                candidates.append(list(partial))
            return
        for n in range(min(bounds[depth], remaining) + 1):
            partial.append(n)
            recurse(depth + 1, remaining - n, partial)
            partial.pop()
    recurse(0, total, [])
    # Sort by L1 distance to target
    candidates.sort(key=lambda c: sum(abs(c[a] - target_mass[a]) for a in range(K)))
    return candidates[:max_vectors]


def main():
    t0 = time.time()
    print("analysis: Integer count-vector PSD feasibility test", flush=True)

    # 1. Build infrastructure
    print("  1. Building infrastructure...", flush=True)
    perms = build_stabilizer()
    pt_orb, orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, Mpair = compute_pair_orbits(perms, pt_orb)
    K = len(orbits); N = K + Mpair; sizes = [len(o) for o in orbits]
    print(f"     |G|={len(perms)}, K={K}, Mpair={Mpair} ({time.time()-t0:.1f}s)")

    C0, C_pt, C_pr = build_orbit_coeff_matrices(orbits, pair_orb, K, Mpair)
    H = form_group_algebra_element(perms, seed=69)
    vals, vecs = eigh(H)
    clusters = cluster_eigenvalues(vals, tol=1e-6)

    # Precompute block projections
    blocks = []
    for cval, indices in clusters:
        m = len(indices)
        U = vecs[:, indices].copy()
        B0 = (U.T @ (C0 @ U) + (U.T @ (C0 @ U)).T) / 2
        Bp = [(U.T @ (C_pt[a] @ U) + (U.T @ (C_pt[a] @ U)).T) / 2 for a in range(K)]
        Bj = [(U.T @ (C_pr[j] @ U) + (U.T @ (C_pr[j] @ U)).T) / 2 for j in range(Mpair)]
        blocks.append({"m": m, "B0": B0, "Bp": Bp, "Bj": Bj})

    # 2. Build linear constraints
    print("  2. Building linear constraints...", flush=True)
    lut, _ = load_lut(LUT_PATH)
    records, wmeta = build_core_constraints(CoreQuotient(1), lut)
    eq_A, eq_b, ub_A, ub_b, K2, M2, N2, n_aj = build_lp(
        records, pt_orb, orbits, pair_orb, Mpair, pair_ep)
    Aeq = dense_rows_to_csr(eq_A, N); beq = np.array(eq_b, dtype=float)
    Aub = dense_rows_to_csr(ub_A, N); bub = np.array(ub_b, dtype=float)
    Atri, btri, tri_meta = build_triangle_constraints(pt_orb, pair_orb, K, Mpair)
    Aub_all = sparse.vstack([Aub, Atri], format="csr")
    bub_all = np.concatenate([bub, btri])
    print(f"     {Aub_all.shape[0]} ub constraints ({time.time()-t0:.1f}s)")

    # 3. Generate candidate count vectors
    continuous_mass = [0.672, 0.712, 2.958, 5.029, 2.754, 6.875]
    candidates = generate_nearby_count_vectors(continuous_mass, sizes, total=19, max_vectors=30)
    print(f"  3. Testing {len(candidates)} count vectors near continuous optimum...",
          flush=True)

    # 4. Test each with block SDP
    import cvxpy as cp

    results = []
    for ci, n_vec in enumerate(candidates):
        x_fixed = [n_vec[a] / sizes[a] for a in range(K)]

        # Build sub-SDP: only pair variables are free
        y_var = cp.Variable(Mpair, name="y")
        z = np.zeros(N)
        z[:K] = x_fixed

        # Substitute x into linear constraints
        # Aeq @ [x; y] = beq => Aeq_y @ y = beq - Aeq_x @ x
        Aeq_x = Aeq[:, :K]; Aeq_y = Aeq[:, K:]
        beq_sub = beq - Aeq_x @ np.array(x_fixed)

        Aub_x = Aub_all[:, :K]; Aub_y = Aub_all[:, K:]
        bub_sub = bub_all - Aub_x @ np.array(x_fixed)

        constraints = [
            Aeq_y @ y_var == beq_sub,
            Aub_y @ y_var <= bub_sub,
            y_var >= 0, y_var <= 1,
        ]

        # PSD blocks
        for b in blocks:
            m = b["m"]
            # Fixed part: B0 + Σ x_a Bp[a]
            B_fixed = b["B0"].copy()
            for a in range(K):
                B_fixed += x_fixed[a] * b["Bp"][a]
            if m == 1:
                coeff = np.zeros(Mpair)
                for j in range(Mpair):
                    coeff[j] = float(b["Bj"][j])
                constraints.append(coeff @ y_var >= -float(B_fixed))
            else:
                B_expr = cp.Constant(np.asarray(B_fixed, dtype=float))
                for j in range(Mpair):
                    if np.any(np.abs(b["Bj"][j]) > 1e-15):
                        B_expr = B_expr + y_var[j] * np.asarray(b["Bj"][j], dtype=float)
                constraints.append(B_expr >> 0)

        prob = cp.Problem(cp.Minimize(0), constraints)
        try:
            prob.solve(solver=cp.CLARABEL, verbose=False, max_iter=300,
                       tol_gap_abs=1e-7, tol_gap_rel=1e-7)
            status = prob.status
        except Exception as e:
            status = f"error: {e}"

        feasible = "optimal" in str(status)
        rec = {"n": n_vec, "status": str(status), "feasible": feasible,
               "l1_dist": sum(abs(n_vec[a] - continuous_mass[a]) for a in range(K))}

        if feasible and y_var.value is not None:
            yval = np.array(y_var.value).flatten()
            zfull = np.zeros(N)
            zfull[:K] = x_fixed
            zfull[K:] = yval
            # Quick PSD check
            from block_sdp_v2 import build_full_moment_matrix
            Mfull = build_full_moment_matrix(zfull, pt_orb, pair_orb, K)
            eigvals = np.linalg.eigvalsh(Mfull)
            rec["psd_min_eig"] = float(eigvals[0])
            rec["psd_neg_count"] = int(np.sum(eigvals < -1e-8))

        results.append(rec)
        tag = "✓" if feasible else "✗"
        eig_str = f", min_eig={rec.get('psd_min_eig', 'N/A')}" if feasible else ""
        print(f"     [{ci+1:2d}] n={n_vec} {tag} {status}{eig_str}", flush=True)

    n_feas = sum(1 for r in results if r["feasible"])
    print(f"\n  Summary: {n_feas}/{len(results)} feasible", flush=True)

    summary = {
        "schema": "integer_count_psd_v1",
        "meaning": ("For each integer count vector, test whether the remaining "
                     "pair-variable SDP (Wang RLT + triangle + block PSD) is "
                     "feasible. Feasible = orbit-averaged moment exists, not a support."),
        "continuous_optimal_mass": continuous_mass,
        "n_tested": len(results),
        "n_feasible": n_feas,
        "results": results,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    (OUT / "integer_count_psd_results.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(f"  Saved: {OUT / 'integer_count_psd_results.json'}", flush=True)


if __name__ == "__main__":
    main()
