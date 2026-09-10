#!/usr/bin/env python3
"""analysis v2: Block SDP via group-algebra eigenspace decomposition.

The 256×256 moment matrix M is G-invariant and commutes with every
group-algebra element H = Σ c_g P_g.  The eigenspaces of H give an
orthogonal decomposition of C^256 that is M-invariant.  Therefore:

    M ≽ 0  ⟺  U_k^T M U_k ≽ 0  for each eigenspace k.

With the E11 stabilizer (|G|=1152), H has 93 distinct eigenvalues with
multiplicities up to 7.  This replaces one 256×256 PSD cone (32896
scalar params) with 93 small PSD cones (594 total scalar params).
"""
from __future__ import annotations

import json
import time
import sys
from pathlib import Path
from collections import Counter

import numpy as np
from scipy import sparse
from scipy.linalg import eigh

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

OUT = ROOT / "workspace/data/block_sdp"


def build_orbit_coeff_matrices(orbits, pair_orb, K, Mpair):
    n = 256
    C0 = sparse.csr_matrix(([1.0], ([0], [0])), shape=(n, n))
    C_pt = []
    for a in range(K):
        rs, cs, vs = [], [], []
        for p in orbits[a]:
            rs.extend([0, p, p]); cs.extend([p, 0, p]); vs.extend([1., 1., 1.])
        C_pt.append(sparse.csr_matrix((vs, (rs, cs)), shape=(n, n)))
    pbyo = [[] for _ in range(Mpair)]
    for (p, q), j in pair_orb.items():
        pbyo[j].append((p, q))
    C_pr = []
    for j in range(Mpair):
        rs, cs, vs = [], [], []
        for (p, q) in pbyo[j]:
            rs.extend([p, q]); cs.extend([q, p]); vs.extend([1., 1.])
        C_pr.append(sparse.csr_matrix((vs, (rs, cs)), shape=(n, n)))
    return C0, C_pt, C_pr


def form_group_algebra_element(perms, seed=69):
    rng = np.random.default_rng(seed)
    H = np.zeros((256, 256), dtype=np.float64)
    for perm in perms:
        r = rng.standard_normal()
        for j in range(256):
            H[int(perm[j]), j] += r
    return (H + H.T) / 2.0


def cluster_eigenvalues(vals, tol=1e-6):
    clusters = []
    i = 0
    n = len(vals)
    while i < n:
        j = i + 1
        while j < n and abs(vals[j] - vals[i]) < tol * (1.0 + abs(vals[i])):
            j += 1
        clusters.append((float(np.mean(vals[i:j])), list(range(i, j))))
        i = j
    return clusters


def build_full_moment_matrix(z, pt_orb, pair_orb_dict, K):
    M = np.zeros((256, 256), dtype=float)
    M[0, 0] = 1.0
    for p in range(1, 256):
        xp = z[pt_orb[p]]
        M[0, p] = M[p, 0] = xp
        M[p, p] = xp
    for (p, q), j in pair_orb_dict.items():
        yj = z[K + j]
        M[p, q] = M[q, p] = yj
    return M


def main():
    t0 = time.time()
    OUT.mkdir(parents=True, exist_ok=True)

    print("analysis v2: Block SDP via group-algebra eigenspaces", flush=True)

    # ── 1. Stabiliser and orbits ─────────────────────────────────────────
    print("  1. Building stabiliser...", flush=True)
    perms = build_stabilizer()
    pt_orb, orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, Mpair = compute_pair_orbits(perms, pt_orb)
    K = len(orbits); N = K + Mpair
    sizes = [len(o) for o in orbits]
    print(f"     |G|={len(perms)}, K={K}, Mpair={Mpair}, N={N}, sizes={sizes} "
          f"({time.time()-t0:.1f}s)", flush=True)

    # ── 2. Orbit coefficient matrices ────────────────────────────────────
    print("  2. Building orbit coefficient matrices...", flush=True)
    C0, C_pt, C_pr = build_orbit_coeff_matrices(orbits, pair_orb, K, Mpair)

    # ── 3. Group-algebra element and eigendecomposition ──────────────────
    print("  3. Forming H and eigendecomposing...", flush=True)
    H = form_group_algebra_element(perms, seed=69)
    # Verify commutativity with G-invariant test matrix
    M_test = np.zeros((256, 256), dtype=float)
    for perm in perms:
        for j in range(256):
            M_test[int(perm[j]), j] += 1.0
    M_test /= len(perms)
    comm = np.max(np.abs(M_test @ H - H @ M_test))
    print(f"     |[M_test, H]| = {comm:.2e}", flush=True)
    assert comm < 1e-8

    vals, vecs = eigh(H)
    clusters = cluster_eigenvalues(vals, tol=1e-6)
    mult_sizes = [len(idx) for _, idx in clusters]
    mult_hist = dict(Counter(mult_sizes))
    total_psd_params = sum(m * (m + 1) // 2 for m in mult_sizes)

    print(f"     {len(clusters)} eigenspaces, mult histogram: "
          f"{dict(sorted(mult_hist.items()))}", flush=True)
    print(f"     total PSD params: {total_psd_params} "
          f"(vs 256×257/2 = {256*257//2})", flush=True)

    # ── 4. Project orbit matrices onto each eigenspace ───────────────────
    print("  4. Computing block projections...", flush=True)
    blocks = []
    for cval, indices in clusters:
        m = len(indices)
        U = vecs[:, indices].copy()
        B0 = U.T @ (C0 @ U); B0 = (B0 + B0.T) / 2
        Bp = []
        for a in range(K):
            B = U.T @ (C_pt[a] @ U); B = (B + B.T) / 2; Bp.append(B)
        Bj = []
        for j in range(Mpair):
            B = U.T @ (C_pr[j] @ U); B = (B + B.T) / 2; Bj.append(B)
        blocks.append({"m": m, "eigenvalue": cval, "B0": B0, "Bp": Bp, "Bj": Bj})
    print(f"     projected {len(blocks)} blocks ({time.time()-t0:.1f}s)", flush=True)

    # ── 5. Validate on analysis witnesses ─────────────────────────────────
    print("  5. Validating block decomposition...", flush=True)
    wb_path = ROOT / "workspace/data/invariant_pair_block/pair_block_triangles.json"
    validations = []
    if wb_path.exists():
        wb = json.loads(wb_path.read_text())
        for rec in wb.get("results", []):
            n_vec = rec["n_by_point_orbit"]; m_vec = rec["m_by_pair_orbit"]
            z = np.zeros(N, dtype=float)
            for a in range(K): z[a] = n_vec[a] / sizes[a]
            for j in range(Mpair): z[K + j] = m_vec[j] / pair_sizes[j]
            Mfull = build_full_moment_matrix(z, pt_orb, pair_orb, K)
            full_eigs = np.linalg.eigvalsh(Mfull)
            full_min = float(full_eigs[0])
            # Block check
            block_min = float('inf')
            for b in blocks:
                Bb = b["B0"].copy()
                for a in range(K): Bb += z[a] * b["Bp"][a]
                for j in range(Mpair): Bb += z[K + j] * b["Bj"][j]
                if b["m"] == 1:
                    block_min = min(block_min, float(Bb))
                else:
                    beigs = np.linalg.eigvalsh(Bb)
                    block_min = min(block_min, float(beigs[0]))
            ok = abs(block_min - full_min) < 1e-5
            validations.append({"label": rec["label"], "full": full_min,
                                "block": block_min, "match": ok})
            print(f"     {rec['label']}: full={full_min:.6f}, "
                  f"block={block_min:.6f}, match={ok}", flush=True)

    # ── 6. Build Wang RLT + triangle constraints ─────────────────────────
    print("  6. Building linear constraints...", flush=True)
    lut, _ = load_lut(LUT_PATH)
    records, wmeta = build_core_constraints(CoreQuotient(1), lut)
    eq_A, eq_b, ub_A, ub_b, K2, M2, N2, n_aj = build_lp(
        records, pt_orb, orbits, pair_orb, Mpair, pair_ep)
    Aeq = dense_rows_to_csr(eq_A, N); beq = np.array(eq_b, dtype=float)
    Aub = dense_rows_to_csr(ub_A, N); bub = np.array(ub_b, dtype=float)
    n_rlt = Aub.shape[0]
    Atri, btri, tri_meta = build_triangle_constraints(pt_orb, pair_orb, K, Mpair)
    Aub_all = sparse.vstack([Aub, Atri], format="csr")
    bub_all = np.concatenate([bub, btri])
    print(f"     {Aeq.shape[0]} eq, {Aub_all.shape[0]} ub "
          f"(RLT={n_rlt}, tri={tri_meta['unique_triangle_inequalities']}) "
          f"({time.time()-t0:.1f}s)", flush=True)

    # ── 7. Formulate and solve block SDP ─────────────────────────────────
    print("  7. Formulating block SDP...", flush=True)
    import cvxpy as cp

    z_var = cp.Variable(N, name="z")
    constraints = [
        Aeq @ z_var == beq,
        Aub_all @ z_var <= bub_all,
        z_var >= 0, z_var <= 1,
    ]

    n_scalar_c = 0; n_matrix_c = 0; largest_m = 0
    for b in blocks:
        m = b["m"]
        if m == 1:
            coeff = np.zeros(N)
            for a in range(K): coeff[a] = float(b["Bp"][a])
            for j in range(Mpair): coeff[K + j] = float(b["Bj"][j])
            constraints.append(coeff @ z_var >= -float(b["B0"]))
            n_scalar_c += 1
        else:
            # Only include nonzero coefficient matrices
            B_expr = cp.Constant(np.asarray(b["B0"], dtype=float))
            for a in range(K):
                if np.any(np.abs(b["Bp"][a]) > 1e-15):
                    B_expr = B_expr + z_var[a] * np.asarray(b["Bp"][a], dtype=float)
            for j in range(Mpair):
                if np.any(np.abs(b["Bj"][j]) > 1e-15):
                    B_expr = B_expr + z_var[K + j] * np.asarray(b["Bj"][j], dtype=float)
            constraints.append(B_expr >> 0)
            n_matrix_c += 1
            largest_m = max(largest_m, m)

    print(f"     {n_scalar_c} scalar + {n_matrix_c} matrix PSD "
          f"(largest m={largest_m}) ({time.time()-t0:.1f}s)", flush=True)

    print("  8. Solving with CLARABEL...", flush=True)
    prob = cp.Problem(cp.Minimize(0), constraints)
    solve_t0 = time.time()
    try:
        prob.solve(solver=cp.CLARABEL, verbose=True, max_iter=500,
                   tol_gap_abs=1e-8, tol_gap_rel=1e-8)
        prob_status = prob.status
    except Exception as e:
        prob_status = f"exception: {e}"
    solve_sec = time.time() - solve_t0

    print(f"     status: {prob_status}, solve: {solve_sec:.1f}s "
          f"({time.time()-t0:.1f}s total)", flush=True)

    # ── 8. Verify solution ───────────────────────────────────────────────
    feasible_point = None; full_verify = None
    if z_var.value is not None:
        zval = np.array(z_var.value).flatten()
        Mfull = build_full_moment_matrix(zval, pt_orb, pair_orb, K)
        full_eigs = np.linalg.eigvalsh(Mfull)
        eq_res = float(np.max(np.abs(Aeq @ zval - beq)))
        ub_res = float(np.max(Aub_all @ zval - bub_all))
        feasible_point = {
            "x_by_orbit": [float(zval[a]) for a in range(K)],
            "n_mass": [float(sizes[a] * zval[a]) for a in range(K)],
            "total_mass": float(sum(sizes[a] * zval[a] for a in range(K))),
            "nonzero_pairs": int(np.sum(np.abs(zval[K:]) > 1e-10)),
        }
        full_verify = {
            "full_256_min_eig": float(full_eigs[0]),
            "full_256_neg_1e8": int(np.sum(full_eigs < -1e-8)),
            "eq_resid": eq_res, "ub_viol": ub_res,
        }
        print(f"     full 256×256: min eig={full_eigs[0]:.10f}, "
              f"neg={full_verify['full_256_neg_1e8']}", flush=True)
        print(f"     lin: eq={eq_res:.2e}, ub={ub_res:.2e}", flush=True)
        print(f"     mass: {feasible_point['n_mass']}", flush=True)
        np.save(OUT / "feasible_z.npy", zval)

    # ── 9. Save ──────────────────────────────────────────────────────────
    result = {
        "schema": "block_sdp_v2",
        "meaning": ("Block-decomposed SDP for E11 moment matrix. "
                     "Feasible = continuous moment point exists "
                     "(not a support). Infeasible = PSD+RLT globally excluded."),
        "elapsed_sec": round(time.time() - t0, 3),
        "block_decomposition": {
            "n_eigenspaces": len(clusters),
            "multiplicity_histogram": mult_hist,
            "total_psd_params": total_psd_params,
            "n_scalar_psd": n_scalar_c,
            "n_matrix_psd": n_matrix_c,
            "largest_block": largest_m,
        },
        "linear_model": {
            "n_eq": int(Aeq.shape[0]),
            "n_ub_rlt": n_rlt,
            "n_ub_tri": tri_meta["unique_triangle_inequalities"],
            "n_ub_total": int(Aub_all.shape[0]),
        },
        "sdp_status": str(prob_status),
        "sdp_solve_sec": round(solve_sec, 3),
        "feasible_point": feasible_point,
        "full_verification": full_verify,
        "block_witness_validation": validations,
    }
    (OUT / "block_sdp_result.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"\n  Result: {OUT / 'block_sdp_result.json'}", flush=True)
    # Summary
    print(json.dumps({
        "status": str(prob_status),
        "n_eigenspaces": len(clusters),
        "largest_block": largest_m,
        "solve_sec": round(solve_sec, 3),
        "feasible_min_eig": full_verify["full_256_min_eig"] if full_verify else None,
    }, indent=2), flush=True)


if __name__ == "__main__":
    main()
