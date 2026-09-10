#!/usr/bin/env python3
"""analysis: Block-decompose the E11 moment matrix using group-algebra eigenspaces.

The 256×256 orbit-averaged moment matrix M is G-invariant under the 1152-element
E11 stabilizer.  Every G-invariant M commutes with every group-algebra element
H = Σ_g c_g P_g, so eigenspaces of a generic H are M-invariant.  This gives
a block decomposition: M ≽ 0 iff each block B_λ ≽ 0.

For the isotypic decomposition V = ⊕_λ (W_λ ⊗ V_λ), the blocks B_λ are
m_λ × m_λ symmetric matrices.  The number of PSD scalar parameters is
Σ m_λ(m_λ+1)/2 = dim(symmetric commutant) = 110,
far smaller than 256·257/2 = 32896.

Combined with Wang RLT + triangle constraints, this gives a tractable SDP.
"""
from __future__ import annotations

import json
import time
import sys
import hashlib
from pathlib import Path
from collections import Counter

import numpy as np
from scipy import sparse
from scipy.linalg import eigh
from scipy.optimize import linprog

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from rlt_pair_lift import (
    build_stabilizer,
    compute_point_orbits,
    compute_pair_orbits,
    build_lp,
    LUT_PATH,
)
from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints
from rlt_triangle_integrality import (
    build_triangle_constraints,
    dense_rows_to_csr,
)

OUT = ROOT / "workspace/data/block_sdp"


# ── Orbit coefficient matrices (sparse 256×256) ──────────────────────────

def build_orbit_coeff_matrices(orbits, pair_orb, K, Mpair):
    """Build coefficient matrices for M(x,y) = C0 + Σ_a x_a Ca + Σ_j y_j Cj.

    C0 = e_0 e_0^T  (the constant 1 at position (0,0))
    Ca = Σ_{p∈O_a} (e_p e_0^T + e_0 e_p^T + e_p e_p^T)  (point orbit a)
    Cj = Σ_{{p,q}∈P_j} (e_p e_q^T + e_q e_p^T)           (pair orbit j)
    """
    n = 256
    C0 = sparse.csr_matrix(([1.0], ([0], [0])), shape=(n, n))

    C_pt = []
    for a in range(K):
        rs, cs, vs = [], [], []
        for p in orbits[a]:
            rs.extend([0, p, p])
            cs.extend([p, 0, p])
            vs.extend([1.0, 1.0, 1.0])
        C_pt.append(sparse.csr_matrix((vs, (rs, cs)), shape=(n, n)))

    # organise pairs by orbit
    pairs_by_orbit = [[] for _ in range(Mpair)]
    for (p, q), j in pair_orb.items():
        pairs_by_orbit[j].append((p, q))

    C_pr = []
    for j in range(Mpair):
        rs, cs, vs = [], [], []
        for (p, q) in pairs_by_orbit[j]:
            rs.extend([p, q])
            cs.extend([q, p])
            vs.extend([1.0, 1.0])
        C_pr.append(sparse.csr_matrix((vs, (rs, cs)), shape=(n, n)))

    return C0, C_pt, C_pr


# ── Group-algebra element ────────────────────────────────────────────────

def form_group_algebra_element(perms, n=256, seed=69):
    """H = Σ_g r_g P_g, symmetrised.  H commutes with every G-invariant M."""
    rng = np.random.default_rng(seed)
    H = np.zeros((n, n), dtype=np.float64)
    for perm in perms:
        r = rng.standard_normal()
        for j in range(n):
            H[int(perm[j]), j] += r
    return (H + H.T) / 2.0


# ── Eigenvalue clustering ────────────────────────────────────────────────

def cluster_eigenvalues(vals, tol=1e-6):
    """Return list of (mean_eigenvalue, [sorted_indices])."""
    n = len(vals)
    clusters = []
    i = 0
    while i < n:
        j = i + 1
        while j < n and abs(vals[j] - vals[i]) < tol * (1.0 + abs(vals[i])):
            j += 1
        # refine cluster: check internal gaps
        cluster_mean = float(np.mean(vals[i:j]))
        clusters.append((cluster_mean, list(range(i, j))))
        i = j
    return clusters


# ── Block projection ─────────────────────────────────────────────────────

def project_to_block(U, C0, C_pt, C_pr, K, Mpair):
    """Project orbit coefficient matrices onto a single eigenspace.

    U: (256, m) orthonormal eigenvector matrix for this block.
    Returns B0, B_pt[a], B_pr[j], each m×m symmetric numpy arrays.
    """
    B0 = U.T @ (C0 @ U)
    B_pt = [U.T @ (C_pt[a] @ U) for a in range(K)]
    B_pr = [U.T @ (C_pr[j] @ U) for j in range(Mpair)]
    return B0, B_pt, B_pr


def identify_unique_blocks(clusters, vecs, C0, C_pt, C_pr, K, Mpair, tol=1e-6):
    """Group eigenspaces into isotypic components.

    Two eigenspaces with the same dimension m whose projected coefficient
    matrices agree (up to tol) belong to the same isotypic component.
    Only one PSD block per component is needed.
    """
    eigenspace_projections = []
    for cval, indices in clusters:
        m = len(indices)
        U = vecs[:, indices].copy()
        B0, Bp, Bj = project_to_block(U, C0, C_pt, C_pr, K, Mpair)
        # Symmetrise numerically
        B0 = (B0 + B0.T) / 2
        for a in range(K):
            Bp[a] = (Bp[a] + Bp[a].T) / 2
        for j in range(Mpair):
            Bj[j] = (Bj[j] + Bj[j].T) / 2
        eigenspace_projections.append({
            "eigenvalue": cval,
            "m": m,
            "indices": indices,
            "B0": B0,
            "Bp": Bp,
            "Bj": Bj,
        })

    # Group by block size, then identify isotypic components
    by_size = {}
    for es in eigenspace_projections:
        by_size.setdefault(es["m"], []).append(es)

    unique_blocks = []
    for m, group in sorted(by_size.items()):
        remaining = list(group)
        while remaining:
            rep = remaining[0]
            component = [rep]
            leftovers = []
            for es in remaining[1:]:
                match = True
                # Compare a few coefficient matrices
                if np.max(np.abs(es["B0"] - rep["B0"])) > tol:
                    match = False
                if match:
                    for a in range(K):
                        if np.max(np.abs(es["Bp"][a] - rep["Bp"][a])) > tol:
                            match = False
                            break
                if match:
                    for j in range(min(20, Mpair)):
                        if np.max(np.abs(es["Bj"][j] - rep["Bj"][j])) > tol:
                            match = False
                            break
                if match:
                    component.append(es)
                else:
                    leftovers.append(es)
            remaining = leftovers
            d = len(component)
            unique_blocks.append({
                "m": m,
                "d": d,
                "total_dim": m * d,
                "eigenvalues": [es["eigenvalue"] for es in component],
                "B0": rep["B0"],
                "Bp": rep["Bp"],
                "Bj": rep["Bj"],
                "U": vecs[:, rep["indices"]].copy(),
            })

    return unique_blocks


# ── Build full 256×256 moment matrix from orbit variables ────────────────

def build_full_moment_matrix(z, pt_orb, pair_orb_dict, K, Mpair):
    """Reconstruct the full 256×256 matrix from orbit variables z."""
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


# ── Main ─────────────────────────────────────────────────────────────────

def main():
    t0 = time.time()
    OUT.mkdir(parents=True, exist_ok=True)

    print("analysis: Block decomposition of E11 moment matrix", flush=True)

    # ── 1. Stabiliser ────────────────────────────────────────────────────
    print("  1. Building stabiliser...", flush=True)
    perms = build_stabilizer()
    pt_orb, orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, Mpair = compute_pair_orbits(perms, pt_orb)
    K = len(orbits)
    N = K + Mpair
    sizes = [len(o) for o in orbits]
    print(f"     |G|={len(perms)}, K={K}, Mpair={Mpair}, N={N}, "
          f"sizes={sizes} ({time.time()-t0:.1f}s)", flush=True)

    # ── 2. Orbit coefficient matrices ────────────────────────────────────
    print("  2. Building sparse orbit coefficient matrices...", flush=True)
    C0, C_pt, C_pr = build_orbit_coeff_matrices(orbits, pair_orb, K, Mpair)
    print(f"     C0 nnz={C0.nnz}, C_pt nnz={[c.nnz for c in C_pt]}, "
          f"C_pr total nnz={sum(c.nnz for c in C_pr)} ({time.time()-t0:.1f}s)", flush=True)

    # ── 3. Group-algebra element ─────────────────────────────────────────
    print("  3. Forming group-algebra element H...", flush=True)
    H = form_group_algebra_element(perms, n=256, seed=69)
    # H is NOT G-invariant; it's a group-algebra element.
    # The key property: every G-invariant M commutes with H,
    # because M commutes with each P_g and H = Σ r_g P_g.
    # Verify commutativity with a simple G-invariant test matrix.
    M_test = np.zeros((256, 256), dtype=float)
    for perm in perms:
        for j in range(256):
            M_test[int(perm[j]), j] += 1.0  # M_test = Σ_g P_g
    M_test /= len(perms)
    comm = np.max(np.abs(M_test @ H - H @ M_test))
    assert comm < 1e-8, f"Commutativity fail: [M_test, H] = {comm}"
    print(f"     H commutativity verified: |[M_test, H]| = {comm:.2e} ({time.time()-t0:.1f}s)",
          flush=True)

    # ── 4. Eigendecompose ────────────────────────────────────────────────
    print("  4. Eigendecomposing H (256×256)...", flush=True)
    vals, vecs = eigh(H)
    print(f"     eigenvalue range [{vals[0]:.6f}, {vals[-1]:.6f}] ({time.time()-t0:.1f}s)",
          flush=True)

    # ── 5. Cluster eigenvalues ───────────────────────────────────────────
    print("  5. Clustering eigenvalues...", flush=True)
    clusters = cluster_eigenvalues(vals, tol=1e-6)
    mult_sizes = [len(idx) for _, idx in clusters]
    mult_hist = dict(Counter(mult_sizes))
    total_eigenspaces = len(clusters)
    total_psd_raw = sum(m * (m + 1) // 2 for m in mult_sizes)

    print(f"     {total_eigenspaces} distinct eigenvalues", flush=True)
    print(f"     multiplicity histogram: {dict(sorted(mult_hist.items()))}", flush=True)
    print(f"     Σ m(m+1)/2 = {total_psd_raw}  (expect 110 for symmetric commutant)",
          flush=True)

    # Verify dimensions
    total_check = sum(len(idx) for _, idx in clusters)
    assert total_check == 256, f"Eigenvalue clustering lost dimensions: {total_check}"

    # ── 6. Identify isotypic components ──────────────────────────────────
    print("  6. Projecting orbit matrices and grouping blocks...", flush=True)
    blocks = identify_unique_blocks(clusters, vecs, C0, C_pt, C_pr, K, Mpair)

    total_dim = sum(b["total_dim"] for b in blocks)
    total_psd_params = sum(b["m"] * (b["m"] + 1) // 2 for b in blocks)
    n_scalar = sum(1 for b in blocks if b["m"] == 1)
    n_matrix = sum(1 for b in blocks if b["m"] > 1)

    block_info = []
    for i, b in enumerate(blocks):
        info = {
            "block": i,
            "m": b["m"],
            "d": b["d"],
            "total_dim": b["total_dim"],
            "psd_params": b["m"] * (b["m"] + 1) // 2,
        }
        block_info.append(info)

    print(f"     {len(blocks)} unique blocks (isotypic components)", flush=True)
    print(f"     scalar (m=1): {n_scalar}, matrix (m>1): {n_matrix}", flush=True)
    for b in blocks:
        if b["m"] > 1:
            print(f"       m={b['m']}, d={b['d']}, dim={b['total_dim']}, "
                  f"PSD params={b['m']*(b['m']+1)//2}", flush=True)
    print(f"     total PSD params: {total_psd_params}, dim check: {total_dim} "
          f"({time.time()-t0:.1f}s)", flush=True)

    # ── 7. Validate block decomposition on analysis witnesses ─────────────
    print("  7. Validating on analysis witnesses...", flush=True)
    wb_path = ROOT / "workspace/data/invariant_pair_block/pair_block_triangles.json"
    validation_records = []
    if wb_path.exists():
        wb_data = json.loads(wb_path.read_text())
        for rec in wb_data.get("results", []):
            n_vec = rec["n_by_point_orbit"]
            m_vec = rec["m_by_pair_orbit"]
            z = np.zeros(N, dtype=float)
            for a in range(K):
                z[a] = n_vec[a] / sizes[a]
            for j in range(Mpair):
                z[K + j] = m_vec[j] / pair_sizes[j]
            # Full 256×256 eigenvalues
            Mfull = build_full_moment_matrix(z, pt_orb, pair_orb, K, Mpair)
            full_eigs = np.linalg.eigvalsh(Mfull)
            full_min = float(full_eigs[0])
            full_neg = int(np.sum(full_eigs < -1e-10))
            # Block eigenvalues
            block_mins = []
            block_negs_total = 0
            for b in blocks:
                B = b["B0"].copy()
                for a in range(K):
                    B += z[a] * b["Bp"][a]
                for j in range(Mpair):
                    B += z[K + j] * b["Bj"][j]
                if b["m"] == 1:
                    bval = float(B)
                    block_mins.append(bval)
                    if bval < -1e-10:
                        block_negs_total += b["d"]
                else:
                    beigs = np.linalg.eigvalsh(B)
                    block_mins.append(float(beigs[0]))
                    neg = int(np.sum(beigs < -1e-10))
                    block_negs_total += neg * b["d"]
            recon_min = min(block_mins)
            vrec = {
                "label": rec["label"],
                "n": n_vec,
                "full_min_eig": full_min,
                "full_neg_count": full_neg,
                "block_min_eig": recon_min,
                "block_neg_count": block_negs_total,
                "full_block_consistent": abs(recon_min - full_min) < 1e-6,
            }
            validation_records.append(vrec)
            print(f"     {rec['label']}: full min={full_min:.6f}, "
                  f"block min={recon_min:.6f}, neg={full_neg}/{block_negs_total}",
                  flush=True)

    # ── 8. Build Wang RLT + triangle constraints ─────────────────────────
    print("  8. Building Wang RLT + triangle constraints...", flush=True)
    lut, _ = load_lut(LUT_PATH)
    records, wmeta = build_core_constraints(CoreQuotient(1), lut)
    print(f"     records={len(records)} ({time.time()-t0:.1f}s)", flush=True)

    eq_A, eq_b, ub_A, ub_b, K2, M2, N2, n_aj = build_lp(
        records, pt_orb, orbits, pair_orb, Mpair, pair_ep
    )
    assert (K2, M2, N2) == (K, Mpair, N)
    Aeq = dense_rows_to_csr(eq_A, N)
    beq = np.array(eq_b, dtype=float)
    Aub = dense_rows_to_csr(ub_A, N)
    bub = np.array(ub_b, dtype=float)
    n_rlt = Aub.shape[0]

    Atri, btri, tri_meta = build_triangle_constraints(pt_orb, pair_orb, K, Mpair)
    Aub_all = sparse.vstack([Aub, Atri], format="csr")
    bub_all = np.concatenate([bub, btri])

    print(f"     linear: {Aeq.shape[0]} eq, {Aub_all.shape[0]} ub "
          f"(RLT={n_rlt}, tri={tri_meta['unique_triangle_inequalities']}) "
          f"({time.time()-t0:.1f}s)", flush=True)

    # ── 9. Formulate and solve block SDP ─────────────────────────────────
    print("  9. Formulating block SDP with CVXPY...", flush=True)
    import cvxpy as cp

    z_var = cp.Variable(N, name="z")

    constraints = [
        Aeq @ z_var == beq,
        Aub_all @ z_var <= bub_all,
        z_var >= 0,
        z_var <= 1,
    ]

    n_scalar_psd = 0
    n_matrix_psd = 0
    largest_block = 0

    for b in blocks:
        m = b["m"]
        if m == 1:
            # Scalar PSD = linear constraint
            coeff = np.zeros(N, dtype=float)
            for a in range(K):
                coeff[a] = float(b["Bp"][a])
            for j in range(Mpair):
                coeff[K + j] = float(b["Bj"][j])
            rhs = -float(b["B0"])
            constraints.append(coeff @ z_var >= rhs)
            n_scalar_psd += 1
        else:
            # Matrix PSD constraint: B0 + Σ x_a Bp[a] + Σ y_j Bj[j] >> 0
            B_expr = cp.Constant(b["B0"])
            for a in range(K):
                if np.any(np.abs(b["Bp"][a]) > 1e-15):
                    B_expr = B_expr + z_var[a] * b["Bp"][a]
            for j in range(Mpair):
                if np.any(np.abs(b["Bj"][j]) > 1e-15):
                    B_expr = B_expr + z_var[K + j] * b["Bj"][j]
            constraints.append(B_expr >> 0)
            n_matrix_psd += 1
            largest_block = max(largest_block, m)

    print(f"     {n_scalar_psd} scalar PSD constraints, "
          f"{n_matrix_psd} matrix PSD blocks (largest m={largest_block})", flush=True)

    print("  10. Solving with CLARABEL...", flush=True)
    prob = cp.Problem(cp.Minimize(0), constraints)
    solve_t0 = time.time()
    try:
        prob.solve(solver=cp.CLARABEL, verbose=True, max_iter=500,
                   tol_gap_abs=1e-8, tol_gap_rel=1e-8)
    except Exception as e:
        print(f"     solver exception: {e}", flush=True)
        prob_status = f"exception: {e}"
    else:
        prob_status = prob.status
    solve_sec = time.time() - solve_t0
    print(f"     status: {prob_status}, solve time: {solve_sec:.1f}s "
          f"({time.time()-t0:.1f}s total)", flush=True)

    # ── 11. Analyse result ───────────────────────────────────────────────
    feasible_point = None
    full_verification = None
    if z_var.value is not None:
        zval = np.array(z_var.value).flatten()
        # Verify by reconstructing full 256×256 matrix
        Mfull = build_full_moment_matrix(zval, pt_orb, pair_orb, K, Mpair)
        full_eigs = np.linalg.eigvalsh(Mfull)
        full_min = float(full_eigs[0])
        full_neg = int(np.sum(full_eigs < -1e-8))
        # Check linear feasibility
        eq_res = float(np.max(np.abs(Aeq @ zval - beq)))
        ub_res = float(np.max(Aub_all @ zval - bub_all))
        feasible_point = {
            "x_by_orbit": [float(zval[a]) for a in range(K)],
            "n_mass_by_orbit": [float(sizes[a] * zval[a]) for a in range(K)],
            "total_mass": float(sum(sizes[a] * zval[a] for a in range(K))),
            "y_nonzero_count": int(np.sum(np.abs(zval[K:]) > 1e-10)),
        }
        full_verification = {
            "full_256_min_eig": full_min,
            "full_256_neg_count_1e8": full_neg,
            "eq_max_residual": eq_res,
            "ub_max_violation": ub_res,
        }
        print(f"     solution: full 256×256 min eig = {full_min:.10f}, "
              f"neg count = {full_neg}", flush=True)
        print(f"     linear: eq resid = {eq_res:.2e}, ub viol = {ub_res:.2e}",
              flush=True)
        print(f"     masses: {feasible_point['n_mass_by_orbit']}", flush=True)
        # Save full z
        np.save(OUT / "feasible_z.npy", zval)

    # ── 12. Save results ─────────────────────────────────────────────────
    result = {
        "schema": "block_sdp_v1",
        "meaning": (
            "Block-decomposed SDP for the E11 moment matrix. "
            "Feasible = Wang+RLT+triangle+PSD admits a continuous moment point "
            "(not a support). Infeasible = the moment-matrix PSD condition, "
            "combined with Wang RLT, excludes all continuous solutions."
        ),
        "elapsed_sec": round(time.time() - t0, 3),
        "stabiliser_order": len(perms),
        "n_variables": N,
        "block_decomposition": {
            "n_blocks": len(blocks),
            "n_scalar_psd": n_scalar_psd,
            "n_matrix_psd": n_matrix_psd,
            "largest_block": largest_block,
            "total_psd_params": total_psd_params,
            "total_dim_check": total_dim,
            "block_info": block_info,
            "multiplicity_histogram": mult_hist,
        },
        "linear_model": {
            "n_eq": int(Aeq.shape[0]),
            "n_ub_rlt": n_rlt,
            "n_ub_triangle": tri_meta["unique_triangle_inequalities"],
            "n_ub_total": int(Aub_all.shape[0]),
        },
        "sdp_solve_sec": round(solve_sec, 3),
        "sdp_status": str(prob_status),
        "sdp_value": float(prob.value) if prob.value is not None else None,
        "feasible_point": feasible_point,
        "full_verification": full_verification,
        "block_witness_validation": validation_records,
    }
    (OUT / "block_sdp_result.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n"
    )
    print(f"\n  Saved: {OUT / 'block_sdp_result.json'}", flush=True)
    print(json.dumps({
        "status": str(prob_status),
        "n_blocks": len(blocks),
        "n_scalar_psd": n_scalar_psd,
        "n_matrix_psd": n_matrix_psd,
        "largest_block": largest_block,
        "solve_sec": round(solve_sec, 3),
        "feasible_min_eig": full_verification["full_256_min_eig"] if full_verification else None,
    }, indent=2), flush=True)


if __name__ == "__main__":
    main()
