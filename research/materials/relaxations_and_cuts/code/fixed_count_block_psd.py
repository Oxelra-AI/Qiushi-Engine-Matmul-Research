#!/usr/bin/env python3
"""analysis: fixed-orbit-count block-total + PSD test for E11 pair moments.

analysis showed feasibility for Wang+RLT+triangle+PSD with first moments fixed to
integer orbit means x_a=n_a/|O_a|, but it did not impose the deterministic orbit
count identities preserved by averaging one actual support over the E11
stabilizer.  For a genuine support with orbit counts n_a and pair-orbit counts
m_j = |P_j| y_j, the block totals must satisfy

    sum_{P_j subset O_a x O_b} |P_j| y_j = n_a n_b       (a<b)
    sum_{P_j subset binom(O_a,2)} |P_j| y_j = C(n_a,2)   (a=a).

Equivalently, the moment matrix has forced kernels
    u_a = (-n_a, 1_{O_a}) with M u_a = 0.

This script tests a bounded selection of count vectors using the small PSD
blocks from analysis.  It is still a continuous moment test: feasible means an
orbit-averaged second-moment witness exists for that n, not an actual support.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, List, Tuple

import numpy as np
from scipy import sparse
from scipy.linalg import eigh

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
from rlt_triangle_integrality import (  # noqa: E402
    build_triangle_constraints,
    dense_rows_to_csr,
)
from block_sdp_v2 import (  # noqa: E402
    build_full_moment_matrix,
    build_orbit_coeff_matrices,
    cluster_eigenvalues,
    form_group_algebra_element,
)

OUT = ROOT / "workspace/data/fixed_count_block_psd"


def as_tuple(n: Iterable[int]) -> Tuple[int, ...]:
    return tuple(int(x) for x in n)


def load_candidate_counts(max_from: int = 30, include: bool = True) -> list[dict]:
    """Load a bounded, provenance-labelled set of count vectors."""
    out: list[dict] = []
    seen: set[Tuple[int, ...]] = set()

    p69 = ROOT / "workspace/data/block_sdp/integer_count_psd_results.json"
    if p69.exists():
        d = json.loads(p69.read_text())
        for rec in d.get("results", [])[:max_from]:
            n = as_tuple(rec["n"])
            if n not in seen:
                seen.add(n)
                out.append({
                    "n": list(n),
                    "source": "integer_mean_psd",
                    "source_status": rec.get("status"),
                    "source_feasible": rec.get("feasible"),
                    "l1_dist": rec.get("l1_dist"),
                })

    if include:
        p66 = ROOT / "workspace/data/invariant_pair_block/pair_block_triangles.json"
        if p66.exists():
            d = json.loads(p66.read_text())
            for rec in d.get("results", []):
                n = as_tuple(rec.get("n_by_point_orbit", []))
                if len(n) == 6 and n not in seen:
                    seen.add(n)
                    out.append({
                        "n": list(n),
                        "source": "integer_pair_block_witness_n",
                        "source_status": rec.get("status"),
                        "source_label": rec.get("label"),
                        "source_exact_count_feasible": rec.get("exact_fraction_check", {}).get("is_exact_feasible"),
                    })
    return out


def build_block_total_rows(pair_sizes, pair_ep, K: int, Mpair: int):
    """Return rows B such that B y = deterministic block pair totals."""
    rows = []
    labels = []
    for a in range(K):
        row = np.zeros(Mpair, dtype=float)
        for j, (u, v) in enumerate(pair_ep):
            if int(u) == a and int(v) == a:
                row[j] += float(pair_sizes[j])
        rows.append(row); labels.append((a, a))
    for a in range(K):
        for b in range(a + 1, K):
            row = np.zeros(Mpair, dtype=float)
            for j, (u, v) in enumerate(pair_ep):
                if int(u) == a and int(v) == b:
                    row[j] += float(pair_sizes[j])
            rows.append(row); labels.append((a, b))
    return np.vstack(rows), labels


def target_block_totals(n_vec: list[int], labels: list[tuple[int, int]]):
    vals = []
    for a, b in labels:
        if a == b:
            vals.append(n_vec[a] * (n_vec[a] - 1) // 2)
        else:
            vals.append(n_vec[a] * n_vec[b])
    return np.array(vals, dtype=float)


def moment_kernel_residuals(Mfull: np.ndarray, n_vec: list[int], point_orbits: list[list[int]]):
    vals = []
    for a, orb in enumerate(point_orbits):
        u = np.zeros(256, dtype=float)
        u[0] = -float(n_vec[a])
        for p in orb:
            u[int(p)] = 1.0
        vals.append(float(np.max(np.abs(Mfull @ u))))
    return vals


def solve_one_count(n_vec, source, sizes, K, Mpair, pair_sizes, pair_ep,
                    Aeq, beq, Aub_all, bub_all, blocks, pt_orb, pair_orb,
                    point_orbits, block_rows, block_labels, solver="CLARABEL"):
    import cvxpy as cp

    x_fixed = np.array([n_vec[a] / sizes[a] for a in range(K)], dtype=float)
    y = cp.Variable(Mpair, name="y")

    # Substitute fixed first moments into all linear constraints.
    Aeq_x = Aeq[:, :K]; Aeq_y = Aeq[:, K:]
    Aub_x = Aub_all[:, :K]; Aub_y = Aub_all[:, K:]
    beq_sub = beq - Aeq_x @ x_fixed
    bub_sub = bub_all - Aub_x @ x_fixed
    btot = target_block_totals(n_vec, block_labels)

    constraints = [
        Aeq_y @ y == beq_sub,
        Aub_y @ y <= bub_sub,
        block_rows @ y == btot,
        y >= 0,
        y <= 1,
    ]

    # Block PSD constraints with x fixed.
    scalar_blocks = 0; matrix_blocks = 0
    for b in blocks:
        m = b["m"]
        B_fixed = b["B0"].copy()
        for a in range(K):
            B_fixed += x_fixed[a] * b["Bp"][a]
        if m == 1:
            coeff = np.array([float(b["Bj"][j]) for j in range(Mpair)], dtype=float)
            constraints.append(coeff @ y >= -float(B_fixed))
            scalar_blocks += 1
        else:
            B_expr = cp.Constant(np.asarray(B_fixed, dtype=float))
            for j in range(Mpair):
                Bj = b["Bj"][j]
                if np.any(np.abs(Bj) > 1e-15):
                    B_expr = B_expr + y[j] * np.asarray(Bj, dtype=float)
            constraints.append(B_expr >> 0)
            matrix_blocks += 1

    prob = cp.Problem(cp.Minimize(0), constraints)
    solve_t0 = time.time()
    try:
        if solver == "CLARABEL":
            prob.solve(solver=cp.CLARABEL, verbose=False, max_iter=500,
                       tol_gap_abs=1e-8, tol_gap_rel=1e-8, tol_feas=1e-8)
        else:
            prob.solve(solver=solver, verbose=False)
        status = str(prob.status)
    except Exception as e:
        status = f"error: {e}"
    solve_sec = time.time() - solve_t0

    rec = {
        "n": list(map(int, n_vec)),
        "source": source,
        "status": status,
        "solver": solver,
        "solve_sec": round(solve_sec, 3),
        "scalar_psd_blocks": scalar_blocks,
        "matrix_psd_blocks": matrix_blocks,
    }
    if y.value is not None:
        yval = np.array(y.value, dtype=float).flatten()
        z = np.zeros(K + Mpair, dtype=float)
        z[:K] = x_fixed; z[K:] = yval
        Mfull = build_full_moment_matrix(z, pt_orb, pair_orb, K)
        eig = np.linalg.eigvalsh(Mfull)
        eq_resid = float(np.max(np.abs(Aeq @ z - beq)))
        ub_viol = float(np.max(Aub_all @ z - bub_all))
        block_res = block_rows @ yval - btot
        kernel_res = moment_kernel_residuals(Mfull, list(map(int, n_vec)), point_orbits)
        m_float = np.array(pair_sizes, dtype=float) * yval
        rec.update({
            "linear_eq_resid": eq_resid,
            "linear_ub_viol": ub_viol,
            "block_total_max_abs_resid": float(np.max(np.abs(block_res))),
            "kernel_max_abs_resid": float(max(kernel_res)),
            "kernel_residuals_by_orbit": kernel_res,
            "psd_min_eig": float(eig[0]),
            "psd_neg_count_1e_8": int(np.sum(eig < -1e-8)),
            "psd_neg_count_1e_7": int(np.sum(eig < -1e-7)),
            "y_min": float(np.min(yval)),
            "y_max": float(np.max(yval)),
            "nonzero_y_orbits_1e_10": int(np.sum(np.abs(yval) > 1e-10)),
            "m_integrality_max_distance": float(np.max(np.abs(m_float - np.rint(m_float)))),
            "m_integrality_sum_distance": float(np.sum(np.abs(m_float - np.rint(m_float)))),
            "m_total_float": float(np.sum(m_float)),
            "block_totals": [
                {"block": [int(a), int(b)], "value": float((block_rows @ yval)[i]), "target": float(btot[i]), "residual": float(block_res[i])}
                for i, (a, b) in enumerate(block_labels)
            ],
        })
        rec["numerically_feasible"] = bool(
            ("optimal" in status)
            and eq_resid <= 1e-6
            and ub_viol <= 1e-6
            and rec["block_total_max_abs_resid"] <= 1e-6
            and rec["kernel_max_abs_resid"] <= 1e-6
            and rec["psd_min_eig"] >= -1e-7
            and rec["y_min"] >= -1e-7
            and rec["y_max"] <= 1 + 1e-7
        )
        rec["z_vector_saved"] = None
        rec["y_vector_saved"] = None
    else:
        rec["numerically_feasible"] = False
    return rec, (np.array(y.value).flatten() if y.value is not None else None)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-analysis", type=int, default=30)
    ap.add_argument("--include-analysis", action="store_true")
    ap.add_argument("--solver", default="CLARABEL")
    ap.add_argument("--out", type=Path, default=OUT / "fixed_count_block_psd_results.json")
    args = ap.parse_args()

    t0 = time.time()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    print("analysis: fixed count + block-total + block-PSD test", flush=True)

    # Infrastructure.
    print("  1. Build stabilizer, orbits, and PSD blocks", flush=True)
    perms = build_stabilizer()
    pt_orb, point_orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, Mpair = compute_pair_orbits(perms, pt_orb)
    K = len(point_orbits); N = K + Mpair; sizes = [len(o) for o in point_orbits]
    C0, C_pt, C_pr = build_orbit_coeff_matrices(point_orbits, pair_orb, K, Mpair)
    H = form_group_algebra_element(perms, seed=69)
    vals, vecs = eigh(H)
    clusters = cluster_eigenvalues(vals, tol=1e-6)
    blocks = []
    for cval, indices in clusters:
        U = vecs[:, indices].copy(); m = len(indices)
        B0 = U.T @ (C0 @ U); B0 = (B0 + B0.T) / 2
        Bp = []
        for a in range(K):
            B = U.T @ (C_pt[a] @ U); B = (B + B.T) / 2; Bp.append(B)
        Bj = []
        for j in range(Mpair):
            B = U.T @ (C_pr[j] @ U); B = (B + B.T) / 2; Bj.append(B)
        blocks.append({"m": m, "eigenvalue": float(cval), "B0": B0, "Bp": Bp, "Bj": Bj})
    print(f"     |G|={len(perms)}, point_sizes={sizes}, pair_orbits={Mpair}, blocks={len(blocks)}, largest={max(b['m'] for b in blocks)} ({time.time()-t0:.1f}s)", flush=True)

    # Linear model.
    print("  2. Build Wang RLT + triangle rows", flush=True)
    lut, lut_meta = load_lut(LUT_PATH)
    records, wmeta = build_core_constraints(CoreQuotient(1), lut)
    eq_A, eq_b, ub_A, ub_b, K2, M2, N2, n_aj = build_lp(records, pt_orb, point_orbits, pair_orb, Mpair, pair_ep)
    assert (K2, M2, N2) == (K, Mpair, N)
    Aeq = dense_rows_to_csr(eq_A, N); beq = np.array(eq_b, dtype=float)
    Aub = dense_rows_to_csr(ub_A, N); bub = np.array(ub_b, dtype=float)
    Atri, btri, tri_meta = build_triangle_constraints(pt_orb, pair_orb, K, Mpair)
    Aub_all = sparse.vstack([Aub, Atri], format="csr")
    bub_all = np.concatenate([bub, btri])
    print(f"     eq={Aeq.shape[0]}, ub={Aub_all.shape[0]} (RLT={Aub.shape[0]}, tri={Atri.shape[0]}) ({time.time()-t0:.1f}s)", flush=True)

    block_rows, block_labels = build_block_total_rows(pair_sizes, pair_ep, K, Mpair)
    print(f"     block-total rows={block_rows.shape[0]}", flush=True)

    candidates = load_candidate_counts(args.max, args.include)
    print(f"  3. Testing {len(candidates)} count vectors", flush=True)
    results = []
    saved_witnesses = []
    for i, c in enumerate(candidates):
        rec, yval = solve_one_count(
            c["n"], c, sizes, K, Mpair, pair_sizes, pair_ep,
            Aeq, beq, Aub_all, bub_all, blocks, pt_orb, pair_orb,
            point_orbits, block_rows, block_labels, solver=args.solver)
        results.append(rec)
        tag = "OK" if rec.get("numerically_feasible") else "NO"
        print(f"    [{i+1:02d}] n={c['n']} {tag} status={rec['status']} minEig={rec.get('psd_min_eig')} ub={rec.get('linear_ub_viol')} block={rec.get('block_total_max_abs_resid')}", flush=True)
        # Save full vectors for the first few numerically feasible witnesses.
        if yval is not None and rec.get("numerically_feasible") and len(saved_witnesses) < 3:
            stem = "n_" + "_".join(str(v) for v in c["n"])
            y_path = args.out.parent / f"{stem}_y.npy"
            z_path = args.out.parent / f"{stem}_z.npy"
            z = np.zeros(N, dtype=float)
            z[:K] = np.array([c["n"][a] / sizes[a] for a in range(K)], dtype=float)
            z[K:] = yval
            np.save(y_path, yval); np.save(z_path, z)
            rec["y_vector_saved"] = str(y_path)
            rec["z_vector_saved"] = str(z_path)
            saved_witnesses.append({"n": c["n"], "y": str(y_path), "z": str(z_path)})

    status_counts = Counter(r.get("status") for r in results)
    n_num = sum(1 for r in results if r.get("numerically_feasible"))
    payload = {
        "schema": "fixed_count_block_psd_v1",
        "meaning": "For fixed orbit counts n, impose Wang RLT, triangle/Fortet rows, deterministic orbit-block pair totals, and the block-decomposed 256x256 PSD condition. Feasible is a continuous second-moment witness for that count vector, not a point support and not an exact rank result.",
        "field": "F2",
        "core": "E11 quotient distinct projected-A branch",
        "point_orbit_sizes": sizes,
        "pair_orbit_count": int(Mpair),
        "block_psd": {"n_blocks": len(blocks), "largest_block": int(max(b["m"] for b in blocks)), "histogram": {str(k): int(v) for k, v in sorted(Counter(b["m"] for b in blocks).items())}},
        "linear_model": {"n_eq": int(Aeq.shape[0]), "n_ub_rlt": int(Aub.shape[0]), "n_ub_triangle": int(Atri.shape[0]), "n_ub_total": int(Aub_all.shape[0]), "block_total_equalities": int(block_rows.shape[0])},
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "candidate_count": len(candidates),
        "status_counts": {str(k): int(v) for k, v in sorted(status_counts.items())},
        "numerically_feasible_count": int(n_num),
        "saved_witnesses": saved_witnesses,
        "results": results,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(args.out),
        "tested": len(results),
        "numerically_feasible": n_num,
        "status_counts": payload["status_counts"],
        "saved_witnesses": saved_witnesses,
        "elapsed_sec": payload["elapsed_sec"],
    }, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
