#!/usr/bin/env python3
"""analysis: global RLT+triangle+PSD separation for the E11 distinct-support model.

The analysis relay incorrectly treated the uniform first-moment extension
    x_p = 19/255, y_pq = 19*18/(255*254)
as feasible for Wang RLT.  It is PSD and satisfies first-order Wang, but cap-1
RLT rows can force particular y_pq to zero, so uniform-y violates RLT.

This script keeps the six point-orbit moments free and tests the global
orbit-averaged RLT+triangle model against labelled moment-matrix positivity.
It also repairs the analysis PSD-cut extraction: coefficients are for normalized
moment variables x_a, y_j and therefore must be UNDIVORED orbit sums:

  v^T M v = v0^2
            + sum_a [2 v0 sum_{p in O_a} v_p + sum_{p in O_a} v_p^2] x_a
            + sum_j [2 sum_{ {p,q} in P_j } v_p v_q] y_j.

Dividing those coefficients by orbit sizes gives count-variable coefficients;
evaluating such divided coefficients against normalized moments is wrong.

The separation loop adds valid square inequalities w^T M w >= 0, with integer
vectors w obtained by rounding violated eigenvectors.  The LP solves are still
floating-point exploratory computations; any infeasibility conclusion would need
an exact replay/Farkas certificate before entering the lower-bound chain.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from collections import Counter
from fractions import Fraction
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

OUT = ROOT / "workspace/data/global_psd"


def make_pair_var_matrix(pair_orb: Dict[Tuple[int, int], int]) -> np.ndarray:
    mat = np.full((256, 256), -1, dtype=np.int16)
    for (p, q), j in pair_orb.items():
        mat[p, q] = j
        mat[q, p] = j
    return mat


def build_moment_matrix(z: np.ndarray, pt_orb: List[int], pair_var: np.ndarray, K: int) -> np.ndarray:
    """Build the labelled 256x256 moment matrix from normalized orbit variables."""
    M = np.zeros((256, 256), dtype=float)
    M[0, 0] = 1.0
    x_by_point = np.zeros(256, dtype=float)
    for p in range(1, 256):
        x_by_point[p] = z[pt_orb[p]]
    M[0, 1:] = x_by_point[1:]
    M[1:, 0] = x_by_point[1:]
    for p in range(1, 256):
        M[p, p] = x_by_point[p]
    y = z[K:]
    for p in range(1, 256):
        # Python loop is fine: 32385 pairs.
        for q in range(p + 1, 256):
            val = y[int(pair_var[p, q])]
            M[p, q] = val
            M[q, p] = val
    return M


def moment_kernel_residual(M: np.ndarray) -> dict:
    u = np.ones(256, dtype=float)
    u[0] = -19.0
    Mu = M @ u
    return {
        "max_abs_Mu": float(np.max(np.abs(Mu))),
        "norm_Mu": float(np.linalg.norm(Mu)),
        "quad_u": float(u @ M @ u),
    }


def fixed_coefficients_for_vector(w: np.ndarray, orbits: List[List[int]], pair_var: np.ndarray,
                                  K: int, Mpair: int) -> Tuple[int, np.ndarray, np.ndarray]:
    """Exact integer coefficients for w^T M w in normalized x_a,y_j variables."""
    wi = np.asarray(w, dtype=object)
    w0 = int(wi[0])
    const = w0 * w0
    xcoef = np.zeros(K, dtype=object)
    for a, orb in enumerate(orbits):
        s1 = sum(int(wi[p]) for p in orb)
        s2 = sum(int(wi[p]) * int(wi[p]) for p in orb)
        xcoef[a] = 2 * w0 * s1 + s2
    ycoef = np.zeros(Mpair, dtype=object)
    for p in range(1, 256):
        wp = int(wi[p])
        if wp == 0:
            # Even when wp=0, skip many operations for sparse rounded vectors.
            continue
        for q in range(p + 1, 256):
            wq = int(wi[q])
            if wq:
                ycoef[int(pair_var[p, q])] += 2 * wp * wq
    return int(const), np.array([int(v) for v in xcoef], dtype=object), np.array([int(v) for v in ycoef], dtype=object)


def float_quad_from_coeff(const: int, xcoef: np.ndarray, ycoef: np.ndarray, z: np.ndarray, K: int) -> float:
    return float(const) + float(np.dot(np.array(xcoef, dtype=float), z[:K])) + float(np.dot(np.array(ycoef, dtype=float), z[K:]))


def exact_quad_for_counts(const: int, xcoef: np.ndarray, ycoef: np.ndarray,
                          n_vec: List[int], m_vec: List[int], orbit_sizes: List[int],
                          pair_sizes: List[int]) -> Fraction:
    val = Fraction(int(const), 1)
    for a, n in enumerate(n_vec):
        if xcoef[a] and n:
            val += Fraction(int(xcoef[a]) * int(n), int(orbit_sizes[a]))
    for j, m in enumerate(m_vec):
        if ycoef[j] and m:
            val += Fraction(int(ycoef[j]) * int(m), int(pair_sizes[j]))
    return val


def integerize_negative_direction(v: np.ndarray, z: np.ndarray, orbits: List[List[int]], pair_var: np.ndarray,
                                  K: int, Mpair: int, target_neg: float | None = None,
                                  scales=(64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384)) -> dict:
    """Round a violated eigenvector to an integer vector still violating the current moment."""
    vmax = float(np.max(np.abs(v)))
    if vmax == 0:
        raise ValueError("zero eigenvector")
    vn = v / vmax
    best = None
    for scale in scales:
        w = np.rint(vn * scale).astype(np.int64)
        if not np.any(w):
            continue
        # Divide gcd for compactness.
        g = 0
        for x in w:
            g = math.gcd(g, abs(int(x)))
        if g > 1:
            w = (w // g).astype(np.int64)
        const, xcoef, ycoef = fixed_coefficients_for_vector(w, orbits, pair_var, K, Mpair)
        q = float_quad_from_coeff(const, xcoef, ycoef, z, K)
        rec = {
            "scale": int(scale),
            "gcd": int(g),
            "float_quad_on_current_z": float(q),
            "nonzero_w": int(np.count_nonzero(w)),
            "max_abs_w": int(np.max(np.abs(w))),
            "const": int(const),
            "xcoef": [int(c) for c in xcoef],
            "ycoef": [int(c) for c in ycoef],
            "w": [int(x) for x in w.tolist()],
        }
        if best is None or q < best["float_quad_on_current_z"]:
            best = rec
        # A robust negative rounded cut.  Use absolute threshold because q scales with w^2.
        if q < -1e-7 * max(1.0, abs(float(const)), float(np.max(np.abs(np.array(xcoef, dtype=float)))) if len(xcoef) else 1.0):
            return rec
        if q < -1e-6:
            return rec
    if best is None:
        raise RuntimeError("failed to integerize eigenvector")
    return best


def add_square_cut(Aub: sparse.csr_matrix, bub: np.ndarray, cut: dict, K: int) -> Tuple[sparse.csr_matrix, np.ndarray, dict]:
    coeff = np.array(cut["xcoef"] + cut["ycoef"], dtype=float)
    rhs = float(cut["const"])
    # const + coeff*z >= 0  <=>  -coeff*z <= const.
    raw_row = -coeff
    raw_rhs = rhs
    scale = max(1.0, float(np.max(np.abs(raw_row))) if raw_row.size else 1.0, abs(raw_rhs))
    row = sparse.csr_matrix((raw_row / scale).reshape(1, -1))
    new_A = sparse.vstack([Aub, row], format="csr")
    new_b = np.concatenate([bub, np.array([raw_rhs / scale], dtype=float)])
    meta = {
        "normalization_scale": scale,
        "raw_rhs": raw_rhs,
        "max_abs_raw_coef": float(np.max(np.abs(raw_row))) if raw_row.size else 0.0,
    }
    return new_A, new_b, meta


def solve_feasible_lp(Aeq: sparse.csr_matrix, beq: np.ndarray, Aub: sparse.csr_matrix, bub: np.ndarray,
                      N: int, objective: np.ndarray | None = None) -> Tuple[object, float]:
    c = np.zeros(N, dtype=float) if objective is None else np.array(objective, dtype=float)
    t0 = time.time()
    res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                  bounds=[(0.0, 1.0)] * N, method="highs")
    return res, time.time() - t0


def residual_stats(Aeq: sparse.csr_matrix, beq: np.ndarray, Aub: sparse.csr_matrix, bub: np.ndarray, z: np.ndarray) -> dict:
    eq = Aeq @ z - beq
    ub = Aub @ z - bub
    return {
        "max_abs_eq": float(np.max(np.abs(eq))) if eq.size else 0.0,
        "max_ub_violation": float(max(0.0, np.max(ub))) if ub.size else 0.0,
        "min_ub_slack": float(np.min(-ub)) if ub.size else None,
        "violated_ub_count_1e-8": int(np.sum(ub > 1e-8)) if ub.size else 0,
    }


def load_block_witnesses() -> list:
    path = ROOT / "workspace/data/invariant_pair_block/pair_block_triangles.json"
    if not path.exists():
        return []
    data = json.loads(path.read_text())
    return data.get("results", [])


def repair_block_witness_cuts(witnesses: list, orbits, pair_var, pair_sizes, K, Mpair, out_jsonl: Path) -> Tuple[list, list]:
    """Recompute negative spectra and exact integer square cuts for analysis witnesses."""
    records = []
    cuts = []
    sizes = [len(o) for o in orbits]
    with out_jsonl.open("w") as f:
        for rec in witnesses:
            n_vec = rec["n_by_point_orbit"]
            m_vec = rec["m_by_pair_orbit"]
            z = np.zeros(K + Mpair, dtype=float)
            for a in range(K):
                z[a] = n_vec[a] / sizes[a]
            for j in range(Mpair):
                z[K + j] = m_vec[j] / pair_sizes[j]
            Mmat = build_moment_matrix(z, [0] + [None]*255, pair_var, K) if False else None
            # Build directly without pt_orb: use orbits to set point variables.
            Mmat = np.zeros((256, 256), dtype=float)
            Mmat[0, 0] = 1.0
            for a, orb in enumerate(orbits):
                for p in orb:
                    Mmat[0, p] = Mmat[p, 0] = z[a]
                    Mmat[p, p] = z[a]
            for p in range(1, 256):
                for q in range(p + 1, 256):
                    yval = z[K + int(pair_var[p, q])]
                    Mmat[p, q] = Mmat[q, p] = yval
            eigvals, eigvecs = np.linalg.eigh(Mmat)
            min_eig = float(eigvals[0])
            v = eigvecs[:, 0]
            cut = integerize_negative_direction(v, z, orbits, pair_var, K, Mpair)
            const, xcoef, ycoef = int(cut["const"]), np.array(cut["xcoef"], dtype=object), np.array(cut["ycoef"], dtype=object)
            exact_val = exact_quad_for_counts(const, xcoef, ycoef, n_vec, m_vec, sizes, pair_sizes)
            old_style_const, old_style_x, old_style_y = old_divided_cut_for_float(v, orbits, pair_var, pair_sizes, K, Mpair)
            old_eval = float(old_style_const + old_style_x @ z[:K] + old_style_y @ z[K:])
            fixed_const_f, fixed_x_f, fixed_y_f = fixed_cut_for_float(v, orbits, pair_var, K, Mpair)
            fixed_eval = float(fixed_const_f + fixed_x_f @ z[:K] + fixed_y_f @ z[K:])
            qdirect = float(v @ Mmat @ v)
            short = {
                "source": "block_witness",
                "label": rec["label"],
                "n_by_point_orbit": n_vec,
                "m_total": rec.get("m_total"),
                "min_eigenvalue": min_eig,
                "direct_float_vMv": qdirect,
                "fixed_undivided_reconstruction": fixed_eval,
                "old_divided_reconstruction_against_normalized_moments": old_eval,
                "integer_cut_float_quad": cut["float_quad_on_current_z"],
                "integer_cut_exact_quad_num_digits": len(str(abs(exact_val.numerator))),
                "integer_cut_exact_quad_denominator": str(exact_val.denominator),
                "integer_cut_exact_quad_is_negative": exact_val < 0,
                "integer_cut_exact_quad_float": float(exact_val),
                "integer_cut_nonzero_w": cut["nonzero_w"],
                "integer_cut_max_abs_w": cut["max_abs_w"],
            }
            records.append(short)
            full = {**short, "cut": cut}
            f.write(json.dumps(full, sort_keys=True) + "\n")
            if exact_val < 0:
                cuts.append(cut)
    return records, cuts


def fixed_cut_for_float(v: np.ndarray, orbits: List[List[int]], pair_var: np.ndarray,
                        K: int, Mpair: int) -> Tuple[float, np.ndarray, np.ndarray]:
    const = float(v[0] * v[0])
    xcoef = np.zeros(K, dtype=float)
    for a, orb in enumerate(orbits):
        s1 = float(np.sum(v[orb]))
        s2 = float(np.sum(v[orb] * v[orb]))
        xcoef[a] = 2.0 * float(v[0]) * s1 + s2
    ycoef = np.zeros(Mpair, dtype=float)
    for p in range(1, 256):
        vp = float(v[p])
        for q in range(p + 1, 256):
            ycoef[int(pair_var[p, q])] += 2.0 * vp * float(v[q])
    return const, xcoef, ycoef


def old_divided_cut_for_float(v: np.ndarray, orbits: List[List[int]], pair_var: np.ndarray,
                              pair_sizes: List[int], K: int, Mpair: int) -> Tuple[float, np.ndarray, np.ndarray]:
    """Replicate analysis's erroneous normalized-moment coefficient extraction."""
    const = float(v[0] * v[0])
    xcoef = np.zeros(K, dtype=float)
    for a, orb in enumerate(orbits):
        s1 = float(np.sum(v[orb]))
        s2 = float(np.sum(v[orb] * v[orb]))
        xcoef[a] = (2.0 * float(v[0]) * s1 + s2) / len(orb)
    ycoef = np.zeros(Mpair, dtype=float)
    for p in range(1, 256):
        vp = float(v[p])
        for q in range(p + 1, 256):
            j = int(pair_var[p, q])
            ycoef[j] += 2.0 * vp * float(v[q]) / pair_sizes[j]
    return const, xcoef, ycoef


def make_z_summary(z: np.ndarray, orbits, pair_sizes, K, Mpair, max_pairs: int = 30) -> dict:
    y = z[K:]
    nz = [
        {"pair_orbit": int(j), "y": float(y[j]), "m_float": float(pair_sizes[j] * y[j])}
        for j in range(Mpair) if y[j] > 1e-10
    ]
    nz_sorted = sorted(nz, key=lambda d: -abs(d["m_float"]))
    return {
        "x_by_point_orbit": [float(z[a]) for a in range(K)],
        "n_mass_by_point_orbit": [float(len(orbits[a]) * z[a]) for a in range(K)],
        "nonzero_pair_orbits": len(nz),
        "top_pair_masses": nz_sorted[:max_pairs],
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-cuts", type=int, default=40)
    ap.add_argument("--no-triangles", action="store_true")
    ap.add_argument("--add-repaired-block-cuts", action="store_true")
    ap.add_argument("--tol", type=float, default=1e-7)
    args = ap.parse_args()

    t0 = time.time()
    OUT.mkdir(parents=True, exist_ok=True)
    cut_jsonl = OUT / "psd_square_cuts.jsonl"
    if cut_jsonl.exists():
        cut_jsonl.unlink()

    print("analysis: global RLT+triangle + labelled moment PSD separation", flush=True)
    print("  1. Building stabilizer and orbits...", flush=True)
    perms = build_stabilizer()
    pt_orb, orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, Mpair = compute_pair_orbits(perms, pt_orb)
    pair_var = make_pair_var_matrix(pair_orb)
    K = len(orbits)
    N = K + Mpair
    print(f"     |G|={len(perms)}, point_orbits={K}, sizes={[len(o) for o in orbits]}, pair_orbits={Mpair} ({time.time()-t0:.1f}s)", flush=True)

    print("  2. Loading complete E11 Wang records...", flush=True)
    lut, _ = load_lut(LUT_PATH)
    records, wmeta = build_core_constraints(CoreQuotient(1), lut)
    print(f"     records={len(records)} ({time.time()-t0:.1f}s)", flush=True)

    print("  3. Building raw analysis RLT LP...", flush=True)
    eq_A, eq_b, ub_A, ub_b, K2, M2, N2, n_aj = build_lp(records, pt_orb, orbits, pair_orb, Mpair, pair_ep)
    assert (K2, M2, N2) == (K, Mpair, N)
    Aeq = dense_rows_to_csr(eq_A, N)
    beq = np.array(eq_b, dtype=float)
    Aub = dense_rows_to_csr(ub_A, N)
    bub = np.array(ub_b, dtype=float)
    base_rlt_ub = Aub.shape[0]
    tri_meta = None
    if not args.no_triangles:
        print("  4. Building repaired triangle/Fortet rows...", flush=True)
        Atri, btri, tri_meta = build_triangle_constraints(pt_orb, pair_orb, K, Mpair)
        Aub = sparse.vstack([Aub, Atri], format="csr")
        bub = np.concatenate([bub, btri])
        print(f"     triangle unique={tri_meta['unique_triangle_inequalities']} raw={tri_meta['raw_triangle_inequalities']} ({time.time()-t0:.1f}s)", flush=True)
    print(f"     global linear model: {Aeq.shape[0]} eq, {Aub.shape[0]} ub, N={N}", flush=True)

    # Uniform first moment + uniform distinct-pair extension regression.
    z_uniform = np.zeros(N, dtype=float)
    z_uniform[:K] = 19.0 / 255.0
    z_uniform[K:] = (19.0 * 18.0) / (255.0 * 254.0)
    uniform_lin = residual_stats(Aeq, beq, Aub, bub, z_uniform)
    Munif = build_moment_matrix(z_uniform, pt_orb, pair_var, K)
    eig_uniform = np.linalg.eigvalsh(Munif)
    uniform_psd = {
        "x_value": 19.0 / 255.0,
        "y_value": (19.0 * 18.0) / (255.0 * 254.0),
        "linear_residuals": uniform_lin,
        "max_ub_violation_positive_means_not_RLT_feasible": uniform_lin["max_ub_violation"],
        "psd_min_eigenvalue": float(eig_uniform[0]),
        "psd_negative_count_1e-10": int(np.sum(eig_uniform < -1e-10)),
        "kernel_residual": moment_kernel_residual(Munif),
    }
    print(f"  Uniform extension: max linear violation={uniform_lin['max_ub_violation']:.6g}, PSD min={eig_uniform[0]:.3e}", flush=True)

    # Repair analysis cut extraction on the exact analysis block witnesses.
    print("  5. Repairing analysis PSD cut extraction on block witnesses...", flush=True)
    block_witnesses = load_block_witnesses()
    block_records, repaired_block_cuts = repair_block_witness_cuts(
        block_witnesses, orbits, pair_var, pair_sizes, K, Mpair, OUT / "repaired_block_witness_cuts.jsonl")
    print(f"     repaired cuts exact-negative: {len(repaired_block_cuts)}/{len(block_witnesses)}", flush=True)

    active_cut_records = []
    if args.add_repaired_block_cuts:
        for idx, cut in enumerate(repaired_block_cuts):
            Aub, bub, meta = add_square_cut(Aub, bub, cut, K)
            active_cut_records.append({"kind": "repaired_block_cut", "source_index": idx, **meta})
        print(f"     added {len(repaired_block_cuts)} repaired block cuts to global LP", flush=True)

    # Cutting-plane loop.
    print("  6. Spectral separation loop with free first moments...", flush=True)
    loop_records = []
    status = "unresolved"
    final_z = None
    final_eigs = None
    objectives = [np.zeros(N, dtype=float)]
    # Add a small list of fixed objectives for alternate faces if needed.
    omitted_obj = np.zeros(N, dtype=float); omitted_obj[:4] = -np.array([len(orbits[a]) for a in range(4)], dtype=float)
    concentrated_obj = -omitted_obj
    objectives.extend([omitted_obj, concentrated_obj])

    with cut_jsonl.open("a") as cutf:
        for it in range(args.max_cuts + 1):
            obj = objectives[min(it, len(objectives)-1)] if it < len(objectives) else None
            res, solve_sec = solve_feasible_lp(Aeq, beq, Aub, bub, N, objective=obj)
            rec = {
                "iteration": it,
                "lp_status_code": int(res.status),
                "lp_message": str(res.message),
                "lp_success": bool(res.status == 0),
                "lp_solve_sec": round(solve_sec, 3),
                "n_active_psd_cuts": len(active_cut_records),
                "n_ub_total": int(Aub.shape[0]),
            }
            if res.status == 2:
                status = "lp_infeasible_after_square_cuts_floating"
                loop_records.append(rec)
                print(f"     iter {it}: LP infeasible after {len(active_cut_records)} square cuts", flush=True)
                break
            if res.status != 0 or res.x is None:
                status = "lp_solver_nonoptimal"
                loop_records.append(rec)
                print(f"     iter {it}: LP status {res.status}: {res.message}", flush=True)
                break
            z = np.array(res.x, dtype=float)
            Mmat = build_moment_matrix(z, pt_orb, pair_var, K)
            eigvals, eigvecs = np.linalg.eigh(Mmat)
            min_eig = float(eigvals[0])
            neg_count = int(np.sum(eigvals < -args.tol))
            rec.update({
                "linear_residuals": residual_stats(Aeq, beq, Aub, bub, z),
                "min_eigenvalue": min_eig,
                "negative_eig_count_tol": neg_count,
                "kernel_residual": moment_kernel_residual(Mmat),
                "z_summary": make_z_summary(z, orbits, pair_sizes, K, Mpair, max_pairs=10),
            })
            print(f"     iter {it}: LP ok in {solve_sec:.2f}s, min_eig={min_eig:.6g}, neg={neg_count}, cuts={len(active_cut_records)}", flush=True)
            if min_eig >= -args.tol:
                status = "psd_feasible_witness_found_numerical"
                final_z = z
                final_eigs = eigvals
                loop_records.append(rec)
                break
            if it == args.max_cuts:
                status = "max_cuts_reached_still_psd_violated"
                final_z = z
                final_eigs = eigvals
                loop_records.append(rec)
                break
            v = eigvecs[:, 0]
            cut = integerize_negative_direction(v, z, orbits, pair_var, K, Mpair)
            # Verify repaired undivided coefficients agree with current moment for the integer cut.
            qcur = float(cut["float_quad_on_current_z"])
            Aub, bub, meta = add_square_cut(Aub, bub, cut, K)
            cut_rec = {
                "kind": "separation_cut",
                "iteration": it,
                "min_eigenvalue_source": min_eig,
                "integer_cut_float_quad_on_source": qcur,
                **meta,
                "cut": cut,
            }
            active_cut_records.append({k: v for k, v in cut_rec.items() if k != "cut"})
            cutf.write(json.dumps(cut_rec, sort_keys=True) + "\n")
            cutf.flush()
            rec["added_cut_float_quad"] = qcur
            rec["added_cut_nonzero_w"] = cut["nonzero_w"]
            rec["added_cut_max_abs_w"] = cut["max_abs_w"]
            loop_records.append(rec)

    final_record = None
    if final_z is not None:
        final_record = {
            "z_summary": make_z_summary(final_z, orbits, pair_sizes, K, Mpair, max_pairs=40),
            "x_by_point_orbit": [float(final_z[a]) for a in range(K)],
            "y_by_pair_orbit": [float(final_z[K+j]) for j in range(Mpair)],
            "n_mass_by_point_orbit": [float(len(orbits[a]) * final_z[a]) for a in range(K)],
            "m_mass_by_pair_orbit": [float(pair_sizes[j] * final_z[K+j]) for j in range(Mpair)],
            "linear_residuals_final": residual_stats(Aeq, beq, Aub, bub, final_z),
            "psd_min_eigenvalue": float(final_eigs[0]) if final_eigs is not None else None,
            "psd_negative_count_1e-8": int(np.sum(final_eigs < -1e-8)) if final_eigs is not None else None,
            "psd_smallest_10_eigenvalues": [float(x) for x in final_eigs[:10]] if final_eigs is not None else None,
        }
        np.save(OUT / "final_z.npy", final_z)

    summary = {
        "schema": "global_psd_cut_loop_v1",
        "meaning": "Floating-point global separation test for the orbit-averaged complete-Wang RLT+triangle model with labelled moment PSD square cuts. Feasible PSD moment is not an A-support; infeasibility requires exact replay before use as a lower-bound proof.",
        "elapsed_sec": round(time.time() - t0, 3),
        "point_orbit_sizes": [len(o) for o in orbits],
        "point_orbit_reps": [o[0] for o in orbits],
        "pair_orbit_size_histogram": dict(Counter(pair_sizes)),
        "n_pair_orbits": Mpair,
        "n_variables": N,
        "n_eq_constraints": int(Aeq.shape[0]),
        "n_ub_constraints_base_rlt": int(base_rlt_ub),
        "triangle_meta": tri_meta,
        "n_ub_constraints_initial_with_triangles": int(base_rlt_ub + (tri_meta["unique_triangle_inequalities"] if tri_meta else 0)),
        "uniform_extension_regression": uniform_psd,
        "cut_extraction_repair": {
            "error": "analysis divided orbit-sum coefficients by orbit sizes but evaluated against normalized x_a,y_j; correct normalized-moment coefficients are undivided orbit sums.",
            "block_witness_repairs": block_records,
            "full_repaired_block_cuts_jsonl": str(OUT / "repaired_block_witness_cuts.jsonl"),
        },
        "added_repaired_block_cuts_to_loop": bool(args.add_repaired_block_cuts),
        "active_cut_records_without_full_coefficients": active_cut_records,
        "full_separation_cuts_jsonl": str(cut_jsonl),
        "loop_status": status,
        "loop_records": loop_records,
        "final_record": final_record,
    }
    (OUT / "global_psd_cut_loop_summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print("  Saved summary:", OUT / "global_psd_cut_loop_summary.json", flush=True)
    print(json.dumps({
        "status": status,
        "elapsed_sec": summary["elapsed_sec"],
        "uniform_max_linear_violation": uniform_lin["max_ub_violation"],
        "repaired_block_exact_negative": sum(1 for r in block_records if r["integer_cut_exact_quad_is_negative"]),
        "iterations": len(loop_records),
        "active_psd_cuts": len(active_cut_records),
        "final_min_eig": None if final_record is None else final_record["psd_min_eigenvalue"],
        "summary": str(OUT / "global_psd_cut_loop_summary.json"),
    }, indent=2), flush=True)


if __name__ == "__main__":
    main()
