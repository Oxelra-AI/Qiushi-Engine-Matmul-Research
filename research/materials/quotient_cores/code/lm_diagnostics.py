#!/usr/bin/env python3
r"""
analysis: bounded LM continuation with gauge/norm/conditioning diagnostics.

Scientific purpose:
  The analysis real LM run reduced the rank-22 residual for T_333 to 2.23e-4
  from a cn122 one-term truncation, but without recording the factor trajectory.
  This script reruns the same deterministic starting route in short LM segments,
  saving states and diagnostics after each segment so the numerical campaign can
  distinguish a bounded approach to an exact rank-22 point from noncompact
  cancellation/degeneration.

Diagnostics recorded:
  * relative residual and gradient infinity norm ||J^T f||_inf,
  * term-balanced factor norms and total tensor-term amplitude,
  * a diagonal GL3^3 stabilizer normalization proxy (post term balancing),
  * U/V/W span singular values and UV-pairing singular values,
  * Brent Jacobian singular spectrum around ranks 526 and 550.

No numerical result here is a rank theorem.  Any near-zero candidate must later
be gauge-fixed, reconstructed over an exact field, and checked against all 729
Brent identities.
"""
from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
from scipy.optimize import least_squares, minimize

M = 9
R = 22


def make_T333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.float64)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1.0
    return T


def load_qmm(path: Path) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    U, V, W = [], [], []
    for line in path.read_text().splitlines():
        p = line.strip().split()
        if len(p) >= 10 and p[0] in ("u", "v", "w"):
            {"u": U, "v": V, "w": W}[p[0]].append([float(x) for x in p[1:10]])
    return np.array(U, dtype=np.float64).T, np.array(V, dtype=np.float64).T, np.array(W, dtype=np.float64).T


def khatri_rao(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    return (A[:, None, :] * B[None, :, :]).reshape(A.shape[0] * B.shape[0], -1)


def tensor_from(U: np.ndarray, V: np.ndarray, W: np.ndarray) -> np.ndarray:
    return np.einsum("ir,jr,kr->ijk", U, V, W)


def als_cp(T: np.ndarray, r: int, U0=None, V0=None, W0=None, max_iter: int = 3000, reg: float = 1e-12):
    m = T.shape[0]
    Tn = np.linalg.norm(T)
    T1 = T.reshape(m, m * m)
    T2 = T.transpose(1, 0, 2).reshape(m, m * m)
    T3 = T.transpose(2, 0, 1).reshape(m, m * m)
    rng = np.random.default_rng(2026090525)
    U = U0.copy() if U0 is not None else rng.standard_normal((m, r))
    V = V0.copy() if V0 is not None else rng.standard_normal((m, r))
    W = W0.copy() if W0 is not None else rng.standard_normal((m, r))
    best = np.inf
    best_state = None
    for it in range(max_iter):
        KR = khatri_rao(V, W)
        U = np.linalg.solve(KR.T @ KR + reg * np.eye(r), KR.T @ T1.T).T
        KR = khatri_rao(U, W)
        V = np.linalg.solve(KR.T @ KR + reg * np.eye(r), KR.T @ T2.T).T
        KR = khatri_rao(U, V)
        W = np.linalg.solve(KR.T @ KR + reg * np.eye(r), KR.T @ T3.T).T
        if (it + 1) % 25 == 0 or it == max_iter - 1:
            res = np.linalg.norm(T - tensor_from(U, V, W)) / Tn
            if res < best:
                best = res
                best_state = (U.copy(), V.copy(), W.copy())
            if res < 1e-14:
                break
    if best_state is not None:
        U, V, W = best_state
    else:
        best = np.linalg.norm(T - tensor_from(U, V, W)) / Tn
    return U, V, W, float(best)


def pack(U: np.ndarray, V: np.ndarray, W: np.ndarray) -> np.ndarray:
    return np.concatenate([U.ravel(), V.ravel(), W.ravel()])


def unpack(x: np.ndarray, r: int = R) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    return x[: M * r].reshape(M, r), x[M * r : 2 * M * r].reshape(M, r), x[2 * M * r :].reshape(M, r)


def brent_res(x: np.ndarray, T_flat: np.ndarray, r: int = R) -> np.ndarray:
    U, V, W = unpack(x, r)
    return T_flat - tensor_from(U, V, W).ravel()


def brent_jac(x: np.ndarray, T_flat: np.ndarray, r: int = R) -> np.ndarray:
    U, V, W = unpack(x, r)
    J = np.zeros((M**3, 3 * M * r), dtype=np.float64)
    VW = np.einsum("bi,ci->bci", V, W).reshape(M * M, r)
    for a in range(M):
        J[a * M * M : (a + 1) * M * M, a * r : (a + 1) * r] = -VW
    UW = np.einsum("ai,ci->aci", U, W)
    for b in range(M):
        col_start = M * r + b * r
        for a in range(M):
            row_start = a * M * M + b * M
            J[row_start : row_start + M, col_start : col_start + r] = -UW[a, :, :]
    UV = np.einsum("ai,bi->abi", U, V).reshape(M * M, r)
    row_base = np.array([a * M * M + b * M for a in range(M) for b in range(M)])
    for c in range(M):
        rows = row_base + c
        col_start = 2 * M * r + c * r
        J[rows, col_start : col_start + r] = -UV
    return J


def term_balance(U: np.ndarray, V: np.ndarray, W: np.ndarray, eps: float = 1e-300):
    U2, V2, W2 = U.copy(), V.copy(), W.copy()
    nu = np.linalg.norm(U2, axis=0)
    nv = np.linalg.norm(V2, axis=0)
    nw = np.linalg.norm(W2, axis=0)
    prod = np.maximum(nu * nv * nw, eps)
    q = prod ** (1.0 / 3.0)
    U2 *= (q / np.maximum(nu, eps))[None, :]
    V2 *= (q / np.maximum(nv, eps))[None, :]
    W2 *= (q / np.maximum(nw, eps))[None, :]
    return U2, V2, W2


def apply_diag_stabilizer(U: np.ndarray, V: np.ndarray, W: np.ndarray, z: np.ndarray):
    # z contains p[0:3], q[0:3], r[0:3].  Means are removed to suppress null drifts.
    p = z[:3].copy(); q = z[3:6].copy(); rr = z[6:9].copy()
    p -= np.mean(p); q -= np.mean(q); rr -= np.mean(rr)
    # clip exponent arguments for numerical safety in the diagnostic optimizer
    Uo = U.copy(); Vo = V.copy(); Wo = W.copy()
    for t in range(U.shape[1]):
        Um = Uo[:, t].reshape(3, 3)
        Vm = Vo[:, t].reshape(3, 3)
        Wm = Wo[:, t].reshape(3, 3)
        SU = np.exp(np.clip(p[:, None] - q[None, :], -30, 30))
        SV = np.exp(np.clip(q[:, None] - rr[None, :], -30, 30))
        SW = np.exp(np.clip(-p[:, None] + rr[None, :], -30, 30))
        Uo[:, t] = (SU * Um).reshape(9)
        Vo[:, t] = (SV * Vm).reshape(9)
        Wo[:, t] = (SW * Wm).reshape(9)
    return Uo, Vo, Wo


def balanced_objective_from_z(z: np.ndarray, U: np.ndarray, V: np.ndarray, W: np.ndarray) -> float:
    Ug, Vg, Wg = apply_diag_stabilizer(U, V, W, z)
    Ub, Vb, Wb = term_balance(Ug, Vg, Wg)
    # log objective is more stable when occasional terms are tiny/large.
    val = np.sum(Ub * Ub) + np.sum(Vb * Vb) + np.sum(Wb * Wb)
    return float(math.log(max(val, 1e-300)))


def diag_gauge_metrics(U: np.ndarray, V: np.ndarray, W: np.ndarray) -> Dict:
    z0 = np.zeros(9, dtype=np.float64)
    raw_obj = balanced_objective_from_z(z0, U, V, W)
    try:
        opt = minimize(
            balanced_objective_from_z,
            z0,
            args=(U, V, W),
            method="BFGS",
            options={"maxiter": 80, "gtol": 1e-6},
        )
        z = opt.x if np.isfinite(opt.fun) else z0
        ok = bool(opt.success or opt.fun <= raw_obj + 1e-9)
    except Exception as exc:  # keep diagnostics robust
        z = z0
        opt = None
        ok = False
    Ug, Vg, Wg = apply_diag_stabilizer(U, V, W, z)
    Ub, Vb, Wb = term_balance(Ug, Vg, Wg)
    term_products = np.linalg.norm(Ub, axis=0) * np.linalg.norm(Vb, axis=0) * np.linalg.norm(Wb, axis=0)
    frob2 = float(np.sum(Ub * Ub) + np.sum(Vb * Vb) + np.sum(Wb * Wb))
    return {
        "diag_opt_ok": ok,
        "diag_log_objective_before": float(raw_obj),
        "diag_log_objective_after": float(balanced_objective_from_z(z, U, V, W)),
        "diag_z_projected": [float(x) for x in np.r_[z[:3]-np.mean(z[:3]), z[3:6]-np.mean(z[3:6]), z[6:9]-np.mean(z[6:9])]],
        "diag_balanced_total_frob": float(math.sqrt(frob2)),
        "diag_balanced_amplitude_sum_products": float(np.sum(term_products)),
        "diag_balanced_max_product": float(np.max(term_products)),
    }


def sv_metrics(A: np.ndarray, label: str) -> Dict:
    s = np.linalg.svd(A, compute_uv=False)
    tol = max(A.shape) * np.finfo(float).eps * (s[0] if len(s) else 1.0)
    rank = int(np.sum(s > tol))
    out = {
        f"{label}_rank_tol": rank,
        f"{label}_smax": float(s[0]) if len(s) else 0.0,
        f"{label}_smin": float(s[-1]) if len(s) else 0.0,
        f"{label}_condition_tol": float(s[0] / s[rank - 1]) if rank > 0 else float("inf"),
        f"{label}_singular_values_tail5": [float(x) for x in s[-5:]],
    }
    return out


def factor_metrics(U: np.ndarray, V: np.ndarray, W: np.ndarray) -> Dict:
    Ub, Vb, Wb = term_balance(U, V, W)
    nu = np.linalg.norm(Ub, axis=0); nv = np.linalg.norm(Vb, axis=0); nw = np.linalg.norm(Wb, axis=0)
    prod = nu * nv * nw
    X = khatri_rao(Ub, Vb)
    out = {
        "term_balanced_total_amplitude_sum_products": float(np.sum(prod)),
        "term_balanced_max_product": float(np.max(prod)),
        "term_balanced_min_product": float(np.min(prod)),
        "term_balanced_product_quantiles": [float(x) for x in np.quantile(prod, [0, 0.25, 0.5, 0.75, 1])],
        "term_balanced_factor_frobenius": {
            "U": float(np.linalg.norm(Ub)),
            "V": float(np.linalg.norm(Vb)),
            "W": float(np.linalg.norm(Wb)),
            "total": float(math.sqrt(np.sum(Ub*Ub)+np.sum(Vb*Vb)+np.sum(Wb*Wb))),
        },
        "raw_factor_frobenius": {"U": float(np.linalg.norm(U)), "V": float(np.linalg.norm(V)), "W": float(np.linalg.norm(W))},
    }
    out.update(sv_metrics(Ub, "U_span"))
    out.update(sv_metrics(Vb, "V_span"))
    out.update(sv_metrics(Wb, "W_span"))
    out.update(sv_metrics(X, "UV_pairing"))
    # determinant distribution is useful because cn122 individual factors are singular;
    # this is not a proof invariant, only a diagnostic of matrix-factor behavior.
    for name, A in [("U", Ub), ("V", Vb), ("W", Wb)]:
        dets = [float(np.linalg.det(A[:, i].reshape(3, 3))) for i in range(A.shape[1])]
        out[f"{name}_det_abs_max"] = float(np.max(np.abs(dets)))
        out[f"{name}_det_abs_median"] = float(np.median(np.abs(dets)))
    out.update(diag_gauge_metrics(U, V, W))
    return out


def jacobian_spectrum_metrics(J: np.ndarray) -> Dict:
    s = np.linalg.svd(J, compute_uv=False)
    # Sorted descending. Generic rank-22 image has rank 550 (=594-44 scaling kernel).
    # A bounded exact T333 rank-22 point would have at least 68 kernel directions,
    # so singular values indices 526..549 should collapse as residual goes to zero.
    def get(idx: int) -> float:
        return float(s[idx]) if 0 <= idx < len(s) else float("nan")
    s0 = float(s[0])
    thresholds = [1e-6, 1e-8, 1e-10, 1e-12]
    return {
        "J_smax": s0,
        "J_s_525_rank526_last_expected_nonzero": get(525),
        "J_s_526_first_extra_stabilizer_band": get(526),
        "J_s_549_generic_rank550_last_nonzero": get(549),
        "J_s_550_first_scaling_kernel": get(550),
        "J_band_526_549_min": float(np.min(s[526:550])),
        "J_band_526_549_max": float(np.max(s[526:550])),
        "J_band_526_549_median": float(np.median(s[526:550])),
        "J_condition_to_s525": float(s0 / max(get(525), 1e-300)),
        "J_condition_to_s549": float(s0 / max(get(549), 1e-300)),
        "J_n_singular_gt_rel": {str(th): int(np.sum(s > th * s0)) for th in thresholds},
        "J_tail_50": [float(x) for x in s[-50:]],
    }


def compute_metrics(x: np.ndarray, T: np.ndarray, label: str, elapsed: float, nfev_total: int) -> Dict:
    T_flat = T.ravel(); Tn = np.linalg.norm(T)
    f = brent_res(x, T_flat, R)
    rel = float(np.linalg.norm(f) / Tn)
    J = brent_jac(x, T_flat, R)
    grad = J.T @ f
    U, V, W = unpack(x, R)
    out = {
        "label": label,
        "elapsed_sec": float(elapsed),
        "nfev_total": int(nfev_total),
        "relative_residual": rel,
        "residual_norm": float(np.linalg.norm(f)),
        "grad_inf_norm": float(np.max(np.abs(grad))),
        "grad_l2_norm": float(np.linalg.norm(grad)),
    }
    out.update(factor_metrics(U, V, W))
    out.update(jacobian_spectrum_metrics(J))
    return out


def parse_segments(s: str) -> List[int]:
    return [int(x) for x in s.split(",") if x.strip()]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--drop", type=int, default=1)
    ap.add_argument("--als-iters", type=int, default=3000)
    ap.add_argument("--segments", default="500,500,1000,1000,1000", help="comma-separated LM max_nfev segments")
    ap.add_argument("--outdir", default="data/lm_diagnostics")
    ap.add_argument("--max-factor-amplitude", type=float, default=1e5, help="stop if term-balanced amplitude exceeds this")
    args = ap.parse_args()

    t_start = time.time()
    root = Path(__file__).resolve().parent.parent
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    T = make_T333()
    T_flat = T.ravel()
    Tn = float(np.linalg.norm(T))
    U23, V23, W23 = load_qmm(root / "data/cn122_r23_reproduce/scheme.qmm")
    cn122_rel = float(np.linalg.norm(T - tensor_from(U23, V23, W23)) / Tn)
    print(f"T333 norm={Tn:.8g}; cn122 rank-23 residual={cn122_rel:.3e}", flush=True)

    # Baseline metrics for cn122 (rank 23 amplitude only; no J spectrum because rank differs).
    base23_metrics = factor_metrics(U23, V23, W23)

    cols = [j for j in range(23) if j != args.drop]
    print(f"ALS warm-up from cn122 drop={args.drop}, cols={cols}, iters={args.als_iters}", flush=True)
    U, V, W, als_res = als_cp(T, R, U23[:, cols], V23[:, cols], W23[:, cols], max_iter=args.als_iters)
    x = pack(U, V, W)
    print(f"ALS best relative residual={als_res:.8e}", flush=True)

    trajectory = []
    metrics0 = compute_metrics(x, T, "after_ALS", time.time() - t_start, 0)
    trajectory.append(metrics0)
    print(
        "METRIC after_ALS "
        f"rel={metrics0['relative_residual']:.8e} grad_inf={metrics0['grad_inf_norm']:.3e} "
        f"amp={metrics0['term_balanced_total_amplitude_sum_products']:.3e} "
        f"diag_amp={metrics0['diag_balanced_amplitude_sum_products']:.3e} "
        f"Jband_med={metrics0['J_band_526_549_median']:.3e} s549={metrics0['J_s_549_generic_rank550_last_nonzero']:.3e}",
        flush=True,
    )
    np.savez_compressed(outdir / "state_after_ALS.npz", x=x, U=U, V=V, W=W)

    total_nfev = 0
    segments = parse_segments(args.segments)
    for seg_idx, seg_nfev in enumerate(segments, start=1):
        print(f"\nLM segment {seg_idx}/{len(segments)} max_nfev={seg_nfev}", flush=True)
        t0 = time.time()
        res = least_squares(
            brent_res,
            x,
            jac=brent_jac,
            args=(T_flat, R),
            method="lm",
            max_nfev=seg_nfev,
            ftol=1e-15,
            xtol=1e-15,
            gtol=1e-15,
        )
        x = res.x.copy()
        total_nfev += int(res.nfev)
        U, V, W = unpack(x, R)
        met = compute_metrics(x, T, f"LM_segment_{seg_idx}", time.time() - t_start, total_nfev)
        met.update({
            "segment_nfev": int(res.nfev),
            "segment_requested_nfev": int(seg_nfev),
            "segment_status": int(res.status),
            "segment_message": str(res.message),
            "segment_cost": float(res.cost),
            "segment_elapsed_sec": float(time.time() - t0),
            "scipy_optimality": float(res.optimality),
        })
        trajectory.append(met)
        np.savez_compressed(outdir / f"state_segment_{seg_idx:02d}.npz", x=x, U=U, V=V, W=W)
        # Save after every segment so timeout still leaves durable evidence.
        partial = {
            "description": "analysis segmented LM diagnostics from cn122 one-term truncation",
            "drop": args.drop,
            "als_iters": args.als_iters,
            "segments_requested": segments,
            "T333_norm": Tn,
            "cn122_rank23_residual": cn122_rel,
            "cn122_rank23_factor_metrics": base23_metrics,
            "trajectory": trajectory,
        }
        (outdir / "trajectory_partial.json").write_text(json.dumps(partial, indent=2) + "\n")
        print(
            f"METRIC segment={seg_idx} rel={met['relative_residual']:.8e} "
            f"grad_inf={met['grad_inf_norm']:.3e} scipy_opt={met['scipy_optimality']:.3e} "
            f"amp={met['term_balanced_total_amplitude_sum_products']:.3e} "
            f"diag_amp={met['diag_balanced_amplitude_sum_products']:.3e} "
            f"UV_smin={met['UV_pairing_smin']:.3e} "
            f"Jband_med={met['J_band_526_549_median']:.3e} "
            f"J_s526={met['J_s_526_first_extra_stabilizer_band']:.3e} "
            f"J_s549={met['J_s_549_generic_rank550_last_nonzero']:.3e} "
            f"status={res.status} nfev={res.nfev} time={met['segment_elapsed_sec']:.1f}s",
            flush=True,
        )
        if met["term_balanced_total_amplitude_sum_products"] > args.max_factor_amplitude:
            print("STOP: amplitude exceeded configured bound; treating this as possible noncompact degeneration.", flush=True)
            break
        if met["relative_residual"] < 1e-10:
            print("STOP: residual below numerical candidate threshold; exact reconstruction should be attempted next.", flush=True)
            break

    summary = {
        "description": "analysis bounded numerical campaign: LM continuation with term/diagonal gauge diagnostics and Jacobian conditioning.",
        "drop": args.drop,
        "als_iters": args.als_iters,
        "segments_requested": segments,
        "T333_norm": Tn,
        "cn122_rank23_residual": cn122_rel,
        "cn122_rank23_factor_metrics": base23_metrics,
        "trajectory": trajectory,
        "best_by_residual": min(trajectory, key=lambda d: d["relative_residual"]),
        "interpretation_template": {
            "bounded_route_indicator": "falling residual and gradient with stable term/diagonal-gauge amplitudes and no collapse of UV rank",
            "degeneration_indicator": "falling residual accompanied by rapidly growing amplitude, worsening span/pairing conditioning, or noncompact diagonal gauge parameters",
            "rank22_exact_requirement": "a numerical near-root is only useful after high-precision gauge fixing, exact reconstruction, and all 729 Brent identities",
        },
        "elapsed_sec": time.time() - t_start,
    }
    (outdir / "trajectory.json").write_text(json.dumps(summary, indent=2) + "\n")
    np.savez_compressed(outdir / "best_state.npz", x=x, U=U, V=V, W=W)
    print(f"\nSaved trajectory to {outdir / 'trajectory.json'}", flush=True)
    print(f"Saved best/current state to {outdir / 'best_state.npz'}", flush=True)


if __name__ == "__main__":
    main()
