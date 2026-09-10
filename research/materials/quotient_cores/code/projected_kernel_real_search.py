#!/usr/bin/env python3
r"""
analysis: real-valued projected-kernel rank-22 search with live pivot terms.

For T_333 let L be its 9-dimensional UV/W flattening image and let
Q: R^81 -> R^72 annihilate L.  For r=22 and full X=[u_i \otimes v_i],
existence of W with T_333 = X W^T is equivalent to rank(QX)=13.

On a 13-column chart this script solves
    Q x_j = sum_a C[a,j] Q x_{piv_a},       j in the 9 remaining terms,
with all U,V factors and all C entries live.  Pivot terms are only the chart
basis for the projected columns; they are not frozen.

Any numerical zero must be followed by reconstruction of W and all 729 Brent
identities.  The script records X-rank, rank(QX), inclusion residual, and
factor amplitude so spurious low-rank or noncompact behavior is visible.
"""
from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
from scipy.linalg import qr
from scipy.optimize import least_squares

M = 9
R = 22
PIV = 13
REM = 9


def make_T333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.float64)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1.0
    return T


def t333_uv_flat(T: np.ndarray) -> np.ndarray:
    return T.reshape(81, 9)


def sparse_t333_quotient() -> np.ndarray:
    support_by_c = {c: [] for c in range(9)}
    support_rows = set()
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a = 3 * i + j
                b = 3 * j + k
                c = 3 * i + k
                uv = a * 9 + b
                support_by_c[c].append(uv)
                support_rows.add(uv)
    rows = []
    for uv in range(81):
        if uv not in support_rows:
            e = np.zeros(81)
            e[uv] = 1.0
            rows.append(e)
    for c in range(9):
        supp = sorted(support_by_c[c])
        anchor = supp[0]
        for uv in supp[1:]:
            e = np.zeros(81)
            e[uv] = 1.0
            e[anchor] = -1.0
            rows.append(e)
    Q = np.array(rows, dtype=np.float64)
    assert Q.shape == (72, 81)
    return Q


def load_qmm(path: Path) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    U, V, W = [], [], []
    for line in path.read_text().splitlines():
        p = line.strip().split()
        if len(p) >= 10 and p[0] in ("u", "v", "w"):
            {"u": U, "v": V, "w": W}[p[0]].append([float(x) for x in p[1:10]])
    return np.array(U, dtype=np.float64).T, np.array(V, dtype=np.float64).T, np.array(W, dtype=np.float64).T


def tensor_from(U: np.ndarray, V: np.ndarray, W: np.ndarray) -> np.ndarray:
    return np.einsum("ir,jr,kr->ijk", U, V, W)


def khatri_rao(U: np.ndarray, V: np.ndarray) -> np.ndarray:
    return (U[:, None, :] * V[None, :, :]).reshape(U.shape[0] * V.shape[0], -1)


def qx_and_derivatives(U: np.ndarray, V: np.ndarray, Q: np.ndarray):
    X = khatri_rao(U, V)
    QX = Q @ X
    Q3 = Q.reshape(72, 9, 9)
    dqu = np.empty((R, 72, 9), dtype=np.float64)
    dqv = np.empty((R, 72, 9), dtype=np.float64)
    for t in range(R):
        vt = V[:, t]
        ut = U[:, t]
        for a in range(9):
            dqu[t, :, a] = Q3[:, a, :] @ vt
        for b in range(9):
            dqv[t, :, b] = Q3[:, :, b] @ ut
    return X, QX, dqu, dqv


def pack(U: np.ndarray, V: np.ndarray, C: np.ndarray) -> np.ndarray:
    return np.concatenate([U.ravel(), V.ravel(), C.ravel()])


def unpack(z: np.ndarray) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    U = z[: M * R].reshape(M, R)
    V = z[M * R : 2 * M * R].reshape(M, R)
    C = z[2 * M * R :].reshape(PIV, REM)
    return U, V, C


def projected_residual_matrix(U: np.ndarray, V: np.ndarray, C: np.ndarray, Q: np.ndarray, piv: List[int], rem: List[int]) -> np.ndarray:
    X = khatri_rao(U, V)
    QX = Q @ X
    return QX[:, rem] - QX[:, piv] @ C


def projected_fun(z: np.ndarray, Q: np.ndarray, piv: List[int], rem: List[int]) -> np.ndarray:
    U, V, C = unpack(z)
    return projected_residual_matrix(U, V, C, Q, piv, rem).ravel()


def projected_jac(z: np.ndarray, Q: np.ndarray, piv: List[int], rem: List[int]) -> np.ndarray:
    U, V, C = unpack(z)
    X, QX, dqu, dqv = qx_and_derivatives(U, V, Q)
    J = np.zeros((72 * REM, 2 * M * R + PIV * REM), dtype=np.float64)
    piv_pos = {t: a for a, t in enumerate(piv)}
    rem_pos = {t: l for l, t in enumerate(rem)}
    # U,V derivatives.
    for t in range(R):
        if t in rem_pos:
            l = rem_pos[t]
            rows = np.arange(72) * REM + l
            J[rows, t : M * R : R] += dqu[t]
            J[rows, M * R + t : 2 * M * R : R] += dqv[t]
        if t in piv_pos:
            a = piv_pos[t]
            for l in range(REM):
                coef = -C[a, l]
                if coef != 0.0:
                    rows = np.arange(72) * REM + l
                    J[rows, t : M * R : R] += coef * dqu[t]
                    J[rows, M * R + t : 2 * M * R : R] += coef * dqv[t]
    # C derivatives.
    c0 = 2 * M * R
    for a in range(PIV):
        qcol = QX[:, piv[a]]
        for l in range(REM):
            rows = np.arange(72) * REM + l
            J[rows, c0 + a * REM + l] = -qcol
    return J


def term_balance(U: np.ndarray, V: np.ndarray, W: np.ndarray | None = None):
    if W is None:
        nu = np.linalg.norm(U, axis=0)
        nv = np.linalg.norm(V, axis=0)
        s = np.sqrt(np.maximum(nu * nv, 1e-300))
        U2 = U * (s / np.maximum(nu, 1e-300))[None, :]
        V2 = V * (s / np.maximum(nv, 1e-300))[None, :]
        return U2, V2
    nu = np.linalg.norm(U, axis=0)
    nv = np.linalg.norm(V, axis=0)
    nw = np.linalg.norm(W, axis=0)
    q = np.maximum(nu * nv * nw, 1e-300) ** (1 / 3)
    return U * (q / np.maximum(nu, 1e-300))[None, :], V * (q / np.maximum(nv, 1e-300))[None, :], W * (q / np.maximum(nw, 1e-300))[None, :]


def sv_info(A: np.ndarray, name: str) -> Dict:
    s = np.linalg.svd(A, compute_uv=False)
    out = {
        f"{name}_smax": float(s[0]) if len(s) else 0.0,
        f"{name}_smin": float(s[-1]) if len(s) else 0.0,
        f"{name}_tail10": [float(x) for x in s[-10:]],
    }
    return out


def choose_pivots(QX: np.ndarray, mode: str) -> List[int]:
    if mode == "first13":
        return list(range(13))
    _, _, perm = qr(QX, mode="economic", pivoting=True)
    return [int(x) for x in perm[:PIV]]


def initial_C(QX: np.ndarray, piv: List[int], rem: List[int]) -> np.ndarray:
    A = QX[:, piv]
    B = QX[:, rem]
    C, *_ = np.linalg.lstsq(A, B, rcond=None)
    return C


def inclusion_metrics(U: np.ndarray, V: np.ndarray, T: np.ndarray, Q: np.ndarray, C: np.ndarray, piv: List[int], rem: List[int]) -> Dict:
    Tuv = t333_uv_flat(T)
    X = khatri_rao(U, V)
    QX = Q @ X
    Wt, *_ = np.linalg.lstsq(X, Tuv, rcond=None)  # X W^T = Tuv
    T_hat = X @ Wt
    W = Wt.T
    rel_incl = float(np.linalg.norm(Tuv - T_hat) / np.linalg.norm(Tuv))
    full_rel = float(np.linalg.norm(T - tensor_from(U, V, W)) / np.linalg.norm(T))
    Ub, Vb, Wb = term_balance(U, V, W)
    prod = np.linalg.norm(Ub, axis=0) * np.linalg.norm(Vb, axis=0) * np.linalg.norm(Wb, axis=0)
    Rmat = projected_residual_matrix(U, V, C, Q, piv, rem)
    s_qx = np.linalg.svd(QX, compute_uv=False)
    out = {
        "projected_residual_rel": float(np.linalg.norm(Rmat) / max(np.linalg.norm(QX), 1e-300)),
        "projected_residual_norm": float(np.linalg.norm(Rmat)),
        "fixed_UV_best_W_relative_residual": rel_incl,
        "full_tensor_relative_residual_with_best_W": full_rel,
        "X_rank_tol": int(np.linalg.matrix_rank(X, tol=1e-9 * max(X.shape) * (np.linalg.svd(X, compute_uv=False)[0] if X.size else 1.0))),
        "QX_rank_tol": int(np.linalg.matrix_rank(QX, tol=1e-9 * max(QX.shape) * (s_qx[0] if len(s_qx) else 1.0))),
        "QX_singular_values_10_to_18": [float(x) for x in s_qx[9:18]],
        "QX_s13_index12": float(s_qx[12]) if len(s_qx) > 12 else float("nan"),
        "QX_s14_index13": float(s_qx[13]) if len(s_qx) > 13 else float("nan"),
        "QX_s15_index14": float(s_qx[14]) if len(s_qx) > 14 else float("nan"),
        "bestW_term_balanced_amplitude_sum_products": float(np.sum(prod)),
        "bestW_term_balanced_max_product": float(np.max(prod)),
        "bestW_norm": float(np.linalg.norm(W)),
    }
    out.update(sv_info(X, "X"))
    out.update(sv_info(QX, "QX"))
    return out


def finite_difference_smoke(z: np.ndarray, Q: np.ndarray, piv: List[int], rem: List[int], rng: np.random.Generator) -> float:
    J = projected_jac(z, Q, piv, rem)
    f0 = projected_fun(z, Q, piv, rem)
    err = 0.0
    eps = 1e-7
    for j in rng.choice(z.size, size=min(20, z.size), replace=False):
        zp = z.copy(); zm = z.copy()
        zp[j] += eps; zm[j] -= eps
        fd = (projected_fun(zp, Q, piv, rem) - projected_fun(zm, Q, piv, rem)) / (2 * eps)
        err = max(err, float(np.max(np.abs(fd - J[:, j]))))
    return err


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--drop", type=int, default=1)
    ap.add_argument("--pivot-mode", choices=["first13", "qr"], default="qr")
    ap.add_argument("--max-nfev", type=int, default=2000)
    ap.add_argument("--from-state", default="", help="optional .npz with U,V to initialize")
    ap.add_argument("--outdir", default="data/projected_kernel_real_search")
    ap.add_argument("--smoke", action="store_true")
    args = ap.parse_args()
    t0 = time.time()
    root = Path(__file__).resolve().parent.parent
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    T = make_T333()
    Q = sparse_t333_quotient()
    assert np.linalg.norm(Q @ t333_uv_flat(T)) < 1e-12
    if args.from_state:
        state = np.load(args.from_state)
        U0 = np.array(state["U"], dtype=np.float64)
        V0 = np.array(state["V"], dtype=np.float64)
        source = args.from_state
    else:
        U23, V23, W23 = load_qmm(root / "data/cn122_r23_reproduce/scheme.qmm")
        cols = [j for j in range(23) if j != args.drop]
        U0 = U23[:, cols]
        V0 = V23[:, cols]
        source = f"cn122_drop_{args.drop}_raw"
    X0 = khatri_rao(U0, V0)
    QX0 = Q @ X0
    piv = choose_pivots(QX0, args.pivot_mode)
    rem = [j for j in range(R) if j not in set(piv)]
    # keep only 9 remaining terms; a 13-term pivot set in 22 terms always has 9 remaining
    assert len(rem) == REM
    C0 = initial_C(QX0, piv, rem)
    z0 = pack(U0, V0, C0)
    rng = np.random.default_rng(2026090525)
    jac_err = finite_difference_smoke(z0, Q, piv, rem, rng) if args.smoke else None
    init_met = inclusion_metrics(U0, V0, T, Q, C0, piv, rem)
    print(f"source={source}; pivot_mode={args.pivot_mode}; piv={piv}; rem={rem}", flush=True)
    if jac_err is not None:
        print(f"Jacobian finite-difference max error on sampled columns={jac_err:.2e}", flush=True)
    print(
        f"initial projected_rel={init_met['projected_residual_rel']:.8e} "
        f"UV_bestW_rel={init_met['fixed_UV_best_W_relative_residual']:.8e} "
        f"rankQX={init_met['QX_rank_tol']} s14={init_met['QX_s14_index13']:.3e} "
        f"amp={init_met['bestW_term_balanced_amplitude_sum_products']:.3e}",
        flush=True,
    )
    res = least_squares(
        projected_fun,
        z0,
        jac=projected_jac,
        args=(Q, piv, rem),
        method="lm",
        max_nfev=args.max_nfev,
        ftol=1e-15,
        xtol=1e-15,
        gtol=1e-15,
    )
    U, V, C = unpack(res.x)
    final_met = inclusion_metrics(U, V, T, Q, C, piv, rem)
    print(
        f"final projected_rel={final_met['projected_residual_rel']:.8e} "
        f"UV_bestW_rel={final_met['fixed_UV_best_W_relative_residual']:.8e} "
        f"rankQX={final_met['QX_rank_tol']} s13={final_met['QX_s13_index12']:.3e} "
        f"s14={final_met['QX_s14_index13']:.3e} s15={final_met['QX_s15_index14']:.3e} "
        f"amp={final_met['bestW_term_balanced_amplitude_sum_products']:.3e} "
        f"status={res.status} nfev={res.nfev} opt={res.optimality:.3e}",
        flush=True,
    )
    summary = {
        "description": "Real projected-kernel 13-column chart search with all U,V,pivot columns live.",
        "source": source,
        "drop": args.drop,
        "pivot_mode": args.pivot_mode,
        "pivots": piv,
        "remaining": rem,
        "max_nfev": args.max_nfev,
        "jacobian_sample_max_error": jac_err,
        "initial": init_met,
        "final": final_met,
        "scipy": {
            "status": int(res.status),
            "message": str(res.message),
            "nfev": int(res.nfev),
            "cost": float(res.cost),
            "optimality": float(res.optimality),
        },
        "elapsed_sec": time.time() - t0,
        "scientific_use": "If projected residual reaches zero while X has rank 22 and fixed-UV best-W residual is zero, this yields a numerical rank-22 candidate to exactify; otherwise the run tests accessibility of the transverse projected-kernel equations in this chart only.",
    }
    out_path = outdir / f"projected_kernel_{Path(str(source)).stem}_piv{args.pivot_mode}_nfev{args.max_nfev}.json"
    out_path.write_text(json.dumps(summary, indent=2) + "\n")
    np.savez_compressed(outdir / f"projected_kernel_{Path(str(source)).stem}_state.npz", U=U, V=V, C=C, piv=np.array(piv), rem=np.array(rem))
    print(f"saved {out_path}", flush=True)


if __name__ == "__main__":
    main()
