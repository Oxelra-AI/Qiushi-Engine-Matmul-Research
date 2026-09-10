#!/usr/bin/env python3
r"""
analysis: structural extraction from the segmented real LM path.

Reads the saved states from lm_diagnostics_main and computes quantities
that connect the numerical path to the exact algebraic rank-22 formulations:
  * singular values of QX for the projected-kernel condition rank(QX)=13,
  * least-squares inclusion residual L(T333) subset span(X),
  * cancellation size of the 22 rank-one tensor columns,
  * dominant term products and small singular vectors of the term-column matrix.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np


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
    return np.array(rows, dtype=np.float64)


def khatri_rao(U: np.ndarray, V: np.ndarray) -> np.ndarray:
    return (U[:, None, :] * V[None, :, :]).reshape(U.shape[0] * V.shape[0], -1)


def tensor_from(U: np.ndarray, V: np.ndarray, W: np.ndarray) -> np.ndarray:
    return np.einsum("ir,jr,kr->ijk", U, V, W)


def term_columns(U: np.ndarray, V: np.ndarray, W: np.ndarray) -> np.ndarray:
    cols = []
    for t in range(U.shape[1]):
        cols.append(np.einsum("i,j,k->ijk", U[:, t], V[:, t], W[:, t]).ravel())
    return np.column_stack(cols)


def state_analysis(label: str, path: Path, T: np.ndarray, Q: np.ndarray) -> Dict:
    dat = np.load(path)
    U = np.array(dat["U"], dtype=np.float64)
    V = np.array(dat["V"], dtype=np.float64)
    W = np.array(dat["W"], dtype=np.float64)
    Tuv = T.reshape(81, 9)
    X = khatri_rao(U, V)
    QX = Q @ X
    s_qx = np.linalg.svd(QX, compute_uv=False)
    Wt_best, *_ = np.linalg.lstsq(X, Tuv, rcond=None)
    incl = np.linalg.norm(Tuv - X @ Wt_best) / np.linalg.norm(Tuv)
    rel = np.linalg.norm(T - tensor_from(U, V, W)) / np.linalg.norm(T)
    termM = term_columns(U, V, W)
    s_term = np.linalg.svd(termM, compute_uv=False)
    approx_norm = np.linalg.norm(termM @ np.ones(U.shape[1]))
    col_norms = np.linalg.norm(termM, axis=0)
    prod = np.linalg.norm(U, axis=0) * np.linalg.norm(V, axis=0) * np.linalg.norm(W, axis=0)
    top = sorted(
        [
            {
                "term": int(i),
                "product_norm": float(prod[i]),
                "column_norm": float(col_norms[i]),
                "projection_on_T_over_col_norm": float((termM[:, i] @ T.ravel()) / (max(col_norms[i], 1e-300) * np.linalg.norm(T))),
            }
            for i in range(U.shape[1])
        ],
        key=lambda d: -d["product_norm"],
    )[:8]
    # Small right singular vectors of term columns are cancellation relations among rank-one tensor terms.
    _, _, vh = np.linalg.svd(termM, full_matrices=False)
    small_relations = []
    for idx in range(1, min(4, vh.shape[0] + 1)):
        vec = vh[-idx]
        support = sorted([(int(i), float(vec[i])) for i in range(len(vec))], key=lambda x: -abs(x[1]))[:8]
        small_relations.append({
            "singular_value": float(s_term[-idx]),
            "top_coefficients": support,
            "sum_coefficients": float(np.sum(vec)),
        })
    return {
        "label": label,
        "state_file": str(path),
        "relative_residual_with_saved_W": float(rel),
        "best_W_inclusion_residual": float(incl),
        "X_rank_tol_1e-9": int(np.linalg.matrix_rank(X, tol=1e-9 * max(X.shape) * np.linalg.svd(X, compute_uv=False)[0])),
        "QX_rank_tol_1e-9": int(np.linalg.matrix_rank(QX, tol=1e-9 * max(QX.shape) * s_qx[0])),
        "QX_s10_to_s18": [float(x) for x in s_qx[9:18]],
        "QX_s13": float(s_qx[12]),
        "QX_s14": float(s_qx[13]),
        "QX_s15": float(s_qx[14]),
        "term_column_singular_values_tail8": [float(x) for x in s_term[-8:]],
        "term_column_condition": float(s_term[0] / max(s_term[-1], 1e-300)),
        "cancellation_ratio_norm_sum_over_sum_column_norms": float(approx_norm / max(np.sum(col_norms), 1e-300)),
        "sum_column_norms": float(np.sum(col_norms)),
        "approximation_norm": float(approx_norm),
        "target_norm": float(np.linalg.norm(T)),
        "top_terms_by_product_norm": top,
        "small_term_column_relations": small_relations,
    }


def main() -> None:
    ws = Path("research/research_record/workspace")
    indir = ws / "data/lm_diagnostics_main"
    outdir = ws / "data/lm_structure"
    outdir.mkdir(parents=True, exist_ok=True)
    T = make_T333()
    Q = sparse_t333_quotient()
    states = [
        ("cn122_rank23", None),
        ("after_ALS", indir / "state_after_ALS.npz"),
        ("LM_segment_1", indir / "state_segment_01.npz"),
        ("LM_segment_2", indir / "state_segment_02.npz"),
    ]
    result: Dict = {
        "description": "Structural quantities extracted from the stopped real LM path.",
        "rank22_projected_kernel_target": "full X rank 22 and rank(QX)=13; exact rank-22 also needs zero inclusion residual and exact Brent check",
        "records": [],
    }
    U23, V23, W23 = load_qmm(ws / "data/cn122_r23_reproduce/scheme.qmm")
    # analyze cn122 with 23 terms separately for scale comparison; QX target is 14 there.
    X23 = khatri_rao(U23, V23)
    QX23 = Q @ X23
    s23 = np.linalg.svd(QX23, compute_uv=False)
    termM23 = term_columns(U23, V23, W23)
    result["cn122_rank23_reference"] = {
        "terms": 23,
        "relative_residual": float(np.linalg.norm(T - tensor_from(U23, V23, W23)) / np.linalg.norm(T)),
        "QX_rank_tol_1e-9": int(np.linalg.matrix_rank(QX23, tol=1e-9 * max(QX23.shape) * s23[0])),
        "QX_s14": float(s23[13]),
        "QX_s15": float(s23[14]) if len(s23) > 14 else None,
        "sum_column_norms": float(np.sum(np.linalg.norm(termM23, axis=0))),
        "cancellation_ratio": float(np.linalg.norm(termM23 @ np.ones(23)) / np.sum(np.linalg.norm(termM23, axis=0))),
    }
    for label, path in states[1:]:
        if path.exists():
            rec = state_analysis(label, path, T, Q)
            result["records"].append(rec)
            print(
                f"{label}: rel={rec['relative_residual_with_saved_W']:.6e} incl={rec['best_W_inclusion_residual']:.6e} "
                f"rankQX={rec['QX_rank_tol_1e-9']} s14={rec['QX_s14']:.3e} "
                f"sumcols={rec['sum_column_norms']:.3e} cancel={rec['cancellation_ratio_norm_sum_over_sum_column_norms']:.3e}",
                flush=True,
            )
    # Compact trend ratios.
    if result["records"]:
        first = result["records"][0]
        last = result["records"][-1]
        result["trend_after_ALS_to_last"] = {
            "residual_ratio_last_over_first": float(last["relative_residual_with_saved_W"] / first["relative_residual_with_saved_W"]),
            "sum_column_norm_ratio_last_over_first": float(last["sum_column_norms"] / first["sum_column_norms"]),
            "QX_s14_ratio_last_over_first": float(last["QX_s14"] / first["QX_s14"]),
            "cancellation_ratio_last_over_first": float(last["cancellation_ratio_norm_sum_over_sum_column_norms"] / first["cancellation_ratio_norm_sum_over_sum_column_norms"]),
        }
    out = outdir / "lm_path_structure.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
