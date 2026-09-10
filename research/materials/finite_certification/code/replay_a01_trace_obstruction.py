#!/usr/bin/env python3
"""
analysis: independent related analysis replay of related analysis's E11-core trace linear obstruction.

related analysis analysis reported that the near-miss distinct E11-core A-support passes the
648 tensor linear equations but becomes linearly inconsistent after adding trace
equations tr(M(q)^-1 X_s)=1 from a single saturated rank-9 contraction q=49.
This script independently rebuilds the E11 core tensor and the labeled GF(2)
linear system using related analysis's reusable GF(2) utilities, but writes all replay output
inside research_record.

This is not a proof of the whole distinct branch; it only checks the specific
near-miss support and the cn122 positive control.
"""
from __future__ import annotations

import json, sys, time
from pathlib import Path
from typing import Sequence

A01_SCRIPTS = Path("scripts").resolve()
if str(A01_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(A01_SCRIPTS))

from fixed_A_saturation import (  # type: ignore
    build_matmul_tensor_f2,
    contraction_matrix,
    mat_rank_f2,
    gf2_linear_consistency,
    read_qmm_terms,
    restrict_terms_f2,
    verify_terms,
    vec_to_mask,
)
from dual_basis_instrument import gf2_mat_inv  # type: ignore

OUT_DIR = Path("data/a01_trace_replay")
OUT_DIR.mkdir(parents=True, exist_ok=True)
OUT_PATH = OUT_DIR / "near_miss_q49_replay.json"
A01_ROOT = Path("research/research_record")


def build_labeled_system(T_core, A_support: Sequence[int], trace_qs: Sequence[int] | None):
    na, nb, nc = T_core.shape
    nterms = len(A_support)
    nvars = nterms * nb * nc

    def var_idx(s, b, c):
        return s * (nb * nc) + b * nc + c

    rows_aug = []
    labels = []
    # Tensor identity rows.
    for a in range(na):
        for b in range(nb):
            for c in range(nc):
                row = 0
                for s, acol in enumerate(A_support):
                    if (acol >> a) & 1:
                        row ^= 1 << var_idx(s, b, c)
                row |= (int(T_core[a, b, c]) & 1) << nvars
                rows_aug.append(row)
                labels.append(("tensor", a, b, c))

    trace_meta = []
    if trace_qs is not None:
        for q in trace_qs:
            M = contraction_matrix(T_core, q)
            rk = mat_rank_f2(M)
            Minv = gf2_mat_inv(M) if rk == nb else None
            Iq = [s for s, acol in enumerate(A_support) if (acol & q).bit_count() & 1]
            trace_meta.append({"q": int(q), "rank": int(rk), "I_q_size": len(Iq), "I_q": Iq})
            if Minv is None or len(Iq) != rk:
                continue
            for s in Iq:
                row = 0
                for b in range(nb):
                    for c in range(nc):
                        if int(Minv[b, c]) & 1:
                            row ^= 1 << var_idx(s, b, c)
                row |= 1 << nvars
                rows_aug.append(row)
                labels.append(("trace", int(q), int(s)))
    return rows_aug, labels, nvars, trace_meta


def solve_and_cert(rows, labels, nvars):
    consistent, rank, cert = gf2_linear_consistency(rows, nvars)
    out = {"consistent": bool(consistent), "rank": int(rank), "equations": len(rows), "nvars": nvars}
    if cert is not None:
        used = [i for i in range(len(rows)) if (cert >> i) & 1]
        xor = 0
        for i in used:
            xor ^= rows[i]
        coeff_mask = (1 << nvars) - 1
        tensor = [labels[i] for i in used if labels[i][0] == "tensor"]
        trace = [labels[i] for i in used if labels[i][0] == "trace"]
        out["certificate"] = {
            "row_count": len(used),
            "tensor_rows": len(tensor),
            "trace_rows": len(trace),
            "trace_qs": sorted({int(x[1]) for x in trace}),
            "coefficients_zero": (xor & coeff_mask) == 0,
            "rhs_one": bool((xor >> nvars) & 1),
            "tensor_labels_head": [list(x) for x in tensor[:60]],
            "trace_labels": [list(x) for x in trace],
        }
    return out


def all_saturated_rank9_qs(T_core, A_support):
    na, nb, nc = T_core.shape
    qs = []
    for q in range(1, 1 << na):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) != 9:
            continue
        Iq = [s for s, acol in enumerate(A_support) if (acol & q).bit_count() & 1]
        if len(Iq) == 9:
            qs.append(q)
    return qs


def main():
    t0 = time.time()
    T_core = build_matmul_tensor_f2()[1:, :, :]
    near = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]

    # Tensor-only near-miss baseline.
    rows_tensor, labels_tensor, nvars, meta0 = build_labeled_system(T_core, near, trace_qs=[])
    near_tensor = solve_and_cert(rows_tensor, labels_tensor, nvars)

    # Single q=49 trace obstruction.
    rows_q49, labels_q49, nvars_q49, meta_q49 = build_labeled_system(T_core, near, trace_qs=[49])
    near_q49 = solve_and_cert(rows_q49, labels_q49, nvars_q49)

    # Full saturated trace set for near miss, to compare with related analysis.
    near_sat_qs = all_saturated_rank9_qs(T_core, near)
    rows_all, labels_all, nvars_all, meta_all = build_labeled_system(T_core, near, trace_qs=near_sat_qs)
    near_all = solve_and_cert(rows_all, labels_all, nvars_all)

    # cn122 E11-core positive control.
    qmm = A01_ROOT / "workspace/data/cn122_3x3_r23_repro/scheme.qmm"
    cn_terms = read_qmm_terms(qmm)
    cn_core_terms = restrict_terms_f2(cn_terms, 1)
    cn_A = [vec_to_mask(t["u"]) for t in cn_core_terms]
    cn_verified = verify_terms(T_core, cn_core_terms)
    cn_sat_qs = all_saturated_rank9_qs(T_core, cn_A)
    cn_rows, cn_labels, cn_nvars, cn_meta = build_labeled_system(T_core, cn_A, trace_qs=cn_sat_qs)
    cn_all = solve_and_cert(cn_rows, cn_labels, cn_nvars)

    record = {
        "schema": "a02_replay_a01_trace_obstruction_v1",
        "scope": "related analysis independent replay of related analysis analysis trace linear obstruction on one near-miss E11-core support; not a distinct-branch proof.",
        "field": "F2",
        "T_core_shape": list(T_core.shape),
        "near_miss_support": near,
        "near_miss_tensor_only": near_tensor,
        "near_miss_q49_meta": meta_q49,
        "near_miss_q49_with_trace": near_q49,
        "near_miss_all_saturated_rank9_qs": near_sat_qs,
        "near_miss_all_saturated_trace": near_all,
        "cn122_control": {
            "qmm_path": str(qmm),
            "core_terms": len(cn_core_terms),
            "verified_core_decomposition": bool(cn_verified),
            "saturated_rank9_qs": cn_sat_qs,
            "with_all_saturated_trace": cn_all,
        },
        "elapsed_sec": round(time.time() - t0, 3),
        "interpretation": "q=49 alone reproduces related analysis's compact contradiction for the near-miss support, while tensor-only is consistent and cn122 control remains consistent with its saturated trace equations. This validates the local trace mechanism but does not exclude all Wang-admissible distinct E11 supports.",
    }
    OUT_PATH.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({
        "out": str(OUT_PATH),
        "near_tensor_consistent": near_tensor["consistent"],
        "near_q49_consistent": near_q49["consistent"],
        "near_q49_cert": near_q49.get("certificate", {}),
        "near_all_sat_qs": near_sat_qs,
        "cn122_verified": cn_verified,
        "cn122_consistent": cn_all["consistent"],
        "cn122_sat_qs": cn_sat_qs,
    }, indent=2))


if __name__ == "__main__":
    main()
