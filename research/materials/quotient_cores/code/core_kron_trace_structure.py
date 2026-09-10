#!/usr/bin/env python3
r"""analysis: exact Kronecker/block structure of E11 core contractions and trace rows.

For the matrix multiplication tensor, an A-contraction by a 3x3 matrix Q should
produce L(Q)=Q^T \otimes I_3 in the current row-major conventions.  This script
checks that for all 255 nonzero E11-core functionals (Q_11=0), and verifies the
corrected trace functional as the transpose of L(Q)^{-1}.  It records the
low-dimensional representation of corrected trace rows by Q^{-T} (equivalently
Q^{-1} depending on row/column typing) so later work can reason without 81-entry
matrices.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import List

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2  # noqa: E402
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from corrected_trace_instrument import trace_functional_correct  # noqa: E402
from trace_compressed_support import matrix_mask, trace_mask_correct  # noqa: E402

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/corrected_trace"


def q_to_Q(q: int) -> np.ndarray:
    bits = [0] + [(int(q) >> i) & 1 for i in range(8)]
    return np.array([[bits[3 * r + c] for c in range(3)] for r in range(3)], dtype=np.uint8)


def mat3_to_core_mask(M: np.ndarray) -> int:
    bits = [int(M[r, c]) & 1 for r in range(3) for c in range(3)]
    mask = 0
    for full_idx in range(1, 9):
        if bits[full_idx]:
            mask |= 1 << (full_idx - 1)
    return mask


def mat3_to_full_bits(M: np.ndarray) -> List[int]:
    return [int(M[r, c]) & 1 for r in range(3) for c in range(3)]


def gf2_rank3(M: np.ndarray) -> int:
    rows = []
    for i in range(3):
        row = 0
        for j in range(3):
            if int(M[i, j]) & 1:
                row |= 1 << j
        rows.append(row)
    basis = [0, 0, 0]
    for row in rows:
        v = row
        while v:
            p = v.bit_length() - 1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p] = v
                break
    return sum(1 for x in basis if x)


def main() -> None:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    T_core = build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2
    I3 = np.eye(3, dtype=np.uint8)
    mismatch = []
    rank_mismatch = []
    trace_mask_mismatch = []
    g_mismatch = []
    rank_hist = Counter()
    q_rank_hist = Counter()
    inv_records = []
    trace_masks = []
    g_masks = []
    for q in range(1, 256):
        Q = q_to_Q(q)
        M = contraction_matrix(T_core, q)
        expected = np.kron(Q.T, I3).astype(np.uint8) % 2
        if not np.array_equal(M, expected):
            mismatch.append(q)
        rkM = mat_rank_f2(M)
        rkQ = gf2_rank3(Q)
        rank_hist[int(rkM)] += 1
        q_rank_hist[int(rkQ)] += 1
        if rkM != 3 * rkQ:
            rank_mismatch.append({"q": q, "rank_Lq": int(rkM), "rank_Q": int(rkQ)})
        if rkM == 9:
            Minv = gf2_mat_inv(M)
            Qinv = gf2_mat_inv(Q)
            assert Minv is not None and Qinv is not None
            expected_inv = np.kron(Qinv.T, I3).astype(np.uint8) % 2
            if not np.array_equal(Minv, expected_inv):
                trace_mask_mismatch.append({"q": q, "issue": "Minv not kron(Qinv.T,I)"})
            # The coefficient matrix for X[b,c] is Minv^T.  In block terms this is Qinv \otimes I.
            coeff_expected = expected_inv.T
            mask = trace_mask_correct(Minv)
            coeff_mask_expected = matrix_mask(coeff_expected)
            if mask != coeff_mask_expected:
                trace_mask_mismatch.append({"q": q, "issue": "trace mask not transpose of inverse"})
            # g_i = phi_q(T_i) should be the core mask of Q^{-T}; verify directly.
            g = 0
            for i in range(8):
                if trace_functional_correct(Minv, T_core[i]):
                    g |= 1 << i
            expected_g = mat3_to_core_mask(Qinv.T)
            if g != expected_g:
                g_mismatch.append({"q": q, "g": g, "expected_QinvT_core_mask": expected_g, "Q_full": mat3_to_full_bits(Q), "Qinv_full": mat3_to_full_bits(Qinv)})
            trace_masks.append(mask)
            g_masks.append(g)
            if len(inv_records) < 12:
                inv_records.append({
                    "q": q,
                    "q_hex": hex(q),
                    "Q_full_bits": mat3_to_full_bits(Q),
                    "Qinv_full_bits": mat3_to_full_bits(Qinv),
                    "g_mask": g,
                    "QinvT_core_mask": expected_g,
                })
    # rank of all trace masks / g masks via row-rank helper on bitmasks
    from fixed_A_saturation import gf2_rank_rows  # local import
    result = {
        "schema": "core_kron_trace_structure_v1",
        "field": "F2",
        "checked_nonzero_core_functionals": 255,
        "contraction_equals_QT_kron_I_failures": mismatch,
        "rank_Lq_equals_3_rank_Q_failures": rank_mismatch,
        "rank_Lq_histogram": {str(k): v for k, v in sorted(rank_hist.items())},
        "rank_Q_histogram": {str(k): v for k, v in sorted(q_rank_hist.items())},
        "invertible_Q_count": len(trace_masks),
        "trace_inverse_structure_failures": trace_mask_mismatch,
        "g_q_equals_QinvT_core_mask_failures": g_mismatch,
        "rank_of_all_invertible_trace_functionals_as_81_masks": gf2_rank_rows(trace_masks, 81),
        "rank_of_all_g_q_core_masks": gf2_rank_rows(g_masks, 8),
        "sample_invertible_records": inv_records,
        "interpretation": "All E11 core contractions have L(q)=Q^T kron I3. For rank-9 q, corrected trace rows are represented by (Q^{-1} kron I3) as the coefficient matrix on X[b,c], and g_q is the core mask of Q^{-T}.",
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = OUTDIR / "core_kron_trace_structure.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "elapsed_sec": result["elapsed_sec"],
        "kron_failures": len(mismatch),
        "rank_failures": len(rank_mismatch),
        "trace_structure_failures": len(trace_mask_mismatch),
        "g_failures": len(g_mismatch),
        "rank_trace_masks": result["rank_of_all_invertible_trace_functionals_as_81_masks"],
        "rank_g_masks": result["rank_of_all_g_q_core_masks"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
