#!/usr/bin/env python3
r"""analysis: verify trace inconsistency and extract GF(2) contradiction certificate.

The analysis trace_linear_system found that the near-miss support is
linearly inconsistent when trace equations from saturated rank-9
contractions are added to the tensor identity. This script:

1. Extracts the contradiction certificate (dual witness)
2. Verifies it is a valid linear combination
3. Tests other candidate supports for the same inconsistency
4. Determines whether trace alone (without Wang) gives the contradiction
"""
from __future__ import annotations

import json, sys, time
import numpy as np
from collections import Counter
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    build_matmul_tensor_f2, contraction_matrix, mat_rank_f2,
    read_qmm_terms, restrict_terms_f2, vec_to_mask,
    gf2_linear_consistency,
)
from dual_basis_instrument import gf2_mat_inv

ROOT = Path("research/research_record")


def build_e11_core_tensor():
    return build_matmul_tensor_f2()[1:, :, :]


def build_labeled_system(T_core, A_support, include_trace=True):
    """Build the linear system with labeled rows for certificate extraction."""
    na, nb, nc = T_core.shape
    nterms = len(A_support)
    nvars = nterms * nb * nc

    def var_idx(s, b, c):
        return s * (nb * nc) + b * nc + c

    rows_aug = []
    row_labels = []

    # Tensor identity
    for i in range(na):
        for b in range(nb):
            for c in range(nc):
                row = 0
                for s, a in enumerate(A_support):
                    if (a >> i) & 1:
                        row ^= 1 << var_idx(s, b, c)
                rhs = int(T_core[i, b, c]) & 1
                row |= rhs << nvars
                rows_aug.append(row)
                row_labels.append(('tensor', i, b, c))

    # Trace equations
    trace_info = []
    if include_trace:
        for q in range(1, 1 << na):
            M = contraction_matrix(T_core, q)
            rk = mat_rank_f2(M)
            if rk != 9:
                continue
            M_inv = gf2_mat_inv(M)
            if M_inv is None:
                continue
            I_q = [s for s, a in enumerate(A_support) if (a & q).bit_count() & 1]
            if len(I_q) != 9:
                continue
            for s in I_q:
                row = 0
                for b in range(nb):
                    for c in range(nc):
                        if int(M_inv[b, c]) & 1:
                            row ^= 1 << var_idx(s, b, c)
                row |= 1 << nvars  # RHS = 1
                rows_aug.append(row)
                row_labels.append(('trace', q, s))
                trace_info.append({'q': q, 's': s, 'I_q': I_q})

    return rows_aug, row_labels, nvars, trace_info


def main():
    out_path = ROOT / 'workspace/data/dual_basis/trace_contradiction_certificate.json'
    out_path.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    T_core = build_e11_core_tensor()
    na, nb, nc = T_core.shape

    results = {}

    # --- Near-miss support ---
    nearmiss_A = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]

    # Full system (tensor + trace)
    rows, labels, nvars, trace_info = build_labeled_system(T_core, nearmiss_A, include_trace=True)
    consistent, rank, cert = gf2_linear_consistency(rows, nvars)
    print(f"Near-miss full: consistent={consistent}, rank={rank}, eqs={len(rows)}")

    if not consistent and cert is not None:
        # Extract the contradiction
        cert_rows = []
        tensor_rows_used = 0
        trace_rows_used = 0
        trace_qs_used = set()
        for idx in range(len(rows)):
            if (cert >> idx) & 1:
                lbl = labels[idx]
                cert_rows.append(lbl)
                if lbl[0] == 'tensor':
                    tensor_rows_used += 1
                elif lbl[0] == 'trace':
                    trace_rows_used += 1
                    trace_qs_used.add(lbl[1])

        # Verify: XOR of the certificate rows should have all-zero coefficients, RHS=1
        xor = 0
        for idx in range(len(rows)):
            if (cert >> idx) & 1:
                xor ^= rows[idx]
        coeff_mask = (1 << nvars) - 1
        coeff_zero = (xor & coeff_mask) == 0
        rhs_one = (xor >> nvars) & 1

        print(f"\nContradiction certificate:")
        print(f"  Total rows in certificate: {tensor_rows_used + trace_rows_used}")
        print(f"  Tensor identity rows: {tensor_rows_used}")
        print(f"  Trace equation rows: {trace_rows_used}")
        print(f"  Distinct saturated rank-9 contractions used: {len(trace_qs_used)}")
        print(f"  Contractions: {sorted(trace_qs_used)}")
        print(f"  Verification: coefficients all zero = {coeff_zero}, RHS = {rhs_one}")
        print(f"  Valid contradiction: {coeff_zero and rhs_one == 1}")

        results['near_miss_contradiction'] = {
            'consistent': False,
            'certificate_size': tensor_rows_used + trace_rows_used,
            'tensor_rows': tensor_rows_used,
            'trace_rows': trace_rows_used,
            'trace_contractions': sorted(trace_qs_used),
            'trace_contractions_count': len(trace_qs_used),
            'verification': {
                'coefficients_zero': coeff_zero,
                'rhs_one': bool(rhs_one),
                'valid': coeff_zero and rhs_one == 1,
            },
        }

    # --- Test WITHOUT trace (should be consistent) ---
    rows_no, labels_no, _, _ = build_labeled_system(T_core, nearmiss_A, include_trace=False)
    con_no, rank_no, _ = gf2_linear_consistency(rows_no, nvars)
    print(f"\nNear-miss tensor-only: consistent={con_no}, rank={rank_no}")
    results['near_miss_tensor_only'] = {'consistent': con_no, 'rank': rank_no}

    # --- Other candidate supports ---
    # analysis 15-violation support
    s46_support = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]
    # Actually let me load the analysis round-12 support
    # Use a few varied supports from the completion batch
    other_supports = {}
    try:
        with open(ROOT / 'workspace/data/completion/distinct_candidate_completion_repaired.json') as f:
            batch = json.load(f)
        for rec in batch.get('best_analyses', [])[:5]:
            key = str(rec['A_cols'][:5])
            other_supports[key] = rec['A_cols']
    except Exception as e:
        print(f"Could not load batch: {e}")

    for name, support in other_supports.items():
        rows_s, labels_s, nvars_s, _ = build_labeled_system(T_core, support, include_trace=True)
        con_s, rank_s, cert_s = gf2_linear_consistency(rows_s, nvars_s)
        # Count saturated rank-9
        n_sat = sum(1 for l in labels_s if l[0] == 'trace') // 9 if any(l[0]=='trace' for l in labels_s) else 0
        print(f"Support {name}: consistent={con_s}, rank={rank_s}, total_eqs={len(rows_s)}")
        results[f'other_{name}'] = {'consistent': con_s, 'rank': rank_s, 'support_head': support[:5]}

    elapsed = time.time() - t0
    results['elapsed_sec'] = round(elapsed, 3)
    results['schema'] = 'trace_contradiction_v1'

    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nSaved {out_path}")


if __name__ == '__main__':
    raise SystemExit('Deprecated: analysis trace certificate used the wrong coefficient M_inv[b,c] on X[b,c]. Use corrected_trace_certificate.py instead.')
