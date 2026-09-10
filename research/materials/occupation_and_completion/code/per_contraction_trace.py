#!/usr/bin/env python3
"""analysis: check trace contradiction for each saturated rank-9 contraction individually."""
import json, sys, time
import numpy as np
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    build_matmul_tensor_f2, contraction_matrix, mat_rank_f2,
    gf2_linear_consistency,
)
from dual_basis_instrument import gf2_mat_inv

ROOT = Path("research/research_record")


def build_labeled_rows(T_core, A_support, q_target):
    """Build tensor identity + trace equations for a single contraction q."""
    na, nb, nc = T_core.shape
    nterms = len(A_support)
    nvars = nterms * nb * nc
    def var_idx(s, b, c):
        return s * (nb * nc) + b * nc + c

    rows_aug = []
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

    # Trace equations for q_target
    M = contraction_matrix(T_core, q_target)
    M_inv = gf2_mat_inv(M)
    I_q = [s for s, a in enumerate(A_support) if (a & q_target).bit_count() & 1]
    trace_count = 0
    if M_inv is not None and len(I_q) == 9:
        for s in I_q:
            row = 0
            for b in range(nb):
                for c in range(nc):
                    if int(M_inv[b, c]) & 1:
                        row ^= 1 << var_idx(s, b, c)
            row |= 1 << nvars
            rows_aug.append(row)
            trace_count += 1

    return rows_aug, nvars, len(I_q), trace_count


def main():
    out_path = ROOT / 'workspace/data/dual_basis/per_contraction_trace_test.json'
    out_path.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    T_core = build_matmul_tensor_f2()[1:, :, :]
    na = 8

    support = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]

    # Find all saturated rank-9 contractions for this support
    sat_rk9 = []
    for q in range(1, 256):
        M = contraction_matrix(T_core, q)
        rk = mat_rank_f2(M)
        I_q = [s for s, a in enumerate(support) if (a & q).bit_count() & 1]
        if rk == 9 and len(I_q) == 9:
            sat_rk9.append(q)

    print(f"Saturated rank-9 contractions: {len(sat_rk9)}")

    results_per_q = []
    inconsistent_count = 0
    for q in sat_rk9:
        rows, nvars, iq_size, trace_count = build_labeled_rows(T_core, support, q)
        consistent, rank, cert = gf2_linear_consistency(rows, nvars)
        cert_size = bin(cert).count('1') if cert is not None else 0
        results_per_q.append({
            'q': q,
            'q_hex': hex(q),
            'q_bin': bin(q),
            'I_q_size': iq_size,
            'trace_eqs': trace_count,
            'total_eqs': len(rows),
            'rank': rank,
            'consistent': consistent,
            'cert_size': cert_size,
        })
        if not consistent:
            inconsistent_count += 1
            print(f"  q={q:3d} ({hex(q):5s}): INCONSISTENT (cert size {cert_size})")
        else:
            print(f"  q={q:3d} ({hex(q):5s}): consistent (rank {rank})")

    print(f"\nInconsistent: {inconsistent_count}/{len(sat_rk9)}")

    result = {
        'schema': 'per_contraction_trace_v1',
        'support': support,
        'saturated_rk9': len(sat_rk9),
        'inconsistent': inconsistent_count,
        'consistent': len(sat_rk9) - inconsistent_count,
        'details': results_per_q,
        'elapsed_sec': round(time.time() - t0, 3),
    }
    with open(out_path, 'w') as f:
        json.dump(result, f, indent=2)
    print(f"Saved {out_path}")


if __name__ == '__main__':
    raise SystemExit('Deprecated: analysis per-contraction trace rows used the wrong coefficient M_inv[b,c] on X[b,c]. Use corrected_trace_instrument.py and corrected_trace_certificate.py instead.')
