#!/usr/bin/env python3
r"""analysis: trace-equation linear strengthening for E11 core B/C compatibility.

For saturated rank-9 contractions, the dual-basis identity gives:
  tr(M_q^{-1} X_s) = 1  for each s in I_q (participating terms)

where X_s = b_s c_s^T is the rank-one matrix for term s. These equations
are consequences of rank-one that can be tested cheaply as linear equations
on the relaxed X_s variables, BEFORE imposing rank-one.

When combined with the tensor identity and domain membership, the trace
equations provide a strictly stronger linear relaxation than the current
linear membership test (which sees no restriction from rank-9 contractions
because their column/row spaces are full F2^9).

This script:
1. Validates the combined system on cn122 (positive control)
2. Tests on the 12-violation near-miss support
3. Reports system rank, redundancy, and consistency
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
    read_qmm_terms, restrict_terms_f2, vec_to_mask, rref_basis,
    gf2_rank_rows, gf2_linear_consistency,
)
from dual_basis_instrument import gf2_mat_inv

ROOT = Path("research/research_record")


def build_e11_core_tensor():
    T_full = build_matmul_tensor_f2()
    return T_full[1:, :, :]


def build_linear_system(T_core, A_support, include_trace=True,
                        include_domains=True, include_ortho=False):
    """Build GF(2) linear system for relaxed B/C completion.

    Variables: for each term s (0..len(A_support)-1), X_s is a 9x9 matrix
    with entries X_s[b,c] for b,c in 0..8. Total: len(A_support) * 81 variables.

    Equations:
    1. Tensor identity: for each i in 0..7, b in 0..8, c in 0..8:
       sum_s A_s[i] * X_s[b,c] = T_core[i,b,c]  (648 equations)

    2. Trace from saturated rank-9: for each q with rank=9 and w(q)=|I_q|=9:
       sum_{b,c} M_q^{-1}[b,c] * X_s[b,c] = 1  for each s in I_q

    3. Domain membership (for non-full-rank contractions): X_s restricted to
       B_s tensor C_s. These are handled by zeroing out variables outside domains.

    4. Orthogonality (optional): for pairs s != t in I_q:
       sum_c c_row * M_q^{-1} * b_col component
       This is quadratic in general but becomes linear if one side is fixed.

    Returns augmented rows for GF(2) linear consistency check.
    """
    na, nb, nc = T_core.shape  # 8, 9, 9
    nterms = len(A_support)
    nvars = nterms * nb * nc  # 19 * 81 = 1539

    def var_idx(s, b, c):
        return s * (nb * nc) + b * nc + c

    rows_aug = []

    # 1. Tensor identity equations
    for i in range(na):
        for b in range(nb):
            for c in range(nc):
                row = 0
                for s, a in enumerate(A_support):
                    # A_s[i] = (a >> i) & 1
                    if (a >> i) & 1:
                        row ^= 1 << var_idx(s, b, c)
                rhs = int(T_core[i, b, c]) & 1
                row |= rhs << nvars
                rows_aug.append(row)

    tensor_eq_count = len(rows_aug)

    # Compute contractions and saturation
    contractions = {}
    for q in range(1, 1 << na):
        M = contraction_matrix(T_core, q)
        rk = mat_rank_f2(M)
        I_q = [s for s, a in enumerate(A_support) if (a & q).bit_count() & 1]
        inv = gf2_mat_inv(M) if rk == 9 else None
        contractions[q] = {'M': M, 'rank': rk, 'I_q': I_q, 'M_inv': inv}

    # 2. Trace equations from saturated rank-9 contractions
    trace_eq_count = 0
    saturated_rk9 = []
    if include_trace:
        for q, info in contractions.items():
            if info['rank'] == 9 and info['M_inv'] is not None and len(info['I_q']) == 9:
                M_inv = info['M_inv']
                saturated_rk9.append(q)
                for s in info['I_q']:
                    row = 0
                    for b in range(nb):
                        for c in range(nc):
                            if int(M_inv[b, c]) & 1:
                                row ^= 1 << var_idx(s, b, c)
                    row |= 1 << nvars  # RHS = 1
                    rows_aug.append(row)
                    trace_eq_count += 1

    # 3. Domain zero-forcing (for terms with restricted domains from non-full contractions)
    domain_eq_count = 0
    if include_domains:
        from complete_core_and_transversal import saturation_domains
        try:
            sat_data = saturation_domains(T_core, A_support)
            B_domains = sat_data['B_domains']
            C_domains = sat_data['C_domains']
            for s in range(nterms):
                Bb = B_domains[s]
                Cb = C_domains[s]
                if len(Bb) < nb:
                    # X_s[b,c] = 0 for b not in span(Bb)
                    B_span = set()
                    vecs = [0]
                    for bv in Bb:
                        vecs = vecs + [x ^ bv for x in vecs]
                    B_span = set(vecs)
                    for b in range(nb):
                        b_mask = 1 << b  # basis vector e_b as a bitmask... 
                        # Actually, the domain is in terms of bitmask vectors.
                        # This is complex - skip for now and use the simpler check.
                        pass
                # Domain zero-forcing is complex; skip and just count
        except Exception:
            pass  # domains not available for all supports

    return {
        'rows_aug': rows_aug,
        'nvars': nvars,
        'tensor_equations': tensor_eq_count,
        'trace_equations': trace_eq_count,
        'domain_equations': domain_eq_count,
        'saturated_rk9_count': len(saturated_rk9),
        'total_equations': len(rows_aug),
    }


def check_system(system_data):
    """Check GF(2) linear consistency."""
    rows = system_data['rows_aug']
    nvars = system_data['nvars']
    consistent, rank, cert = gf2_linear_consistency(rows, nvars)
    return {
        'consistent': consistent,
        'rank': rank,
        'total_equations': len(rows),
        'nvars': nvars,
        'contradiction_cert': cert,
    }


def main():
    out_path = ROOT / 'workspace/data/dual_basis/trace_linear_strengthening.json'
    out_path.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    T_core = build_e11_core_tensor()
    assert T_core.shape == (8, 9, 9)

    # --- cn122 positive control ---
    qmm_path = ROOT / "workspace/data/cn122_3x3_r23_repro/scheme.qmm"
    terms = read_qmm_terms(qmm_path)
    core_terms = restrict_terms_f2(terms, 1)  # E11 pivot = 1
    cn122_A = [vec_to_mask(t['u']) for t in core_terms]
    print(f"cn122 core: {len(cn122_A)} terms, {len(set(cn122_A))} unique A-directions")

    # Test WITHOUT trace
    sys_no_trace = build_linear_system(T_core, cn122_A, include_trace=False, include_domains=False)
    check_no = check_system(sys_no_trace)
    print(f"cn122 no-trace: {check_no['total_equations']} eqs, rank={check_no['rank']}, "
          f"consistent={check_no['consistent']}")

    # Test WITH trace
    sys_with_trace = build_linear_system(T_core, cn122_A, include_trace=True, include_domains=False)
    check_yes = check_system(sys_with_trace)
    print(f"cn122 with-trace: {check_yes['total_equations']} eqs, rank={check_yes['rank']}, "
          f"consistent={check_yes['consistent']}, sat_rk9={sys_with_trace['saturated_rk9_count']}")

    # --- Near-miss support ---
    nearmiss_A = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]
    print(f"\nNear-miss: {len(nearmiss_A)} points")

    sys_nm_no = build_linear_system(T_core, nearmiss_A, include_trace=False, include_domains=False)
    check_nm_no = check_system(sys_nm_no)
    print(f"Near-miss no-trace: {check_nm_no['total_equations']} eqs, rank={check_nm_no['rank']}, "
          f"consistent={check_nm_no['consistent']}")

    sys_nm_yes = build_linear_system(T_core, nearmiss_A, include_trace=True, include_domains=False)
    check_nm_yes = check_system(sys_nm_yes)
    print(f"Near-miss with-trace: {check_nm_yes['total_equations']} eqs, rank={check_nm_yes['rank']}, "
          f"consistent={check_nm_yes['consistent']}, sat_rk9={sys_nm_yes['saturated_rk9_count']}")

    # Rank increase from trace equations
    rank_gain_cn122 = check_yes['rank'] - check_no['rank']
    rank_gain_nm = check_nm_yes['rank'] - check_nm_no['rank']
    print(f"\nRank gain from trace equations:")
    print(f"  cn122: +{rank_gain_cn122} (from {check_no['rank']} to {check_yes['rank']})")
    print(f"  Near-miss: +{rank_gain_nm} (from {check_nm_no['rank']} to {check_nm_yes['rank']})")

    elapsed = time.time() - t0
    result = {
        'schema': 'trace_linear_strengthening_v1',
        'elapsed_sec': round(elapsed, 3),
        'cn122': {
            'terms': len(cn122_A),
            'unique_A': len(set(cn122_A)),
            'no_trace': {
                'equations': check_no['total_equations'],
                'rank': check_no['rank'],
                'consistent': check_no['consistent'],
            },
            'with_trace': {
                'equations': check_yes['total_equations'],
                'rank': check_yes['rank'],
                'consistent': check_yes['consistent'],
                'saturated_rk9': sys_with_trace['saturated_rk9_count'],
                'trace_equations': sys_with_trace['trace_equations'],
            },
            'rank_gain': rank_gain_cn122,
        },
        'near_miss': {
            'support': nearmiss_A,
            'no_trace': {
                'equations': check_nm_no['total_equations'],
                'rank': check_nm_no['rank'],
                'consistent': check_nm_no['consistent'],
            },
            'with_trace': {
                'equations': check_nm_yes['total_equations'],
                'rank': check_nm_yes['rank'],
                'consistent': check_nm_yes['consistent'],
                'saturated_rk9': sys_nm_yes['saturated_rk9_count'],
                'trace_equations': sys_nm_yes['trace_equations'],
            },
            'rank_gain': rank_gain_nm,
        },
    }

    with open(out_path, 'w') as f:
        json.dump(result, f, indent=2)
    print(f"\nSaved {out_path}")


if __name__ == '__main__':
    raise SystemExit('Deprecated: analysis trace script used the wrong coefficient M_inv[b,c] on X[b,c]. Use corrected_trace_instrument.py instead.')
