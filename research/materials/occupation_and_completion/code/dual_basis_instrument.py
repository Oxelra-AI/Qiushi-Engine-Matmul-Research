#!/usr/bin/env python3
r"""analysis: dual-basis algebraic instrument for saturated nonsingular contractions.

For an invertible F2 contraction matrix M = L(q) with exactly 9 participating
terms (saturated), the decomposition M = sum_{s in I} b_s c_s^T forces:

  c_s^T M^{-1} b_s = 1            (trace identity)
  c_s^T M^{-1} b_t = 0            (orthogonality, s != t)

i.e., C^T M^{-1} B = I over F2 where B = [b_s], C = [c_s].

Domain intersection gives full F2^9 for rank-9 contractions (no restriction).
These identities are additional necessary conditions that domain tests miss.

For two overlapping rank-9 contractions q1, q2 with matrices M1, M2 and
common participating terms, the combined constraint:

  c_s^T (M1^{-1} + M2^{-1}) b_t = 0  for s, t in I_{q1} cap I_{q2}

gives a rank condition on N = M1^{-1} + M2^{-1} that constrains how many
independent common B-factors (or C-factors) can exist.

This script:
1. Builds the E11 core tensor and all 255 contraction matrices
2. Computes M^{-1} for all rank-9 contractions (over F2)
3. Validates the dual-basis identity on the cn122 positive control
4. Analyzes overlap structure of rank-9 contraction pairs
5. Focuses on the six violating dual lines from analysis
"""
from __future__ import annotations

import argparse
import json
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

import numpy as np

import sys
SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    build_matmul_tensor_f2,
    contraction_matrix,
    mat_rank_f2,
    read_qmm_terms,
    restrict_terms_f2,
    vec_to_mask,
    verify_terms,
)

ROOT = Path("research/research_record")


# ---------------------------------------------------------------------------
# GF(2) 9×9 matrix algebra
# ---------------------------------------------------------------------------

def mat_to_bits(M: np.ndarray) -> List[int]:
    """Convert np matrix to list of row bitmasks."""
    m, n = M.shape
    rows = []
    for i in range(m):
        x = 0
        for j in range(n):
            if int(M[i, j]) & 1:
                x |= 1 << j
        rows.append(x)
    return rows


def bits_to_mat(rows: List[int], m: int, n: int) -> np.ndarray:
    M = np.zeros((m, n), dtype=np.uint8)
    for i, r in enumerate(rows):
        for j in range(n):
            if (r >> j) & 1:
                M[i, j] = 1
    return M


def gf2_mat_inv(M: np.ndarray) -> Optional[np.ndarray]:
    """Compute M^{-1} over GF(2). Returns None if not invertible."""
    n = M.shape[0]
    assert M.shape == (n, n)
    # Augmented system [M | I]
    aug = []
    for i in range(n):
        row = 0
        for j in range(n):
            if int(M[i, j]) & 1:
                row |= 1 << j
        row |= 1 << (n + i)  # identity part
        aug.append(row)

    # Forward elimination
    for col in range(n):
        # Find pivot
        pivot = None
        for r in range(col, n):
            if (aug[r] >> col) & 1:
                pivot = r
                break
        if pivot is None:
            return None
        aug[col], aug[pivot] = aug[pivot], aug[col]
        for r in range(n):
            if r != col and (aug[r] >> col) & 1:
                aug[r] ^= aug[col]

    # Extract inverse from augmented part
    inv = np.zeros((n, n), dtype=np.uint8)
    for i in range(n):
        for j in range(n):
            if (aug[i] >> (n + j)) & 1:
                inv[i, j] = 1
    return inv


def gf2_mat_mul(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    """Matrix multiply over GF(2)."""
    m, k1 = A.shape
    k2, n = B.shape
    assert k1 == k2
    C = np.zeros((m, n), dtype=np.uint8)
    for i in range(m):
        for j in range(n):
            s = 0
            for l in range(k1):
                s ^= int(A[i, l]) & int(B[l, j])
            C[i, j] = s
    return C


def gf2_trace(M: np.ndarray) -> int:
    """Trace of square matrix over GF(2)."""
    n = M.shape[0]
    s = 0
    for i in range(n):
        s ^= int(M[i, i])
    return s & 1


def gf2_rank(M: np.ndarray) -> int:
    return mat_rank_f2(M)


# ---------------------------------------------------------------------------
# Core tensor and contractions
# ---------------------------------------------------------------------------

def build_e11_core_tensor() -> np.ndarray:
    """Build the E11 codimension-one core tensor (8 x 9 x 9) over F2."""
    T_full = build_matmul_tensor_f2()  # 9 x 9 x 9
    # E11 = A-coordinate 0 (index 0 in 0-based). The core removes coordinate 0.
    # For each A-coordinate a (1..8), the core maps to a-1 in 0..7.
    # But we also need to XOR-eliminate the E11 coordinate from each slice.
    # Standard: restrict_terms_f2 removes a pivot coordinate from terms.
    # The core tensor T_core[a, b, c] = T_full[a+1, b, c] XOR ... no.
    # Actually, the core tensor is built by the CoreQuotient infrastructure.
    # Direct construction: delete the A-coordinate corresponding to E11 (index 0).
    # The remaining tensor is T_full[1:, :, :] but that's the affine restriction,
    # not the projective quotient.
    #
    # Correct: the E11 core quotient T' satisfies T'_a = T_{a+1} + a_0 * T_0
    # where a_0 is the bit being removed. For the projective quotient:
    # T_core[a][b][c] for a in 0..7 = T_full[a+1][b][c] (the slices with a_0=0)
    # because we quotient by E11, meaning we set the E11 coordinate to zero.
    #
    # No wait - the core tensor is the restriction of T to the hyperplane {a: e_0(a)=0},
    # followed by deleting the trivially-zero coordinate.
    # For T_<3,3,3> with A-basis e_0,...,e_8: the hyperplane e_0=0 keeps slices 1..8.
    # After dropping coordinate 0, the core is just T_full[1:9, :, :].
    # But that's not quite right for the quotient...
    #
    # Actually, reading the CoreQuotient code: the quotient removes the pivot coordinate
    # and XOR-eliminates it from all terms. For E11 at position 0:
    # - Terms with a_0 = 1 get their remaining a-coordinates XORed by the pivot row
    # - Then coordinate 0 is dropped
    # This is the affine change of basis, not just deletion.
    #
    # Let me use the same method as restrict_terms_f2 but on the tensor directly.

    # E11 is the first A-basis vector (index 0).
    pivot = 0
    na, nb, nc = T_full.shape  # 9, 9, 9
    core_na = na - 1  # 8
    T_core = np.zeros((core_na, nb, nc), dtype=np.uint8)
    for a in range(na):
        if a == pivot:
            continue
        core_a = a - 1 if a > pivot else a
        T_core[core_a] = T_full[a]  # the a-th slice maps to core coordinate
    # Now XOR-eliminate: for each core coord that originally had e_0 mixed in:
    # Actually in the standard encoding, E11 is the first basis vector, so
    # T_full[0,:,:] is the slice for a=e_0. The remaining slices T_full[1:,:,:]
    # already have a_0=0 in the standard basis. No XOR needed.
    # The quotient core is simply T_full[1:, :, :].

    # Verify: the core should be 8x9x9
    assert T_core.shape == (8, 9, 9)
    return T_core


def compute_all_contractions(T_core: np.ndarray):
    """Compute all 255 nonzero contractions and their properties."""
    na = T_core.shape[0]  # 8
    results = {}
    for q in range(1, 1 << na):
        M = contraction_matrix(T_core, q)
        rk = gf2_rank(M)
        inv = gf2_mat_inv(M) if rk == 9 else None
        results[q] = {
            'M': M,
            'rank': rk,
            'invertible': inv is not None,
            'M_inv': inv,
        }
    return results


# ---------------------------------------------------------------------------
# Dual-basis validation on cn122
# ---------------------------------------------------------------------------

def load_cn122_core_terms():
    """Load cn122 rank-23 decomposition and restrict to E11 core."""
    qmm_path = ROOT / "workspace/data/cn122_3x3_r23_repro/scheme.qmm"
    terms = read_qmm_terms(qmm_path)
    # E11 is the matrix with 1 at position (0,0), i.e., u=[1,0,0,0,0,0,0,0,0]
    # In the qmm format, u is the A-vector. E11 = mask with bit 0 set = 1.
    pivot_mask = 1  # E11
    core_terms = restrict_terms_f2(terms, pivot_mask)
    return core_terms


def validate_dual_basis_on_terms(T_core, contractions, core_terms):
    """Check tr(M^{-1} X_s) = 1 and orthogonality for cn122 core terms."""
    na, nb, nc = T_core.shape
    # Extract B, C vectors from terms
    B_vecs = []  # b_s as column bitmasks
    C_vecs = []  # c_s as column bitmasks
    A_cols = []
    for t in core_terms:
        a = vec_to_mask(t['u'])
        b = vec_to_mask(t['v'])
        c = vec_to_mask(t['w'])
        A_cols.append(a)
        B_vecs.append(b)
        C_vecs.append(c)

    nterms = len(core_terms)
    trace_pass = 0
    trace_fail = 0
    ortho_pass = 0
    ortho_fail = 0
    invertible_sat_count = 0
    invertible_sat_details = []

    for q, info in contractions.items():
        if not info['invertible']:
            continue
        M_inv = info['M_inv']
        # Participating terms
        I_q = [s for s in range(nterms) if (A_cols[s] & q).bit_count() & 1]
        if len(I_q) != 9:
            continue  # not saturated at 9
        invertible_sat_count += 1

        # Check trace: c_s^T M^{-1} b_s for each s in I_q
        q_trace_ok = True
        q_ortho_ok = True
        for idx_s, s in enumerate(I_q):
            # c_s^T M^{-1} b_s
            b_s_vec = np.array([(B_vecs[s] >> j) & 1 for j in range(nb)], dtype=np.uint8)
            c_s_vec = np.array([(C_vecs[s] >> j) & 1 for j in range(nc)], dtype=np.uint8)
            Minv_b = gf2_mat_mul(M_inv, b_s_vec.reshape(-1, 1)).flatten()
            val = sum(int(c_s_vec[j]) & int(Minv_b[j]) for j in range(nc)) & 1
            if val == 1:
                trace_pass += 1
            else:
                trace_fail += 1
                q_trace_ok = False

            # Orthogonality: c_s^T M^{-1} b_t for t != s in I_q
            for idx_t, t in enumerate(I_q):
                if t == s:
                    continue
                b_t_vec = np.array([(B_vecs[t] >> j) & 1 for j in range(nb)], dtype=np.uint8)
                Minv_bt = gf2_mat_mul(M_inv, b_t_vec.reshape(-1, 1)).flatten()
                val_ot = sum(int(c_s_vec[j]) & int(Minv_bt[j]) for j in range(nc)) & 1
                if val_ot == 0:
                    ortho_pass += 1
                else:
                    ortho_fail += 1
                    q_ortho_ok = False

        invertible_sat_details.append({
            'q': q, 'q_hex': hex(q), 'I_count': len(I_q),
            'trace_ok': q_trace_ok, 'ortho_ok': q_ortho_ok,
        })

    return {
        'invertible_saturated_contractions': invertible_sat_count,
        'trace_tests': {'pass': trace_pass, 'fail': trace_fail},
        'orthogonality_tests': {'pass': ortho_pass, 'fail': ortho_fail},
        'all_pass': trace_fail == 0 and ortho_fail == 0,
        'details_sample': invertible_sat_details[:10],
    }


# ---------------------------------------------------------------------------
# Pair analysis: N = M1^{-1} + M2^{-1} for overlapping rank-9 contractions
# ---------------------------------------------------------------------------

def analyze_rank9_pairs(contractions, violating_lines):
    """For violating dual lines, analyze N = M1^{-1} + M2^{-1}."""
    results = []
    for line_info in violating_lines:
        D_nonzero = line_info['D_nonzero']
        # Identify the rank-9 and rank-3 contractions
        rk9 = [q for q in D_nonzero if contractions[q]['rank'] == 9]
        rk3 = [q for q in D_nonzero if contractions[q]['rank'] == 3]
        if len(rk9) != 2 or len(rk3) != 1:
            results.append({'error': 'unexpected rank pattern', 'D_nonzero': D_nonzero})
            continue

        q1, q2 = rk9
        q3 = rk3[0]
        M1_inv = contractions[q1]['M_inv']
        M2_inv = contractions[q2]['M_inv']
        N = (M1_inv + M2_inv) % 2
        N_rank = gf2_rank(N)

        # Also compute M1^{-1} M2 and its structure
        M2 = contractions[q2]['M']
        MinvM = gf2_mat_mul(M1_inv, M2)
        MinvM_rank = gf2_rank(MinvM)
        # (M1^{-1} M2 + I) gives the "difference" in the dual-basis sense
        diff = (MinvM + np.eye(9, dtype=np.uint8)) % 2
        diff_rank = gf2_rank(diff)

        results.append({
            'D_nonzero': D_nonzero,
            'D_basis': line_info.get('D_basis', []),
            'rk9_contractions': rk9,
            'rk3_contraction': q3,
            'N_rank': int(N_rank),
            'MinvM_rank': int(MinvM_rank),
            'MinvM_plus_I_rank': int(diff_rank),
            'N_interpretation': (
                f'N = M1^-1 + M2^-1 has rank {N_rank}. '
                f'Common terms (7 expected) must have c_s^T N b_t = 0 for all s,t. '
                f'If rank(N) = r, then b_t must lie in a (9-r)-dim subspace of '
                f'right null(row of N), constraining common B-factors.'
            ),
        })
    return results


# ---------------------------------------------------------------------------
# Systematic rank-9 pair overlap analysis
# ---------------------------------------------------------------------------

def systematic_pair_analysis(contractions, T_core):
    """Analyze all pairs of rank-9 contractions for N-rank distribution."""
    na = T_core.shape[0]
    rk9_qs = sorted(q for q, info in contractions.items() if info['rank'] == 9)
    N_rank_hist = Counter()
    high_rank_pairs = []
    n_pairs = 0

    for i, q1 in enumerate(rk9_qs):
        for q2 in rk9_qs[i+1:]:
            M1_inv = contractions[q1]['M_inv']
            M2_inv = contractions[q2]['M_inv']
            N = (M1_inv + M2_inv) % 2
            N_rank = gf2_rank(N)
            N_rank_hist[N_rank] += 1
            n_pairs += 1
            if N_rank >= 7:
                high_rank_pairs.append({
                    'q1': q1, 'q2': q2,
                    'N_rank': int(N_rank),
                    'q1q2_xor': q1 ^ q2,
                    'xor_rank': contractions.get(q1 ^ q2, {}).get('rank', None),
                })

    return {
        'total_rank9': len(rk9_qs),
        'total_pairs': n_pairs,
        'N_rank_histogram': {str(k): v for k, v in sorted(N_rank_hist.items())},
        'high_rank_pairs_count': len(high_rank_pairs),
        'high_rank_pairs_sample': high_rank_pairs[:20],
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path,
                        default=ROOT / 'workspace/data/dual_basis/analysis.json')
    args = parser.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()

    # 1. Build core tensor
    T_core = build_e11_core_tensor()
    assert T_core.shape == (8, 9, 9)

    # Verify the core tensor matches what we expect
    T_full = build_matmul_tensor_f2()
    assert np.array_equal(T_core, T_full[1:, :, :]), "Core should be T_full without first A-slice"

    # 2. Compute all contractions
    contractions = compute_all_contractions(T_core)
    rank_hist = Counter(info['rank'] for info in contractions.values())
    inv_count = sum(1 for info in contractions.values() if info['invertible'])
    print(f"Contractions: {len(contractions)}, rank histogram: {dict(sorted(rank_hist.items()))}")
    print(f"Invertible (rank 9): {inv_count}")

    # 3. Validate dual-basis on cn122
    core_terms = load_cn122_core_terms()
    print(f"cn122 core terms: {len(core_terms)}")
    cn122_validation = validate_dual_basis_on_terms(T_core, contractions, core_terms)
    print(f"cn122 dual-basis: trace pass={cn122_validation['trace_tests']['pass']}, "
          f"fail={cn122_validation['trace_tests']['fail']}")
    print(f"cn122 dual-basis: ortho pass={cn122_validation['orthogonality_tests']['pass']}, "
          f"fail={cn122_validation['orthogonality_tests']['fail']}")
    print(f"cn122 dual-basis all pass: {cn122_validation['all_pass']}")

    # 4. Analyze violating dual lines from analysis
    viol_lines = [
        {'D_basis': [43, 18], 'D_nonzero': [18, 43, 57]},
        {'D_basis': [42, 27], 'D_nonzero': [27, 42, 49]},
        {'D_basis': [234, 27], 'D_nonzero': [27, 234, 241]},
        {'D_basis': [179, 9], 'D_nonzero': [9, 179, 186]},
        {'D_basis': [133, 18], 'D_nonzero': [18, 133, 151]},
        {'D_basis': [87, 9], 'D_nonzero': [9, 87, 94]},
    ]
    viol_pair_analysis = analyze_rank9_pairs(contractions, viol_lines)
    for vp in viol_pair_analysis:
        print(f"Violating line {vp.get('D_nonzero')}: "
              f"N_rank={vp.get('N_rank')}, "
              f"M1^-1*M2+I rank={vp.get('MinvM_plus_I_rank')}")

    # 5. Systematic pair analysis
    sys_pairs = systematic_pair_analysis(contractions, T_core)
    print(f"Systematic: {sys_pairs['total_rank9']} rank-9, "
          f"{sys_pairs['total_pairs']} pairs, "
          f"N-rank histogram: {sys_pairs['N_rank_histogram']}")

    elapsed = time.time() - t0
    result = {
        'schema': 'dual_basis_instrument_v1',
        'elapsed_sec': round(elapsed, 3),
        'core_shape': list(T_core.shape),
        'contraction_rank_histogram': {str(k): v for k, v in sorted(rank_hist.items())},
        'invertible_count': inv_count,
        'cn122_core_terms': len(core_terms),
        'cn122_dual_basis_validation': cn122_validation,
        'violating_line_pair_analysis': viol_pair_analysis,
        'systematic_pair_analysis': sys_pairs,
    }

    args.out.write_text(json.dumps(result, indent=2, default=str) + '\n')
    print(f"\nSaved {args.out}")


if __name__ == '__main__':
    main()
