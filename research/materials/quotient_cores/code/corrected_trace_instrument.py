#!/usr/bin/env python3
r"""analysis: corrected trace-functional convention for saturated rank-9 contractions.

analysis used the wrong entrywise coefficient for the linear functional on
X_s=b_s c_s^T.  The valid identity is

    tr(M^{-1} X_s) = sum_{b,c} (M^{-1})[c,b] X_s[b,c] = c_s^T M^{-1} b_s.

This script rebuilds the instrument with the transposed coefficient, validates it
on actual term matrices and on nonsymmetric synthetic invertible controls, and
compresses the one-contraction consequence to an 8-dimensional support test:

    g_q + sum_{s in I_q} a_s in span{a_s : s notin I_q},

where g_q(i)=tr(M_q^{-1} T_i) and I_q={s:q(a_s)=1}.  If the outside A-directions
span ker(q), this one-q trace consequence is automatic.
"""
from __future__ import annotations

import json
import random
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (  # noqa: E402
    build_matmul_tensor_f2,
    contraction_matrix,
    gf2_linear_consistency,
    in_span,
    mat_rank_f2,
    read_qmm_terms,
    restrict_terms_f2,
    rref_basis,
    vec_to_mask,
)
from dual_basis_instrument import gf2_mat_inv, gf2_mat_mul  # noqa: E402

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/corrected_trace"

NEAR_MISS = [1, 2, 3, 4, 8, 20, 24, 31, 32, 64, 73, 109, 127, 128, 141, 160, 182, 192, 219]


def build_e11_core_tensor() -> np.ndarray:
    return build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2


def mask_to_col(mask: int, n: int = 9) -> np.ndarray:
    return np.array([(int(mask) >> i) & 1 for i in range(n)], dtype=np.uint8).reshape(n, 1)


def outer_from_masks(bmask: int, cmask: int, n: int = 9) -> np.ndarray:
    b = mask_to_col(bmask, n)
    c = mask_to_col(cmask, n)
    return (b @ c.T).astype(np.uint8) % 2


def trace_functional_correct(M_inv: np.ndarray, X: np.ndarray) -> int:
    """Return tr(M_inv X) over F2 for X[b,c]."""
    n = M_inv.shape[0]
    val = 0
    for b in range(n):
        for c in range(n):
            val ^= (int(M_inv[c, b]) & int(X[b, c]))
    return val & 1


def trace_functional_wrong(M_inv: np.ndarray, X: np.ndarray) -> int:
    """The entrywise pairing used in analysis: sum M_inv[b,c] X[b,c]."""
    n = M_inv.shape[0]
    val = 0
    for b in range(n):
        for c in range(n):
            val ^= (int(M_inv[b, c]) & int(X[b, c]))
    return val & 1


def direct_dual_basis_value(M_inv: np.ndarray, bmask: int, cmask: int, n: int = 9) -> int:
    b = mask_to_col(bmask, n)
    c = mask_to_col(cmask, n)
    y = gf2_mat_mul(M_inv, b).reshape(n)
    cv = c.reshape(n)
    return sum((int(cv[i]) & int(y[i])) for i in range(n)) & 1


def contraction_rank_data(T_core: np.ndarray) -> Dict[int, dict]:
    out: Dict[int, dict] = {}
    for q in range(1, 1 << T_core.shape[0]):
        M = contraction_matrix(T_core, q)
        rk = mat_rank_f2(M)
        out[q] = {"rank": int(rk), "M": M, "M_inv": gf2_mat_inv(M) if rk == 9 else None}
    return out


def load_cn122_core_terms() -> Tuple[List[dict], List[int], List[int], List[int]]:
    terms = read_qmm_terms(ROOT / "workspace/data/cn122_3x3_r23_repro/scheme.qmm")
    core_terms = restrict_terms_f2(terms, 1)
    A = [vec_to_mask(t["u"]) for t in core_terms]
    B = [vec_to_mask(t["v"]) for t in core_terms]
    C = [vec_to_mask(t["w"]) for t in core_terms]
    return core_terms, A, B, C


def validate_actual_terms(T_core: np.ndarray, contractions: Dict[int, dict]) -> dict:
    _terms, A, B, C = load_cn122_core_terms()
    records = []
    totals = Counter()
    for q, info in contractions.items():
        if info["rank"] != 9:
            continue
        I = [s for s, a in enumerate(A) if ((a & q).bit_count() & 1)]
        if len(I) != 9:
            continue
        M_inv = info["M_inv"]
        q_rec = {"q": q, "q_hex": hex(q), "terms": I, "correct_failures": [], "wrong_failures": []}
        totals["saturated_rank9_q"] += 1
        for s in I:
            X = outer_from_masks(B[s], C[s], 9)
            direct = direct_dual_basis_value(M_inv, B[s], C[s], 9)
            corr = trace_functional_correct(M_inv, X)
            wrong = trace_functional_wrong(M_inv, X)
            totals["term_tests"] += 1
            if direct != 1:
                totals["direct_fail"] += 1
            if corr != direct or corr != 1:
                totals["correct_fail"] += 1
                q_rec["correct_failures"].append({"s": s, "direct": int(direct), "correct": int(corr)})
            if wrong != direct:
                totals["wrong_disagrees_with_direct"] += 1
                q_rec["wrong_failures"].append({"s": s, "direct": int(direct), "wrong": int(wrong)})
        if q_rec["correct_failures"] or q_rec["wrong_failures"]:
            records.append(q_rec)
    return {
        "control": "cn122_E11_core_actual_terms",
        "terms": len(A),
        "unique_A_directions": len(set(A)),
        "saturated_rank9_contractions": totals["saturated_rank9_q"],
        "term_tests": totals["term_tests"],
        "direct_failures": totals["direct_fail"],
        "correct_coefficient_failures": totals["correct_fail"],
        "wrong_disagreements_with_direct": totals["wrong_disagrees_with_direct"],
        "affected_q_sample": records[:8],
    }


def random_invertible_matrix(rng: random.Random, n: int = 9) -> np.ndarray:
    M = np.eye(n, dtype=np.uint8)
    # Random elementary row and column operations keep invertibility.
    for _ in range(6 * n):
        typ = rng.randrange(3)
        i = rng.randrange(n)
        j = rng.randrange(n)
        if i == j:
            continue
        if typ == 0:
            M[[i, j], :] = M[[j, i], :]
        elif typ == 1:
            M[:, [i, j]] = M[:, [j, i]]
        else:
            if rng.randrange(2):
                M[i, :] ^= M[j, :]
            else:
                M[:, i] ^= M[:, j]
    return M % 2


def validate_synthetic_controls(trials: int = 30, seed: int = 5101) -> dict:
    rng = random.Random(seed)
    records = []
    totals = Counter()
    for trial in range(trials):
        B = random_invertible_matrix(rng, 9)
        C = random_invertible_matrix(rng, 9)
        # Columns of B and C define nine rank-one terms.
        M = gf2_mat_mul(B, C.T.astype(np.uint8))
        Minv = gf2_mat_inv(M)
        assert Minv is not None
        nonsymmetric = not np.array_equal(M, M.T)
        correct_fail = 0
        wrong_disagree = 0
        wrong_values = []
        for s in range(9):
            bmask = 0
            cmask = 0
            for i in range(9):
                if int(B[i, s]) & 1:
                    bmask |= 1 << i
                if int(C[i, s]) & 1:
                    cmask |= 1 << i
            X = outer_from_masks(bmask, cmask, 9)
            direct = direct_dual_basis_value(Minv, bmask, cmask, 9)
            corr = trace_functional_correct(Minv, X)
            wrong = trace_functional_wrong(Minv, X)
            if direct != 1 or corr != 1 or corr != direct:
                correct_fail += 1
            if wrong != direct:
                wrong_disagree += 1
            wrong_values.append(int(wrong))
        wrong_total_M = trace_functional_wrong(Minv, M)
        correct_total_M = trace_functional_correct(Minv, M)
        totals["trials"] += 1
        totals["nonsymmetric_trials"] += int(nonsymmetric)
        totals["correct_failures"] += correct_fail
        totals["wrong_disagreements"] += wrong_disagree
        if len(records) < 6 and (nonsymmetric or wrong_disagree):
            records.append({
                "trial": trial,
                "M_rank": int(mat_rank_f2(M)),
                "M_is_symmetric": bool(np.array_equal(M, M.T)),
                "correct_total_trace_Minv_M": int(correct_total_M),
                "wrong_pairing_on_M": int(wrong_total_M),
                "correct_failures": correct_fail,
                "wrong_disagreements": wrong_disagree,
                "wrong_values": wrong_values,
            })
    return {
        "seed": seed,
        "trials": trials,
        "nonsymmetric_trials": totals["nonsymmetric_trials"],
        "correct_failures": totals["correct_failures"],
        "wrong_disagreements": totals["wrong_disagreements"],
        "sample_records": records,
    }


def q_to_full_matrix(q: int) -> List[List[int]]:
    # Core coordinates 0..7 correspond to full row-major positions 1..8; E11 is absent.
    full_bits = [0] + [(q >> i) & 1 for i in range(8)]
    return [[int(full_bits[3 * r + c]) for c in range(3)] for r in range(3)]


def kron_cycle_check(T_core: np.ndarray, q: int = 49) -> dict:
    M = contraction_matrix(T_core, q)
    Minv = gf2_mat_inv(M)
    Q = np.array(q_to_full_matrix(q), dtype=np.uint8)
    I3 = np.eye(3, dtype=np.uint8)
    candidates = {
        "kron_QT_I3": np.kron(Q.T, I3).astype(np.uint8) % 2,
        "kron_Q_I3": np.kron(Q, I3).astype(np.uint8) % 2,
        "kron_I3_QT": np.kron(I3, Q.T).astype(np.uint8) % 2,
        "kron_I3_Q": np.kron(I3, Q).astype(np.uint8) % 2,
    }
    matches = [name for name, C in candidates.items() if np.array_equal(M, C)]
    wrong_pair = trace_functional_wrong(Minv, M) if Minv is not None else None
    corr_pair = trace_functional_correct(Minv, M) if Minv is not None else None
    return {
        "q": q,
        "q_hex": hex(q),
        "q_full_matrix_row_major": q_to_full_matrix(q),
        "description": "core bits mark E12, E23, E31; this is the 3-cycle functional",
        "rank_L_q": int(mat_rank_f2(M)),
        "kron_matches": matches,
        "correct_pairing_tr_Minv_M": int(corr_pair) if corr_pair is not None else None,
        "wrong_entry_pairing": int(wrong_pair) if wrong_pair is not None else None,
        "explanation": "Summing nine wrong trace rows gives the wrong entrywise pairing on M, while the correct trace gives tr(I_9)=1 in F2.",
    }


def trace_rows_for_support(
    T_core: np.ndarray,
    A_support: Sequence[int],
    contractions: Dict[int, dict],
    coefficient: str = "correct",
    q_filter: Optional[Iterable[int]] = None,
) -> Tuple[List[int], List[Tuple], int, List[int]]:
    na, nb, nc = T_core.shape
    nterms = len(A_support)
    nvars = nterms * nb * nc
    q_allowed = None if q_filter is None else set(int(q) for q in q_filter)

    def var_idx(s: int, b: int, c: int) -> int:
        return s * nb * nc + b * nc + c

    rows: List[int] = []
    labels: List[Tuple] = []
    for i in range(na):
        for b in range(nb):
            for c in range(nc):
                row = 0
                for s, a in enumerate(A_support):
                    if (int(a) >> i) & 1:
                        row ^= 1 << var_idx(s, b, c)
                row |= (int(T_core[i, b, c]) & 1) << nvars
                rows.append(row)
                labels.append(("tensor", i, b, c))
    saturated_qs: List[int] = []
    for q, info in contractions.items():
        if q_allowed is not None and q not in q_allowed:
            continue
        if info["rank"] != 9:
            continue
        I = [s for s, a in enumerate(A_support) if ((int(a) & q).bit_count() & 1)]
        if len(I) != 9:
            continue
        saturated_qs.append(q)
        Minv = info["M_inv"]
        for s in I:
            row = 0
            for b in range(nb):
                for c in range(nc):
                    coeff = int(Minv[c, b]) if coefficient == "correct" else int(Minv[b, c])
                    if coeff & 1:
                        row ^= 1 << var_idx(s, b, c)
            row |= 1 << nvars
            rows.append(row)
            labels.append(("trace", q, s, coefficient))
    return rows, labels, nvars, saturated_qs


def system_consistency(rows: Sequence[int], nvars: int) -> dict:
    consistent, rank, cert = gf2_linear_consistency(list(rows), nvars)
    return {
        "consistent": bool(consistent),
        "rank": int(rank),
        "rows": len(rows),
        "contradiction_rows": int(cert.bit_count()) if cert is not None else 0,
    }


def support_trace_condition(T_core: np.ndarray, A_support: Sequence[int], contractions: Dict[int, dict]) -> dict:
    na, nb, nc = T_core.shape
    per_q = []
    failures = []
    outside_dim_hist = Counter()
    automatic_count = 0
    pass_count = 0
    for q, info in contractions.items():
        if info["rank"] != 9:
            continue
        I = [s for s, a in enumerate(A_support) if ((int(a) & q).bit_count() & 1)]
        if len(I) != 9:
            continue
        Minv = info["M_inv"]
        g = 0
        for i in range(na):
            val = trace_functional_correct(Minv, T_core[i])
            if val:
                g |= 1 << i
        sum_I = 0
        for s in I:
            sum_I ^= int(A_support[s])
        h = g ^ sum_I
        outside = [int(A_support[s]) for s in range(len(A_support)) if s not in set(I)]
        outside_basis = rref_basis(outside, na)
        outside_dim = len(outside_basis)
        outside_dim_hist[outside_dim] += 1
        h_in = in_span(h, outside_basis, na)
        if h_in:
            pass_count += 1
        else:
            failures.append(q)
        if outside_dim == na - 1:
            automatic_count += 1
        qh = ((h & q).bit_count() & 1)
        per_q.append({
            "q": q,
            "q_hex": hex(q),
            "I_q_indices": I,
            "outside_count": len(outside),
            "outside_span_dim": outside_dim,
            "outside_spans_kernel_q": bool(outside_dim == na - 1),
            "g_q_mask": g,
            "sum_I_mask": sum_I,
            "h_mask": h,
            "q_dot_h": qh,
            "h_in_outside_span": bool(h_in),
        })
    return {
        "support": [int(x) for x in A_support],
        "saturated_rank9": len(per_q),
        "single_q_trace_condition_passed": pass_count,
        "single_q_trace_condition_failed": len(failures),
        "failed_qs": failures,
        "outside_span_dim_hist": {str(k): v for k, v in sorted(outside_dim_hist.items())},
        "automatic_when_outside_spans_kernel_count": automatic_count,
        "per_q": per_q,
        "interpretation": "The corrected one-contraction trace consequence is exactly h_q in span(outside A-points); it is automatic when the outside points span ker(q).",
    }


def analyze_corrected_systems(T_core: np.ndarray, contractions: Dict[int, dict]) -> dict:
    # cn122 actual A support has multiplicity, so use list as stored.
    _terms, cnA, _B, _C = load_cn122_core_terms()
    rows_cn_tensor, _, nvars_cn, _ = trace_rows_for_support(T_core, cnA, contractions, coefficient="correct", q_filter=[])
    rows_cn_corr, _, _, sat_cn = trace_rows_for_support(T_core, cnA, contractions, coefficient="correct")
    rows_cn_wrong, _, _, _ = trace_rows_for_support(T_core, cnA, contractions, coefficient="wrong")

    rows_nm_tensor, _, nvars_nm, _ = trace_rows_for_support(T_core, NEAR_MISS, contractions, coefficient="correct", q_filter=[])
    rows_nm_corr, _, _, sat_nm = trace_rows_for_support(T_core, NEAR_MISS, contractions, coefficient="correct")
    rows_nm_wrong_all, _, _, _ = trace_rows_for_support(T_core, NEAR_MISS, contractions, coefficient="wrong")
    rows_nm_wrong_q49, _, _, _ = trace_rows_for_support(T_core, NEAR_MISS, contractions, coefficient="wrong", q_filter=[49])
    rows_nm_corr_q49, _, _, _ = trace_rows_for_support(T_core, NEAR_MISS, contractions, coefficient="correct", q_filter=[49])

    return {
        "cn122": {
            "terms": len(cnA),
            "unique_A_directions": len(set(cnA)),
            "saturated_rank9": len(sat_cn),
            "tensor_only": system_consistency(rows_cn_tensor, nvars_cn),
            "correct_trace": system_consistency(rows_cn_corr, nvars_cn),
            "wrong_trace": system_consistency(rows_cn_wrong, nvars_cn),
        },
        "near_miss": {
            "support": NEAR_MISS,
            "saturated_rank9": len(sat_nm),
            "saturated_qs": sat_nm,
            "tensor_only": system_consistency(rows_nm_tensor, nvars_nm),
            "correct_trace_all_saturated_rank9": system_consistency(rows_nm_corr, nvars_nm),
            "correct_trace_q49_only": system_consistency(rows_nm_corr_q49, nvars_nm),
            "wrong_trace_q49_only": system_consistency(rows_nm_wrong_q49, nvars_nm),
            "wrong_trace_all_saturated_rank9": system_consistency(rows_nm_wrong_all, nvars_nm),
            "support_level_single_q_conditions": support_trace_condition(T_core, NEAR_MISS, contractions),
        },
    }


def overlap_reinterpretation(T_core: np.ndarray, contractions: Dict[int, dict]) -> dict:
    rk9 = sorted(q for q, info in contractions.items() if info["rank"] == 9)
    mismatch = []
    hist = Counter()
    for i, q1 in enumerate(rk9):
        for q2 in rk9[i + 1:]:
            N = (contractions[q1]["M_inv"] + contractions[q2]["M_inv"]) % 2
            nr = mat_rank_f2(N)
            xr = contractions[q1 ^ q2]["rank"]
            hist[nr] += 1
            if int(nr) != int(xr):
                mismatch.append({"q1": q1, "q2": q2, "N_rank": int(nr), "xor_rank": int(xr)})
    # For the near-miss, verify the overlap identity and contraction lower-bound equivalence where q1,q2 saturated.
    sat_pair_count = 0
    equivalence_fail = []
    for i, q1 in enumerate(rk9):
        w1 = sum(1 for p in NEAR_MISS if ((p & q1).bit_count() & 1))
        if w1 != 9:
            continue
        for q2 in rk9[i + 1:]:
            w2 = sum(1 for p in NEAR_MISS if ((p & q2).bit_count() & 1))
            if w2 != 9:
                continue
            q3 = q1 ^ q2
            w3 = sum(1 for p in NEAR_MISS if ((p & q3).bit_count() & 1))
            overlap = sum(1 for p in NEAR_MISS if ((p & q1).bit_count() & 1) and ((p & q2).bit_count() & 1))
            nr = contractions[q3]["rank"]
            if w3 != 18 - 2 * overlap:
                equivalence_fail.append({"q1": q1, "q2": q2, "w3": w3, "overlap": overlap, "issue": "weight_identity"})
            if (overlap <= (18 - nr) // 2) != (w3 >= nr):
                equivalence_fail.append({"q1": q1, "q2": q2, "w3": w3, "overlap": overlap, "rank": int(nr), "issue": "bound_equivalence"})
            sat_pair_count += 1
    return {
        "rank9_contractions": len(rk9),
        "rank9_pairs": len(rk9) * (len(rk9) - 1) // 2,
        "rank_Minv_sum_histogram": {str(k): v for k, v in sorted(hist.items())},
        "rank_Minv_sum_equals_rank_L_qxor_failures": mismatch[:10],
        "rank_Minv_sum_equals_rank_L_qxor_failure_count": len(mismatch),
        "near_miss_saturated_rank9_pairs": sat_pair_count,
        "near_miss_overlap_contraction_equivalence_failures": equivalence_fail[:10],
        "near_miss_overlap_contraction_equivalence_failure_count": len(equivalence_fail),
        "interpretation": "Over F2, M1^{-1}+M2^{-1}=M1^{-1}(M1+M2)M2^{-1}; thus its rank is rank L(q1+q2). With w(q1)=w(q2)=9, the overlap bound is just w(q1+q2)>=rank L(q1+q2).",
    }


def main() -> None:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    T_core = build_e11_core_tensor()
    contractions = contraction_rank_data(T_core)

    rank_hist = Counter(info["rank"] for info in contractions.values())
    result = {
        "schema": "corrected_trace_instrument_v1",
        "field": "F2",
        "core": "E11 quotient core, T_full[1:,:,:]",
        "correction": {
            "wrong_coefficient": "M_inv[b,c] on X[b,c]",
            "correct_coefficient": "M_inv[c,b] on X[b,c], computing tr(M_inv X)=c^T M_inv b for X=b c^T",
            "dependent_outputs_not_tensor_meaning": [
                "workspace/data/dual_basis/trace_linear_strengthening.json",
                "workspace/data/dual_basis/trace_contradiction_certificate.json",
                "workspace/data/dual_basis/per_contraction_trace_test.json",
                "workspace/notes/dual_basis_theorem_and_trace_obstruction.md trace-obstruction section",
            ],
        },
        "core_contraction_rank_histogram": {str(k): v for k, v in sorted(rank_hist.items())},
        "q49_cycle_check": kron_cycle_check(T_core, 49),
        "actual_cn122_term_validation": validate_actual_terms(T_core, contractions),
        "synthetic_nonsymmetric_validation": validate_synthetic_controls(),
        "corrected_linear_systems": analyze_corrected_systems(T_core, contractions),
        "overlap_reinterpretation": overlap_reinterpretation(T_core, contractions),
        "elapsed_sec": None,
    }
    result["elapsed_sec"] = round(time.time() - t0, 3)

    out = OUTDIR / "corrected_trace_analysis.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "elapsed_sec": result["elapsed_sec"],
        "q49_wrong_pairing": result["q49_cycle_check"]["wrong_entry_pairing"],
        "q49_correct_pairing": result["q49_cycle_check"]["correct_pairing_tr_Minv_M"],
        "cn122_correct_failures": result["actual_cn122_term_validation"]["correct_coefficient_failures"],
        "synthetic_correct_failures": result["synthetic_nonsymmetric_validation"]["correct_failures"],
        "near_miss_correct_trace_consistent": result["corrected_linear_systems"]["near_miss"]["correct_trace_all_saturated_rank9"]["consistent"],
        "near_miss_single_q_failures": result["corrected_linear_systems"]["near_miss"]["support_level_single_q_conditions"]["single_q_trace_condition_failed"],
        "overlap_rank_failures": result["overlap_reinterpretation"]["rank_Minv_sum_equals_rank_L_qxor_failure_count"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
