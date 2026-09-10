#!/usr/bin/env python3
r"""analysis: extract corrected multi-contraction trace certificates.

Uses the corrected trace coefficient M_inv[c,b] on X[b,c].  The goal is to
replace the invalid analysis q=49 certificate with a faithful statement about
what corrected trace equations actually imply for the analysis near-miss support.
"""
from __future__ import annotations

import itertools
import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (  # noqa: E402
    build_matmul_tensor_f2,
    contraction_matrix,
    gf2_linear_consistency,
    mat_rank_f2,
)
from dual_basis_instrument import gf2_mat_inv  # noqa: E402

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/corrected_trace"
SUPPORT = [1, 2, 3, 4, 8, 20, 24, 31, 32, 64, 73, 109, 127, 128, 141, 160, 182, 192, 219]


def build_labeled_rows(T_core: np.ndarray, A_support: Sequence[int], q_subset: Iterable[int] | None = None):
    na, nb, nc = T_core.shape
    nterms = len(A_support)
    nvars = nterms * nb * nc
    q_allowed = None if q_subset is None else set(int(q) for q in q_subset)

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

    saturated_qs = []
    for q in range(1, 1 << na):
        if q_allowed is not None and q not in q_allowed:
            continue
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) != 9:
            continue
        I = [s for s, a in enumerate(A_support) if ((int(a) & q).bit_count() & 1)]
        if len(I) != 9:
            continue
        saturated_qs.append(q)
        M_inv = gf2_mat_inv(M)
        assert M_inv is not None
        for s in I:
            row = 0
            for b in range(nb):
                for c in range(nc):
                    if int(M_inv[c, b]) & 1:  # corrected coefficient for tr(M_inv X)
                        row ^= 1 << var_idx(s, b, c)
            row |= 1 << nvars
            rows.append(row)
            labels.append(("trace", q, s))

    return rows, labels, nvars, saturated_qs


def check(rows: Sequence[int], nvars: int):
    consistent, rank, cert = gf2_linear_consistency(list(rows), nvars)
    return bool(consistent), int(rank), cert


def cert_summary(rows: Sequence[int], labels: Sequence[Tuple], nvars: int, cert: int):
    used = [idx for idx in range(len(rows)) if (cert >> idx) & 1]
    xor = 0
    for idx in used:
        xor ^= rows[idx]
    coeff_zero = (xor & ((1 << nvars) - 1)) == 0
    rhs_one = ((xor >> nvars) & 1) == 1
    q_counts = Counter()
    tensor_i_counts = Counter()
    tensor_rows = []
    trace_rows = []
    term_trace_counts = Counter()
    for idx in used:
        lbl = labels[idx]
        if lbl[0] == "tensor":
            tensor_rows.append(lbl)
            tensor_i_counts[lbl[1]] += 1
        elif lbl[0] == "trace":
            trace_rows.append(lbl)
            q_counts[lbl[1]] += 1
            term_trace_counts[lbl[2]] += 1
    return {
        "row_count": len(used),
        "tensor_rows": len(tensor_rows),
        "trace_rows": len(trace_rows),
        "trace_qs": sorted(q_counts),
        "trace_q_count": len(q_counts),
        "trace_rows_by_q": {str(k): v for k, v in sorted(q_counts.items())},
        "trace_rows_by_term": {str(k): v for k, v in sorted(term_trace_counts.items())},
        "tensor_rows_by_A_coord": {str(k): v for k, v in sorted(tensor_i_counts.items())},
        "verification": {"coefficients_zero": coeff_zero, "rhs_one": rhs_one, "valid_contradiction": coeff_zero and rhs_one},
        "used_label_sample": [list(x) for x in (tensor_rows[:20] + trace_rows[:20])],
    }


def shrink_rows(rows: Sequence[int], labels: Sequence[Tuple], nvars: int):
    # Start from one certificate if the whole row set is inconsistent, then greedily delete.
    consistent, _rank, cert = check(rows, nvars)
    if consistent or cert is None:
        return None
    active = [idx for idx in range(len(rows)) if (cert >> idx) & 1]
    changed = True
    while changed:
        changed = False
        for idx in active[:]:
            trial = [j for j in active if j != idx]
            con, _r, _c = check([rows[j] for j in trial], nvars)
            if not con:
                active = trial
                changed = True
    shrunk_rows = [rows[j] for j in active]
    con, rank, cert2 = check(shrunk_rows, nvars)
    assert not con
    # cert2 indexes the shrunk list. Build a dense cert over shrunk rows if needed.
    # Summarize directly over the active set using all active rows if they XOR to contradiction;
    # if not, use cert2-selected subset.
    if cert2 is not None:
        selected_active = [active[j] for j in range(len(active)) if (cert2 >> j) & 1]
    else:
        selected_active = active
    selected_rows = [rows[j] for j in selected_active]
    selected_labels = [labels[j] for j in selected_active]
    # Build a summary with local labels.
    xor = 0
    for r in selected_rows:
        xor ^= r
    coeff_zero = (xor & ((1 << nvars) - 1)) == 0
    rhs_one = ((xor >> nvars) & 1) == 1
    q_counts = Counter(lbl[1] for lbl in selected_labels if lbl[0] == "trace")
    tensor_i_counts = Counter(lbl[1] for lbl in selected_labels if lbl[0] == "tensor")
    term_counts = Counter(lbl[2] for lbl in selected_labels if lbl[0] == "trace")
    return {
        "selected_original_indices": selected_active,
        "row_count": len(selected_active),
        "tensor_rows": sum(1 for lbl in selected_labels if lbl[0] == "tensor"),
        "trace_rows": sum(1 for lbl in selected_labels if lbl[0] == "trace"),
        "trace_qs": sorted(q_counts),
        "trace_rows_by_q": {str(k): v for k, v in sorted(q_counts.items())},
        "trace_rows_by_term": {str(k): v for k, v in sorted(term_counts.items())},
        "tensor_rows_by_A_coord": {str(k): v for k, v in sorted(tensor_i_counts.items())},
        "verification": {"coefficients_zero": coeff_zero, "rhs_one": rhs_one, "valid_contradiction": coeff_zero and rhs_one},
        "labels": [list(lbl) for lbl in selected_labels],
    }


def find_min_q_subsets(T_core: np.ndarray, sat_qs: Sequence[int], max_examples: int = 10):
    results = []
    first_k = None
    tested_by_k = {}
    for k in range(1, len(sat_qs) + 1):
        tested = 0
        examples = []
        for comb in itertools.combinations(sat_qs, k):
            rows, labels, nvars, _ = build_labeled_rows(T_core, SUPPORT, comb)
            con, rank, cert = check(rows, nvars)
            tested += 1
            if not con:
                examples.append({
                    "q_subset": list(comb),
                    "rank": rank,
                    "rows": len(rows),
                    "certificate": cert_summary(rows, labels, nvars, cert),
                })
                if len(examples) >= max_examples:
                    break
        tested_by_k[str(k)] = tested
        if examples:
            first_k = k
            results = examples
            break
    return {"minimum_q_count_found": first_k, "tested_by_k_until_first": tested_by_k, "examples": results}


def greedy_shrink_qs(T_core: np.ndarray, sat_qs: Sequence[int]):
    active = list(sat_qs)
    changed = True
    while changed:
        changed = False
        for q in active[:]:
            trial = [x for x in active if x != q]
            rows, _labels, nvars, _ = build_labeled_rows(T_core, SUPPORT, trial)
            con, rank, cert = check(rows, nvars)
            if not con:
                active = trial
                changed = True
    rows, labels, nvars, _ = build_labeled_rows(T_core, SUPPORT, active)
    con, rank, cert = check(rows, nvars)
    shrunk = shrink_rows(rows, labels, nvars)
    return {
        "q_subset": active,
        "q_count": len(active),
        "consistent": con,
        "rank": rank,
        "rows": len(rows),
        "certificate": cert_summary(rows, labels, nvars, cert) if cert is not None else None,
        "greedy_row_shrink": shrunk,
    }


def main() -> None:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    T_core = build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2
    rows, labels, nvars, sat_qs = build_labeled_rows(T_core, SUPPORT, None)
    con, rank, cert = check(rows, nvars)
    full_summary = cert_summary(rows, labels, nvars, cert) if cert is not None else None
    full_shrink = shrink_rows(rows, labels, nvars)
    per_q = []
    for q in sat_qs:
        rq, _lq, nvq, _ = build_labeled_rows(T_core, SUPPORT, [q])
        cq, rr, certq = check(rq, nvq)
        per_q.append({"q": q, "consistent": cq, "rank": rr, "rows": len(rq), "cert_rows": certq.bit_count() if certq is not None else 0})
    min_q = find_min_q_subsets(T_core, sat_qs, max_examples=12)
    greedy_q = greedy_shrink_qs(T_core, sat_qs)

    result = {
        "schema": "corrected_trace_certificate_v1",
        "field": "F2",
        "support": SUPPORT,
        "coefficient_convention": "correct M_inv[c,b] coefficient on X[b,c], i.e. tr(M_inv X)",
        "saturated_rank9_qs": sat_qs,
        "full_corrected_system": {"consistent": con, "rank": rank, "rows": len(rows), "nvars": nvars, "certificate": full_summary},
        "full_greedy_row_shrink": full_shrink,
        "per_single_q_corrected": per_q,
        "minimum_q_subsets": min_q,
        "greedy_q_subset": greedy_q,
        "elapsed_sec": round(time.time() - t0, 3),
        "meaning": "This replaces the invalid analysis single-q certificate. Single corrected q systems are consistent; the near-miss is rejected only by coupling several corrected saturated contraction trace functionals with the tensor identity.",
    }
    out = OUTDIR / "corrected_trace_certificate.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "elapsed_sec": result["elapsed_sec"],
        "full_consistent": con,
        "full_rank": rank,
        "full_cert_rows": full_summary["row_count"] if full_summary else None,
        "single_q_inconsistent": sum(1 for r in per_q if not r["consistent"]),
        "min_q_count": min_q["minimum_q_count_found"],
        "first_min_examples": [e["q_subset"] for e in min_q["examples"][:5]],
        "greedy_q_subset": greedy_q["q_subset"],
        "greedy_row_count": greedy_q["greedy_row_shrink"]["row_count"] if greedy_q.get("greedy_row_shrink") else None,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
