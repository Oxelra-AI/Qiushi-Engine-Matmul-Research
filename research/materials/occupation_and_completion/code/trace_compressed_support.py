#!/usr/bin/env python3
r"""analysis: compressed support-level form of corrected trace equations.

For a fixed A-support and a set Q of saturated invertible contractions, the
corrected trace equations use only the evaluations

    y_{q,s} = phi_q(X_s),   phi_q(X)=tr(M_q^{-1} X).

The tensor identity projected by phi_q gives

    sum_s a_s[i] y_{q,s} = g_q(i),  g_q(i)=phi_q(T_i),

while saturation gives y_{q,s}=1 for s in I_q.  If the phi_q are linearly
dependent as functionals on 9x9 matrices, the same dependencies must hold among
the y_{q,s} for each term s.  This small linear system in |Q|*|support|
variables is equivalent to the full matrix-variable trace relaxation whenever
the tensor-only A-system can realize arbitrary residuals in the common kernel
(as is true for the full-span supports tested here), and is directly comparable
by Gaussian elimination.
"""
from __future__ import annotations

import itertools
import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (  # noqa: E402
    build_matmul_tensor_f2,
    contraction_matrix,
    gf2_linear_consistency,
    gf2_rank_rows,
    mat_rank_f2,
)
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from corrected_trace_instrument import NEAR_MISS, contraction_rank_data, trace_rows_for_support  # noqa: E402
from corrected_trace_batch import load_candidates  # noqa: E402

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/corrected_trace"


def trace_mask_correct(M_inv: np.ndarray) -> int:
    """Bit mask for phi(X)=tr(M_inv X) on vectorized variables X[b,c]."""
    n = M_inv.shape[0]
    mask = 0
    for b in range(n):
        for c in range(n):
            if int(M_inv[c, b]) & 1:
                mask |= 1 << (b * n + c)
    return mask


def matrix_mask(M: np.ndarray) -> int:
    n, m = M.shape
    mask = 0
    for b in range(n):
        for c in range(m):
            if int(M[b, c]) & 1:
                mask |= 1 << (b * m + c)
    return mask


def dot_masks(a: int, b: int) -> int:
    return (int(a) & int(b)).bit_count() & 1


def gf2_nullspace(row_masks: Sequence[int], nvars: int) -> List[int]:
    """Return a basis for {x in F2^nvars: row*x=0 for all rows}."""
    rows = [int(r) & ((1 << nvars) - 1) for r in row_masks if int(r) & ((1 << nvars) - 1)]
    pivots: List[int] = []
    r = 0
    rows = rows[:]
    for col in range(nvars - 1, -1, -1):
        pivot = None
        for i in range(r, len(rows)):
            if (rows[i] >> col) & 1:
                pivot = i
                break
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        for i in range(len(rows)):
            if i != r and ((rows[i] >> col) & 1):
                rows[i] ^= rows[r]
        pivots.append(col)
        r += 1
        if r == len(rows):
            break
    pivot_set = set(pivots)
    rref_rows = rows[:r]
    row_for_pivot = {pivots[i]: rref_rows[i] for i in range(len(pivots))}
    basis = []
    for free in range(nvars):
        if free in pivot_set:
            continue
        x = 1 << free
        for p in pivots:
            row = row_for_pivot[p]
            # pivot variable x_p + sum_free row[f] x_f = 0
            if (row >> free) & 1:
                x |= 1 << p
        basis.append(x)
    return basis


def trace_dependency_basis(trace_masks: Sequence[int]) -> List[int]:
    """Dependencies lambda among trace_masks: xor_q lambda_q mask_q = 0."""
    m = len(trace_masks)
    coordinate_rows = []
    for j in range(81):
        row = 0
        for qidx, mask in enumerate(trace_masks):
            if (int(mask) >> j) & 1:
                row |= 1 << qidx
        if row:
            coordinate_rows.append(row)
    return gf2_nullspace(coordinate_rows, m)


def build_compressed_system(T_core: np.ndarray, A_support: Sequence[int], contractions: Dict[int, dict], q_subset: Sequence[int] | None = None) -> dict:
    na, nb, nc = T_core.shape
    support = [int(x) for x in A_support]
    if q_subset is None:
        qs = []
        for q, info in contractions.items():
            if info["rank"] != 9:
                continue
            I = [s for s, a in enumerate(support) if ((a & q).bit_count() & 1)]
            if len(I) == 9:
                qs.append(int(q))
        qs.sort()
    else:
        qs = [int(q) for q in q_subset]
    m = len(qs)
    nterms = len(support)
    nvars = m * nterms

    def vid(qidx: int, s: int) -> int:
        return qidx * nterms + s

    trace_masks = [trace_mask_correct(contractions[q]["M_inv"]) for q in qs]
    deps = trace_dependency_basis(trace_masks)
    trace_rank = m - len(deps)

    rows = []
    labels = []

    # Projected tensor equations: for each q and A-coordinate i.
    for qidx, q in enumerate(qs):
        phi = trace_masks[qidx]
        g_bits = []
        for i in range(na):
            rhs = dot_masks(phi, matrix_mask(T_core[i]))
            g_bits.append(rhs)
            row = 0
            for s, a in enumerate(support):
                if (a >> i) & 1:
                    row ^= 1 << vid(qidx, s)
            row |= rhs << nvars
            rows.append(row)
            labels.append(("projected_tensor", q, i, rhs))

    # Saturated participation trace equations y_{q,s}=1 for s in I_q.
    for qidx, q in enumerate(qs):
        for s, a in enumerate(support):
            if ((a & q).bit_count() & 1):
                row = (1 << vid(qidx, s)) | (1 << nvars)
                rows.append(row)
                labels.append(("fixed_trace", q, s))

    # Functional dependencies among trace masks, term by term.
    for dep in deps:
        for s in range(nterms):
            row = 0
            for qidx in range(m):
                if (dep >> qidx) & 1:
                    row ^= 1 << vid(qidx, s)
            rows.append(row)  # RHS 0
            labels.append(("trace_dependency", dep, s))

    consistent, rank, cert = gf2_linear_consistency(rows, nvars)
    # Summarize certificate if inconsistent.
    cert_summary = None
    if cert is not None:
        used = [idx for idx in range(len(rows)) if (cert >> idx) & 1]
        xor = 0
        for idx in used:
            xor ^= rows[idx]
        q_counts = Counter()
        type_counts = Counter()
        dep_rows = 0
        for idx in used:
            lbl = labels[idx]
            type_counts[lbl[0]] += 1
            if lbl[0] in ("projected_tensor", "fixed_trace"):
                q_counts[lbl[1]] += 1
            elif lbl[0] == "trace_dependency":
                dep_rows += 1
        cert_summary = {
            "row_count": len(used),
            "type_counts": {str(k): v for k, v in sorted(type_counts.items())},
            "q_counts": {str(k): v for k, v in sorted(q_counts.items())},
            "dependency_rows": dep_rows,
            "verification": {
                "coefficients_zero": (xor & ((1 << nvars) - 1)) == 0,
                "rhs_one": ((xor >> nvars) & 1) == 1,
            },
            "used_label_sample": [list(labels[idx]) for idx in used[:60]],
        }
    return {
        "q_subset": qs,
        "q_count": m,
        "trace_functional_rank": trace_rank,
        "trace_dependency_count": len(deps),
        "trace_dependencies": [int(x) for x in deps[:20]],
        "variables": nvars,
        "rows": len(rows),
        "rank": int(rank),
        "consistent": bool(consistent),
        "certificate": cert_summary,
    }


def full_system_status(T_core: np.ndarray, A_support: Sequence[int], contractions: Dict[int, dict], q_subset: Sequence[int] | None) -> dict:
    rows, _labels, nvars, qs = trace_rows_for_support(T_core, A_support, contractions, coefficient="correct", q_filter=q_subset)
    consistent, rank, cert = gf2_linear_consistency(rows, nvars)
    return {"q_subset": qs, "rows": len(rows), "variables": nvars, "rank": int(rank), "consistent": bool(consistent), "cert_rows": int(cert.bit_count()) if cert is not None else 0}


def pair_subset_scan(T_core: np.ndarray, contractions: Dict[int, dict], support: Sequence[int], sat_qs: Sequence[int]) -> dict:
    # Confirm no small-q contradiction faster in compressed form, and find first examples.
    first = None
    tested_by_k = {}
    examples = []
    for k in range(1, len(sat_qs) + 1):
        tested = 0
        for comb in itertools.combinations(sat_qs, k):
            res = build_compressed_system(T_core, support, contractions, comb)
            tested += 1
            if not res["consistent"]:
                if first is None:
                    first = k
                if len(examples) < 8:
                    examples.append({"q_subset": list(comb), "compressed": {kk: res[kk] for kk in ["q_count", "trace_functional_rank", "trace_dependency_count", "variables", "rows", "rank", "consistent"]}, "certificate": res["certificate"]})
        tested_by_k[str(k)] = tested
        if first is not None:
            break
    return {"minimum_q_count_found": first, "tested_by_k_until_first": tested_by_k, "examples": examples}


def main() -> None:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    T_core = build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2
    contractions = contraction_rank_data(T_core)

    # Main near-miss analysis.
    all_comp = build_compressed_system(T_core, NEAR_MISS, contractions, None)
    all_full = full_system_status(T_core, NEAR_MISS, contractions, None)
    sat_qs = all_comp["q_subset"]
    min_scan = pair_subset_scan(T_core, contractions, NEAR_MISS, sat_qs)

    # Check equivalence with full matrix-variable system on a few subsets.
    subset_checks = []
    test_subsets = [[49], [42, 43, 49], min_scan["examples"][0]["q_subset"] if min_scan["examples"] else sat_qs[:8], sat_qs]
    seen = set()
    for subset in test_subsets:
        key = tuple(subset)
        if key in seen:
            continue
        seen.add(key)
        comp = build_compressed_system(T_core, NEAR_MISS, contractions, subset)
        full = full_system_status(T_core, NEAR_MISS, contractions, subset)
        subset_checks.append({
            "q_subset": list(subset),
            "compressed_consistent": comp["consistent"],
            "full_consistent": full["consistent"],
            "compressed_rank": comp["rank"],
            "full_rank": full["rank"],
            "compressed_variables": comp["variables"],
            "full_variables": full["variables"],
        })

    # Batch summary on existing candidates, using compressed system only but checking full equivalence for first few.
    batch_records = []
    candidates = load_candidates()
    for idx, cand in enumerate(candidates):
        support = [int(x) for x in cand["A_cols"]]
        comp = build_compressed_system(T_core, support, contractions, None)
        rec = {
            "index": idx,
            "name": cand.get("name"),
            "complete_wang_violations": cand.get("complete_wang_violations"),
            "saturated_rank9_count": comp["q_count"],
            "trace_functional_rank": comp["trace_functional_rank"],
            "trace_dependency_count": comp["trace_dependency_count"],
            "compressed_trace_consistent": comp["consistent"],
            "compressed_rows": comp["rows"],
            "compressed_variables": comp["variables"],
        }
        if idx < 6:
            full = full_system_status(T_core, support, contractions, None)
            rec["full_trace_consistent"] = full["consistent"]
            rec["full_trace_rank"] = full["rank"]
        batch_records.append(rec)

    mismatch = [r for r in batch_records if "full_trace_consistent" in r and r["full_trace_consistent"] != r["compressed_trace_consistent"]]
    summary = {
        "candidate_count": len(batch_records),
        "compressed_consistent": sum(1 for r in batch_records if r["compressed_trace_consistent"]),
        "compressed_inconsistent": sum(1 for r in batch_records if not r["compressed_trace_consistent"]),
        "full_checked_prefix_mismatches": len(mismatch),
        "sat_rank9_hist": {str(k): v for k, v in sorted(Counter(r["saturated_rank9_count"] for r in batch_records).items())},
        "trace_functional_rank_hist": {str(k): v for k, v in sorted(Counter(r["trace_functional_rank"] for r in batch_records).items())},
    }

    result = {
        "schema": "compressed_corrected_trace_support_system_v1",
        "field": "F2",
        "meaning": "Small support-level linear system for corrected trace evaluations y_{q,s}; avoids 19*81 matrix variables and reproduces full corrected trace consistency on checked supports/subsets.",
        "near_miss": {
            "support": list(NEAR_MISS),
            "compressed_all_saturated_rank9": all_comp,
            "full_all_saturated_rank9": all_full,
            "subset_equivalence_checks": subset_checks,
            "minimum_q_subset_scan_compressed": min_scan,
        },
        "existing_candidate_batch_summary": summary,
        "existing_candidate_batch_records": batch_records,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = OUTDIR / "compressed_trace_support_system.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "elapsed_sec": result["elapsed_sec"],
        "near_miss_comp_consistent": all_comp["consistent"],
        "near_miss_full_consistent": all_full["consistent"],
        "near_miss_q_count": all_comp["q_count"],
        "near_miss_trace_rank": all_comp["trace_functional_rank"],
        "min_q_count": min_scan["minimum_q_count_found"],
        "batch_summary": summary,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
