#!/usr/bin/env python3
"""Exact tests around the E11 lift residual and rank-one block-sum claims.

This verifies the distribution of Delta=M0+q r^T over all q,r in F2^9 and
constructs a concrete counterexample to the over-strong statement that a sum of
rank-one terms equal to a rank-one matrix forces every nonzero term to share the
final column direction.  Such a force is valid only under saturation/minimality
conditions, not for arbitrary lifted subsets with cancellations.
"""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path


def rank_rows(rows, n):
    basis = [0] * n
    r = 0
    for row in rows:
        v = int(row)
        while v:
            p = v.bit_length() - 1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p] = v
                r += 1
                break
    return r


def outer_rows(q, r, n=9):
    return [r if ((q >> i) & 1) else 0 for i in range(n)]


def add_rows(A, B):
    return [int(a) ^ int(b) for a, b in zip(A, B)]


def rank_mat(rows):
    return rank_rows(rows, len(rows))


def main():
    out = Path("data/lift_residual/lift_residual_rank1_sum_test.json")
    out.parent.mkdir(parents=True, exist_ok=True)

    M0 = [0] * 9
    for i in range(3):
        M0[i] = 1 << i

    hist_pairs = Counter()
    hist_unique = Counter()
    unique_products = set()
    example_by_rank = {}
    for q in range(512):
        for r in range(512):
            qr = tuple(outer_rows(q, r, 9))
            unique_products.add(qr)
            D = add_rows(M0, qr)
            rk = rank_mat(D)
            hist_pairs[rk] += 1
            example_by_rank.setdefault(rk, {"q": q, "r": r, "Delta_rows": D})
    for qr in unique_products:
        hist_unique[rank_mat(add_rows(M0, qr))] += 1

    # Counterexample in a 3x9 block equation: (e1+e2) r + e2 r = e1 r.
    # The first nonzero left factor is not the final q=e1.
    e1 = 1 << 0
    e2 = 1 << 1
    r = 1 << 4  # any nonzero row-side vector
    target_q = e1
    term1_q = e1 ^ e2
    term2_q = e2
    term1 = outer_rows(term1_q, r, 3)
    term2 = outer_rows(term2_q, r, 3)
    target = outer_rows(target_q, r, 3)
    sum12 = add_rows(term1, term2)
    counterexample = {
        "target_left_factor": target_q,
        "target_right_factor": r,
        "term_left_factors": [term1_q, term2_q],
        "term_right_factors": [r, r],
        "sum_equals_target": sum12 == target,
        "term1_left_factor_equals_target": term1_q == target_q,
        "term2_left_factor_equals_target": term2_q == target_q,
        "target_rank": rank_rows(target, 9),
        "term_count": 2,
        "lesson": "A nonminimal or nonsaturated sum of rank-one terms can cancel directions outside the final rank-one column space. Alignment of individual factors follows from tight equality count=rank, not from rank(target)<=1 alone.",
    }

    payload = {
        "schema": "lift_residual_and_rank1_sum_test_v1",
        "field": "F2",
        "M0_rows": M0,
        "pair_distribution_rank_M0_plus_qr": dict(sorted(hist_pairs.items())),
        "unique_rank_le1_matrix_distribution_rank_M0_plus_X": dict(sorted(hist_unique.items())),
        "unique_rank_le1_matrix_count": len(unique_products),
        "examples_by_rank_pairs": example_by_rank,
        "rank1_sum_alignment_counterexample": counterexample,
        "mathematical_consequence": [
            "The peer rank distribution by (q,r) pairs is reproduced: Delta never has rank 0 or 1.",
            "The stronger block statement that every lifted term with nonzero B-block component shares the final q_s direction is false without a saturation/minimality hypothesis.",
            "Tight contraction/domain arguments remain valid when active_count equals matrix rank; they should not be applied to nonsaturated lift block equations merely because the sum has rank at most one.",
        ],
    }
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "pair_distribution": payload["pair_distribution_rank_M0_plus_qr"],
        "unique_distribution": payload["unique_rank_le1_matrix_distribution_rank_M0_plus_X"],
        "counterexample_sum_equals_target": counterexample["sum_equals_target"],
        "term_left_factors": counterexample["term_left_factors"],
        "target_left_factor": counterexample["target_left_factor"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
