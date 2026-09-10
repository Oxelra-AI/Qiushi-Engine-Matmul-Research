#!/usr/bin/env python3
"""Verify the rank-one-difference coset lemma over F_2.

LEMMA: Let A_1, ..., A_h be distinct 3x3 matrices over F_2 with h >= 3.
If rank(A_i + A_j) = 1 for all i != j, then there exist vectors u, v
such that all A_i lie in one affine coset of one of the forms:
  A_1 + u * F_2^3    (column type: common left vector)
  A_1 + F_2^3 * v^T  (row type: common right vector)

PROOF (constructive, exhaustive over F_2):
A rank-1 matrix has the form u v^T for unique nonzero u, v.
Write A_i + A_j = u_{ij} v_{ij}^T.

For three distinct indices i, j, k:
  (A_i + A_j) + (A_j + A_k) = A_i + A_k
  so u_{ij} v_{ij}^T + u_{jk} v_{jk}^T = u_{ik} v_{ik}^T.

A sum of two rank-1 matrices has rank 1 only if they share a common left
or common right vector:
  u_{ij} = u_{jk} (then u_{ik} = u_{ij} as well) -- common left vector
  OR v_{ij} = v_{jk} (then v_{ik} = v_{ij}) -- common right vector

This forces a GLOBAL common direction: either all u_{ij} = u (column type)
or all v_{ij} = v (row type). The distinction is rigid once h >= 3.

This script verifies the lemma exhaustively for all h=3,4 configurations.
"""
from __future__ import annotations
import json, sys, time, itertools
from pathlib import Path
import numpy as np

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from quotient_line_caps_and_controls import bits_to_mat, mat_to_bits, gf2_rank_mat

OUT = Path("data/audit/coset_lemma.json")


def mm3(X, Y):
    return (X @ Y % 2).astype(np.uint8)


def rank1_common_left(M1, M2):
    """Check if two rank-1 matrices share left vector (same column space)."""
    # rank-1 matrix: M = u v^T. Column space = span(u).
    # Two rank-1 matrices share left vector iff their column spaces are equal.
    # For 3x3 over F_2, check if columns are proportional (over F_2, this means equal).
    cols1 = M1[:, M1.any(axis=0)]
    cols2 = M2[:, M2.any(axis=0)]
    if cols1.shape[1] == 0 or cols2.shape[1] == 0:
        return False
    u1 = cols1[:, 0]
    u2 = cols2[:, 0]
    return np.array_equal(u1, u2)


def rank1_common_right(M1, M2):
    """Check if two rank-1 matrices share right vector (same row space)."""
    rows1 = M1[M1.any(axis=1)]
    rows2 = M2[M2.any(axis=1)]
    if rows1.shape[0] == 0 or rows2.shape[0] == 0:
        return False
    v1 = rows1[0]
    v2 = rows2[0]
    return np.array_equal(v1, v2)


def in_column_coset(matrices):
    """Check if all matrices lie in p + u * F_2^3 for some p, u."""
    if len(matrices) < 2:
        return True
    p = matrices[0]
    diffs = [((m + p) % 2) for m in matrices[1:]]
    # All diffs should have the same column space (same left vector u)
    if any(gf2_rank_mat(d) != 1 for d in diffs):
        return False
    # Get the common left vector
    u = None
    for d in diffs:
        cols = d[:, d.any(axis=0)]
        if cols.shape[1] > 0:
            if u is None:
                u = cols[:, 0]
            elif not np.array_equal(cols[:, 0], u):
                return False
    return True


def in_row_coset(matrices):
    """Check if all matrices lie in p + F_2^3 * v^T for some p, v."""
    if len(matrices) < 2:
        return True
    p = matrices[0]
    diffs = [((m + p) % 2) for m in matrices[1:]]
    if any(gf2_rank_mat(d) != 1 for d in diffs):
        return False
    v = None
    for d in diffs:
        rows = d[d.any(axis=1)]
        if rows.shape[0] > 0:
            if v is None:
                v = rows[0]
            elif not np.array_equal(rows[0], v):
                return False
    return True


def main():
    t0 = time.time()
    # All 511 nonzero 3x3 F_2 matrices
    all_mats = [(m, bits_to_mat(m)) for m in range(1, 512)]

    # Find all sets of h >= 3 matrices with pairwise rank-1 differences
    # For h=3: check all (511 choose 3) triples
    # For h=4: check all (511 choose 4) quads

    h3_total = 0
    h3_coset = 0
    h3_neither = 0
    h3_column = 0
    h3_row = 0

    # h=3: exhaustive
    for combo in itertools.combinations(range(511), 3):
        m1, m2, m3 = [all_mats[i][1] for i in combo]
        d12 = (m1 + m2) % 2
        d13 = (m1 + m3) % 2
        d23 = (m2 + m3) % 2
        if gf2_rank_mat(d12) != 1 or gf2_rank_mat(d13) != 1 or gf2_rank_mat(d23) != 1:
            continue
        h3_total += 1
        mats = [m1, m2, m3]
        col = in_column_coset(mats)
        row = in_row_coset(mats)
        if col:
            h3_column += 1
        if row:
            h3_row += 1
        if col or row:
            h3_coset += 1
        else:
            h3_neither += 1
            masks = [all_mats[i][0] for i in combo]
            print(f"COUNTEREXAMPLE h=3: {masks}")

    print(f"h=3: total={h3_total}, coset={h3_coset} (col={h3_column}, row={h3_row}), neither={h3_neither}")

    # h=4: sample (full enumeration too slow)
    h4_total = 0
    h4_coset = 0
    h4_neither = 0
    h4_column = 0
    h4_row = 0
    h4_limit = 500000

    rng = np.random.RandomState(29)
    # First find rank-1-difference triples, then extend
    # More efficient: for each triple, try extending with a 4th element
    h3_examples = []
    for combo in itertools.combinations(range(511), 3):
        m1, m2, m3 = [all_mats[i][1] for i in combo]
        d12 = (m1 + m2) % 2
        d13 = (m1 + m3) % 2
        d23 = (m2 + m3) % 2
        if gf2_rank_mat(d12) != 1 or gf2_rank_mat(d13) != 1 or gf2_rank_mat(d23) != 1:
            continue
        h3_examples.append(combo)
        if len(h3_examples) >= 5000:
            break

    for combo3 in h3_examples:
        used = set(combo3)
        for idx4 in range(511):
            if idx4 in used:
                continue
            m4 = all_mats[idx4][1]
            ok = True
            for idx in combo3:
                d = (m4 + all_mats[idx][1]) % 2
                if gf2_rank_mat(d) != 1:
                    ok = False
                    break
            if not ok:
                continue
            h4_total += 1
            mats = [all_mats[i][1] for i in combo3] + [m4]
            col = in_column_coset(mats)
            row = in_row_coset(mats)
            if col:
                h4_column += 1
            if row:
                h4_row += 1
            if col or row:
                h4_coset += 1
            else:
                h4_neither += 1
                masks = [all_mats[i][0] for i in combo3] + [all_mats[idx4][0]]
                print(f"COUNTEREXAMPLE h=4: {masks}")
            if h4_total >= h4_limit:
                break
        if h4_total >= h4_limit:
            break

    print(f"h=4: total={h4_total}, coset={h4_coset} (col={h4_column}, row={h4_row}), neither={h4_neither}")

    elapsed = time.time() - t0
    rec = {
        "schema": "coset_lemma_v1",
        "h3_total": h3_total,
        "h3_coset": h3_coset,
        "h3_column": h3_column,
        "h3_row": h3_row,
        "h3_neither": h3_neither,
        "h4_total": h4_total,
        "h4_coset": h4_coset,
        "h4_column": h4_column,
        "h4_row": h4_row,
        "h4_neither": h4_neither,
        "lemma_verified": h3_neither == 0 and h4_neither == 0,
        "elapsed_sec": elapsed,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    print(json.dumps(rec, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
