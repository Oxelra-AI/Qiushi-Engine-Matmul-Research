#!/usr/bin/env python3
r"""analysis: random exact controls for corrected trace row direction.

For the fixed near-miss A-support, randomly choose nonzero B/C vectors and build
T' = sum_s a_s \otimes b_s \otimes c_s.  The same corrected row builder must
accept the known matrices X_s=b_s c_s^T for every saturated rank-9 contraction
of T' relative to this support.  This is a direct end-to-end check of tensor
assembly, contraction, inverse, vectorization, and trace coefficient direction.
"""
from __future__ import annotations

import json
import random
import sys
from collections import Counter
from pathlib import Path
from typing import List, Sequence

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import contraction_matrix, mat_rank_f2  # noqa: E402
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from corrected_trace_instrument import (  # noqa: E402
    NEAR_MISS,
    direct_dual_basis_value,
    mask_to_col,
    outer_from_masks,
    trace_functional_correct,
    trace_functional_wrong,
)

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/corrected_trace"


def random_nonzero_mask(rng: random.Random, n: int = 9) -> int:
    return rng.randrange(1, 1 << n)


def tensor_from_masks(A: Sequence[int], B: Sequence[int], C: Sequence[int]) -> np.ndarray:
    T = np.zeros((8, 9, 9), dtype=np.uint8)
    for a, bmask, cmask in zip(A, B, C):
        aa = int(a)
        while aa:
            lba = aa & -aa
            i = lba.bit_length() - 1
            X = outer_from_masks(int(bmask), int(cmask), 9)
            T[i] ^= X
            aa ^= lba
    return T


def trial(seed: int, A: Sequence[int]) -> dict:
    rng = random.Random(seed)
    B = [random_nonzero_mask(rng) for _ in A]
    C = [random_nonzero_mask(rng) for _ in A]
    T = tensor_from_masks(A, B, C)
    rank_hist = Counter()
    sat_rank9 = []
    correct_failures = []
    wrong_disagreements = 0
    wrong_failures = 0
    for q in range(1, 256):
        M = contraction_matrix(T, q)
        rk = mat_rank_f2(M)
        rank_hist[int(rk)] += 1
        I = [s for s, a in enumerate(A) if ((int(a) & q).bit_count() & 1)]
        if rk == 9 and len(I) == 9:
            sat_rank9.append(q)
            Minv = gf2_mat_inv(M)
            assert Minv is not None
            for s in I:
                X = outer_from_masks(B[s], C[s], 9)
                direct = direct_dual_basis_value(Minv, B[s], C[s], 9)
                corr = trace_functional_correct(Minv, X)
                wrong = trace_functional_wrong(Minv, X)
                if direct != 1 or corr != 1 or corr != direct:
                    correct_failures.append({"q": q, "s": s, "direct": int(direct), "correct": int(corr)})
                if wrong != direct:
                    wrong_disagreements += 1
                if wrong != 1:
                    wrong_failures += 1
    return {
        "seed": seed,
        "rank_histogram": {str(k): v for k, v in sorted(rank_hist.items())},
        "saturated_rank9_count": len(sat_rank9),
        "saturated_rank9_qs": sat_rank9[:20],
        "correct_failures": correct_failures[:10],
        "correct_failure_count": len(correct_failures),
        "wrong_disagreements": wrong_disagreements,
        "wrong_failures_against_required_one": wrong_failures,
    }


def main() -> None:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    records: List[dict] = []
    for seed in range(510100, 510140):
        rec = trial(seed, NEAR_MISS)
        records.append(rec)
    result = {
        "schema": "random_corrected_trace_control_v1",
        "field": "F2",
        "support": list(NEAR_MISS),
        "trials": len(records),
        "total_saturated_rank9": sum(r["saturated_rank9_count"] for r in records),
        "total_correct_failures": sum(r["correct_failure_count"] for r in records),
        "total_wrong_disagreements": sum(r["wrong_disagreements"] for r in records),
        "records_with_saturated_rank9": sum(1 for r in records if r["saturated_rank9_count"]),
        "records": records,
        "meaning": "For exact randomly generated decompositions with the same A-support, corrected trace rows agree with the known X_s on every saturated rank-9 contraction found; the old analysis pairing often disagrees.",
    }
    out = OUTDIR / "random_corrected_trace_control.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "trials": result["trials"],
        "records_with_saturated_rank9": result["records_with_saturated_rank9"],
        "total_saturated_rank9": result["total_saturated_rank9"],
        "total_correct_failures": result["total_correct_failures"],
        "total_wrong_disagreements": result["total_wrong_disagreements"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
