#!/usr/bin/env python3
"""Fast bitset replay of minimum inconsistent shadow-trace subsets for an E11 A-support.

This is a verification companion to e11_shadow_filter.py. It uses Python-integer
Gaussian elimination over F2 to test all subsets of tight rank-9 contractions.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from pathlib import Path
from typing import List, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
import e11_shadow_filter as shadow  # noqa: E402


def row_to_int(row: List[int]) -> int:
    x = 0
    for i, b in enumerate(row):
        if int(b) & 1:
            x |= 1 << i
    return x


def rank_int(rows: List[int]) -> int:
    basis = {}
    r = 0
    for x0 in rows:
        x = int(x0)
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                r += 1
                break
    return r


def consistent(coeff_rows: List[int], rhs: List[int], nvars: int) -> Tuple[bool, int, int]:
    r_coeff = rank_int(coeff_rows)
    aug_rows = [row | ((int(b) & 1) << nvars) for row, b in zip(coeff_rows, rhs)]
    r_aug = rank_int(aug_rows)
    return r_coeff == r_aug, r_coeff, r_aug


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--support", required=True)
    ap.add_argument("--max-size", type=int, default=8)
    ap.add_argument("--transpose-coeff", action="store_true")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()

    t0 = time.time()
    support = shadow.parse_support(args.support)
    nvars = 9 * len(support)
    tensor_rows, tensor_rhs = shadow.build_tensor_shadow_rows(support)
    tensor_ints = [row_to_int(r) for r in tensor_rows]
    ok0, r0, r0a = consistent(tensor_ints, tensor_rhs, nvars)
    tight = shadow.tight_rank9_lambdas(support)
    trace_by_lambda = {}
    for lam in tight:
        tr, tb = shadow.add_trace_rows(support, [lam], transpose_coeff=args.transpose_coeff)
        trace_by_lambda[int(lam)] = ([row_to_int(r) for r in tr], list(tb))
    all_trace_rows = []
    all_trace_rhs = []
    for lam in tight:
        rr, bb = trace_by_lambda[lam]
        all_trace_rows.extend(rr); all_trace_rhs.extend(bb)
    ok_full, r_full, r_full_aug = consistent(tensor_ints + all_trace_rows, tensor_rhs + all_trace_rhs, nvars)
    min_found = None
    checked_by_size = {}
    examples = []
    total_bad = 0
    for k in range(1, min(args.max_size, len(tight)) + 1):
        checked = 0
        bad = []
        for comb in itertools.combinations(tight, k):
            checked += 1
            rows = list(tensor_ints)
            rhs = list(tensor_rhs)
            for lam in comb:
                rr, bb = trace_by_lambda[lam]
                rows.extend(rr); rhs.extend(bb)
            ok, _, _ = consistent(rows, rhs, nvars)
            if not ok:
                bad.append(list(comb))
        checked_by_size[str(k)] = checked
        if bad:
            min_found = k
            examples = bad[:20]
            total_bad = len(bad)
            break
    result = {
        "support": support,
        "support_size": len(support),
        "nvars": nvars,
        "tight_rank9_lambdas": tight,
        "tight_rank9_count": len(tight),
        "tensor_consistent": ok0,
        "tensor_rank_aug": [r0, r0a],
        "full_shadow_consistent": ok_full,
        "full_shadow_rank_aug": [r_full, r_full_aug],
        "max_size_checked": args.max_size,
        "min_inconsistent_size": min_found,
        "inconsistent_examples_at_min": examples,
        "total_inconsistent_at_min": total_bad,
        "checked_by_size": checked_by_size,
        "coeff_convention": "coeff[j,i]=Lambda^{-1}[j,i] (M_lambda=Lambda^T tensor I3)" if not args.transpose_coeff else "TRANSPOSED comparison convention",
        "elapsed_sec": time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": "ok",
        "out": str(args.out),
        "tight_rank9_count": len(tight),
        "full_shadow_consistent": ok_full,
        "full_rank_aug": [r_full, r_full_aug],
        "min_inconsistent_size": min_found,
        "total_inconsistent_at_min": total_bad,
        "examples": examples[:2],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
