#!/usr/bin/env python3
"""E11 Wang-table validation assets.

This script recomputes several load-bearing facts without using the analysis
pool convention that was found wrong:

1. Decode every E11-containing Wang LUT row into a quotient subspace U <= F2^8.
2. For quotient hyperplanes, compare the LUT lower bound with the closed-form
   contraction rank rank(Lambda^T \otimes I_3)=3 rank(Lambda), where Lambda is
   the 3x3 coefficient matrix with deleted (0,0) entry.
3. Validate all known rank-21 E11 core decompositions against the same Wang
   occupancy constraints at length 21, using raw 8-bit core A-masks with
   multiplicity. This is the positive control for the support pipeline.

The script saves a JSON summary under workspace/data/wang_validation/.
"""
from __future__ import annotations

import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, List, Tuple

import numpy as np

S04_SCRIPTS = Path("scripts")
if str(S04_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(S04_SCRIPTS))

from wang_capacity_lazy import rref_basis, unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
POOL_PATH = Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
OUTDIR = Path("data/wang_validation")
OUTDIR.mkdir(parents=True, exist_ok=True)

MASK9 = (1 << 9) - 1


def key_contains_e11(key: int) -> bool:
    d = key & 0xF
    if d == 0:
        return False
    last_row = (key >> (4 + 9 * (d - 1))) & MASK9
    return last_row == 1


def key9_to_basis8(key9: int) -> Tuple[int, ...]:
    """Project an E11-containing full 9-bit RREF basis to quotient F2^8.

    Full bit 0 is the deleted E11 direction. Quotient bit a-1 corresponds to
    full bit a for a=1,...,8. The output is RREF in 8-bit coordinates.
    """
    basis9 = list(unpack_basis(key9))
    raw8: List[int] = []
    for b in basis9:
        if b == 1:
            continue
        q = b
        if q & 1:
            q ^= 1
        q8 = 0
        for bit in range(1, 9):
            if (q >> bit) & 1:
                q8 |= 1 << (bit - 1)
        if q8:
            raw8.append(q8)
    return tuple(rref_basis(raw8, n=8)) if raw8 else tuple()


def quotient_points_from_basis8(basis8: Tuple[int, ...]) -> List[int]:
    pts: List[int] = []
    d = len(basis8)
    for mask in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis8):
            if (mask >> i) & 1:
                v ^= b
        pts.append(v)
    pts.sort()
    return pts


def dot_parity(a: int, b: int) -> int:
    return ((a & b).bit_count() & 1)


def annihilator_basis(basis8: Tuple[int, ...]) -> Tuple[int, ...]:
    """Return all nonzero basis vectors of U^perp in RREF-like order.

    For the dimensions used here this simple enumeration is cheap and avoids
    depending on old helper conventions.
    """
    vecs = [x for x in range(1, 256) if all(dot_parity(x, u) == 0 for u in basis8)]
    # Build a basis from the enumerated nullspace vectors.
    piv = [0] * 8
    out: List[int] = []
    for x in vecs:
        v = x
        for p in range(7, -1, -1):
            if (v >> p) & 1:
                if piv[p]:
                    v ^= piv[p]
                else:
                    piv[p] = v
                    out.append(v)
                    break
    return tuple(rref_basis(out, n=8)) if out else tuple()


def gf2_rank_rows(rows: Iterable[int], n: int) -> int:
    basis = [0] * n
    r = 0
    for x0 in rows:
        x = x0
        while x:
            p = x.bit_length() - 1
            if basis[p]:
                x ^= basis[p]
            else:
                basis[p] = x
                r += 1
                break
    return r


def lambda8_to_matrix_rows(lam: int) -> List[int]:
    """Convert quotient coefficients to a 3x3 Lambda, returned as row bitmasks.

    Full A-index a=3*i+j, a=1..8, maps to quotient bit a-1. Entry (0,0) is 0.
    """
    rows = [0, 0, 0]
    for a in range(1, 9):
        if (lam >> (a - 1)) & 1:
            i, j = divmod(a, 3)
            rows[i] |= 1 << j
    return rows


def build_e11_rows(lut):
    """Decode E11 rows once.

    Returns list of dicts with dim8, lb, basis8, points; and point_to_rows for
    occupancy validation.
    """
    rows = []
    point_to_rows: List[List[int]] = [[] for _ in range(256)]
    for key9, lb in lut.items():
        if not key_contains_e11(key9):
            continue
        b8 = key9_to_basis8(key9)
        pts = quotient_points_from_basis8(b8)
        idx = len(rows)
        rows.append({"key9": int(key9), "dim8": len(b8), "lb": int(lb), "basis8": b8, "points": pts})
        for p in pts:
            point_to_rows[p].append(idx)
    return rows, [np.asarray(x, dtype=np.int32) for x in point_to_rows]


def build_e11_core_tensor() -> np.ndarray:
    T = np.zeros((8, 9, 9), dtype=np.uint8)
    # Core slice s corresponds to full A index a=s+1=3*i+j.
    for s in range(8):
        a = s + 1
        i, j = divmod(a, 3)
        for k in range(3):
            T[s, 3 * j + k, 3 * i + k] = 1
    return T


def reconstruct_core_from_row(row: np.ndarray) -> np.ndarray:
    R = row.shape[0] // 3
    T = np.zeros((8, 9, 9), dtype=np.uint8)
    for t in range(R):
        u = int(row[3 * t]) & 0xFF  # raw core-mask convention
        v = int(row[3 * t + 1])
        w = int(row[3 * t + 2])
        if u == 0 or v == 0 or w == 0:
            continue
        for s in range(8):
            if (u >> s) & 1:
                for b in range(9):
                    if (v >> b) & 1:
                        for c in range(9):
                            if (w >> c) & 1:
                                T[s, b, c] ^= 1
    return T


def validate_pool(rows, point_to_rows):
    pool = np.load(POOL_PATH)
    N, cols = pool.shape
    R = cols // 3
    caps21 = np.asarray([21 - r["lb"] for r in rows], dtype=np.int16)
    nrows = len(rows)
    T_core = build_e11_core_tensor()

    violation_rows = []
    brent_failures = []
    zero_u_hist = Counter()
    distinct_hist = Counter()
    rank_hist = Counter()
    duplicate_hist = Counter()
    u_max = 0
    u_min = 999999
    high_bits_rows = 0

    for row_idx in range(N):
        row = pool[row_idx]
        us = [int(row[3 * t]) for t in range(R)]
        raw_us = [u & 0xFF for u in us]
        u_min = min(u_min, min(us))
        u_max = max(u_max, max(us))
        if any(u & ~0xFF for u in us):
            high_bits_rows += 1
        zero_count = sum(1 for u in raw_us if u == 0)
        zero_u_hist[zero_count] += 1
        distinct_nonzero = len(set(u for u in raw_us if u != 0))
        distinct_hist[distinct_nonzero] += 1
        duplicate_hist[R - distinct_nonzero - zero_count] += 1
        rank_hist[gf2_rank_rows([u for u in raw_us if u != 0], 8)] += 1

        # Brent reconstruction in raw 8-bit convention.
        T_rec = reconstruct_core_from_row(row)
        diff = int(np.sum(T_rec != T_core))
        if diff:
            brent_failures.append({"row": row_idx, "diff": diff})

        counts = np.full(nrows, zero_count, dtype=np.int16)
        for u in raw_us:
            if u:
                idxs = point_to_rows[u]
                if idxs.size:
                    counts[idxs] += 1
        bad = np.nonzero(counts > caps21)[0]
        if bad.size:
            head = []
            for bi in bad[:10]:
                rr = rows[int(bi)]
                head.append({
                    "row_index": int(bi),
                    "dim8": int(rr["dim8"]),
                    "lb": int(rr["lb"]),
                    "cap21": int(caps21[bi]),
                    "occ": int(counts[bi]),
                    "basis8": list(map(int, rr["basis8"])),
                })
            violation_rows.append({"pool_row": row_idx, "violations": int(bad.size), "head": head})

    return {
        "pool_shape": list(pool.shape),
        "terms_per_row": int(R),
        "u_min": int(u_min),
        "u_max": int(u_max),
        "rows_with_u_high_bits": int(high_bits_rows),
        "zero_u_hist": dict(sorted((int(k), int(v)) for k, v in zero_u_hist.items())),
        "distinct_nonzero_u_hist": dict(sorted((int(k), int(v)) for k, v in distinct_hist.items())),
        "duplicate_nonzero_count_hist": dict(sorted((int(k), int(v)) for k, v in duplicate_hist.items())),
        "span_rank_hist": dict(sorted((int(k), int(v)) for k, v in rank_hist.items())),
        "brent_failure_count": len(brent_failures),
        "brent_failures_head": brent_failures[:10],
        "wang_violation_row_count": len(violation_rows),
        "wang_violations_head": violation_rows[:5],
    }


def main():
    t0 = time.time()
    print(f"Loading LUT: {LUT_PATH}")
    lut, meta = load_lut(LUT_PATH)
    print(f"LUT entries: {len(lut)}")

    print("Decoding E11-containing rows...")
    rows, point_to_rows = build_e11_rows(lut)
    print(f"E11 rows: {len(rows)}")

    dim_hist = Counter(r["dim8"] for r in rows)
    lb_hist = Counter(r["lb"] for r in rows)
    cap19_hist = Counter(19 - r["lb"] for r in rows if 19 - r["lb"] < 19)
    cap21_hist = Counter(21 - r["lb"] for r in rows if 21 - r["lb"] < 21)

    print("Running codim-1 closed-form rank comparison...")
    codim1 = []
    failures = []
    dist = Counter()
    for idx, r in enumerate(rows):
        if r["dim8"] != 7:
            continue
        ann = annihilator_basis(r["basis8"])
        if len(ann) != 1:
            failures.append({"row_index": idx, "reason": "annihilator_dim", "ann": list(ann)})
            continue
        lam = ann[0]
        rank_lam = gf2_rank_rows(lambda8_to_matrix_rows(lam), 3)
        exact_lb = 3 * rank_lam
        dist[(rank_lam, exact_lb, r["lb"], 19 - r["lb"])] += 1
        if exact_lb != r["lb"]:
            failures.append({
                "row_index": idx,
                "basis8": list(map(int, r["basis8"])),
                "lambda8": int(lam),
                "rank_lambda": int(rank_lam),
                "exact_lb": int(exact_lb),
                "lut_lb": int(r["lb"]),
            })
        codim1.append({"lambda8": int(lam), "rank_lambda": int(rank_lam), "lb": int(r["lb"]), "cap19": int(19 - r["lb"])})
    print(f"  codim1 rows: {len(codim1)}, failures: {len(failures)}")

    print("Validating rank-21 pool against raw-mask Brent and Wang constraints...")
    pool_summary = validate_pool(rows, point_to_rows)
    print(json.dumps({
        "brent_failure_count": pool_summary["brent_failure_count"],
        "wang_violation_row_count": pool_summary["wang_violation_row_count"],
        "zero_u_hist": pool_summary["zero_u_hist"],
        "distinct_nonzero_u_hist": pool_summary["distinct_nonzero_u_hist"],
        "span_rank_hist": pool_summary["span_rank_hist"],
    }, indent=2, sort_keys=True))

    out = {
        "status": "ok",
        "elapsed_sec": time.time() - t0,
        "lut_entries": len(lut),
        "e11_row_count": len(rows),
        "dimension_hist_dim8": dict(sorted((int(k), int(v)) for k, v in dim_hist.items())),
        "lb_hist_all_e11": dict(sorted((int(k), int(v)) for k, v in lb_hist.items())),
        "cap19_hist": dict(sorted((int(k), int(v)) for k, v in cap19_hist.items())),
        "cap21_hist": dict(sorted((int(k), int(v)) for k, v in cap21_hist.items())),
        "codim1_closed_form": {
            "rows": len(codim1),
            "failure_count": len(failures),
            "failures_head": failures[:10],
            "distribution_rank_exactlb_lutlb_cap19": {str(k): int(v) for k, v in sorted(dist.items(), key=lambda kv: kv[0])},
        },
        "rank21_pool_positive_control": pool_summary,
    }

    outpath = OUTDIR / "e11_wang_validation_and_caps.json"
    with open(outpath, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(f"Saved {outpath}")


if __name__ == "__main__":
    main()
