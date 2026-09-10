#!/usr/bin/env python3
"""Prepare full-tensor Wang constraints in the WANG512 format.

The old analysis prepare_full_tensor_wang.py accidentally wrote only four 64-bit
words after saying full masks need 512 bits.  This script always writes eight
64-bit words and can keep all 511 nonzero A-functionals or a rank-restricted
subset.  The row bound is occupancy <= length - LB(U), using Wang's LUT for the
restriction subspace U <= F2^9.
"""
from __future__ import annotations

import argparse, json, struct, sys, time
from collections import Counter
from pathlib import Path

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = Path("data/wang_native/full_tensor")
MAGIC = b"WANG512\x01"


def gf2_rank_rows(rows, n=3):
    basis = [0] * n
    r = 0
    for x0 in rows:
        x = int(x0)
        while x:
            p = x.bit_length() - 1
            if basis[p]:
                x ^= basis[p]
            else:
                basis[p] = x
                r += 1
                break
    return r


def matrix_rank_3x3(a: int) -> int:
    rows = [0, 0, 0]
    for idx in range(9):
        if (a >> idx) & 1:
            i, j = divmod(idx, 3)
            rows[i] |= 1 << j
    return gf2_rank_rows(rows, 3)


def points_from_basis(basis):
    pts = []
    d = len(basis)
    for m in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis):
            if (m >> i) & 1:
                v ^= int(b)
        pts.append(v)
    return pts


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--length", type=int, default=20)
    ap.add_argument("--max-cap", type=int, default=5)
    ap.add_argument("--max-dim", type=int, default=9)
    ap.add_argument("--min-rank", type=int, default=0)
    ap.add_argument("--outdir", type=Path, default=OUTDIR)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    lut, _ = load_lut(LUT)
    rank_hist = Counter()
    valid = set()
    for a in range(1, 512):
        r = matrix_rank_3x3(a)
        rank_hist[r] += 1
        if r >= args.min_rank:
            valid.add(a)

    rows = []
    cap_hist = Counter()
    dim_hist = Counter()
    n_all_rows_by_cap = Counter()
    for key9, lb0 in lut.items():
        lb = int(lb0)
        cap = args.length - lb
        dim = int(key9) & 0xF
        n_all_rows_by_cap[cap] += 1
        if cap < 0 or cap > args.max_cap or dim > args.max_dim:
            continue
        basis = list(unpack_basis(int(key9)))
        pts = [p for p in points_from_basis(basis) if p in valid]
        if not pts:
            continue
        words = [0] * 8
        for p in pts:
            words[p >> 6] |= 1 << (p & 63)
        rows.append((cap, dim, len(pts), words))
        cap_hist[cap] += 1
        dim_hist[dim] += 1

    suffix = f"rank{args.min_rank}" if args.min_rank else "all"
    bin_path = args.outdir / f"full_wang512_cap{args.max_cap}_len{args.length}_{suffix}_dim{args.max_dim}.bin"
    with open(bin_path, "wb") as f:
        f.write(MAGIC)
        f.write(struct.pack("<I", len(rows)))
        for cap, dim, _npts, words in rows:
            f.write(struct.pack("<BBH", cap, dim, 0))
            for w in words:
                f.write(struct.pack("<Q", w))

    meta = {
        "status": "ok",
        "source_lut": str(LUT),
        "length": args.length,
        "max_cap": args.max_cap,
        "max_dim": args.max_dim,
        "min_rank": args.min_rank,
        "valid_points": len(valid),
        "rank_hist_all_points": dict(sorted((int(k), int(v)) for k, v in rank_hist.items())),
        "rows_written": len(rows),
        "cap_hist_written": dict(sorted((int(k), int(v)) for k, v in cap_hist.items())),
        "dim_hist_written": dict(sorted((int(k), int(v)) for k, v in dim_hist.items())),
        "all_lut_cap_hist_for_length": dict(sorted((int(k), int(v)) for k, v in n_all_rows_by_cap.items())),
        "binary_path": str(bin_path),
        "format": "WANG512\\x01; cap uint8, dim uint8, reserved uint16, mask[8] uint64 little-endian",
        "elapsed_sec": time.time() - t0,
    }
    meta_path = bin_path.with_suffix(".meta.json")
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    print(json.dumps(meta, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
