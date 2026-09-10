#!/usr/bin/env python3
"""Stream full A-side Wang occupation rows into WANG512 format.

The older generator accumulated all rows before writing.  This version first
counts selected LUT rows, then streams masks, so it can write the complete
full-tensor row family used by pivot-fixed occupation models.
"""
from __future__ import annotations

import argparse
import json
import struct
import sys
import time
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


def points_mask_from_basis(basis, valid=None):
    d = len(basis)
    words = [0] * 8
    npts = 0
    for m in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis):
            if (m >> i) & 1:
                v ^= int(b)
        if valid is None or v in valid:
            words[v >> 6] |= 1 << (v & 63)
            npts += 1
    return npts, words


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--length", type=int, default=20)
    ap.add_argument("--max-cap", type=int, default=19)
    ap.add_argument("--max-dim", type=int, default=9)
    ap.add_argument("--min-rank", type=int, default=0)
    ap.add_argument("--outdir", type=Path, default=OUTDIR)
    ap.add_argument("--tag", default="stream")
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
    valid_arg = None if args.min_rank == 0 else valid

    nrows = 0
    cap_hist = Counter()
    dim_hist = Counter()
    all_cap_hist = Counter()
    skipped_empty = 0
    count_t0 = time.time()
    for key9, lb0 in lut.items():
        lb = int(lb0)
        cap = args.length - lb
        dim = int(key9) & 0xF
        all_cap_hist[cap] += 1
        if cap < 0 or cap > args.max_cap or dim > args.max_dim:
            continue
        if dim == 0:
            skipped_empty += 1
            continue
        # For all nonzero directions every nonzero subspace has a nonempty row.
        # For rank-restricted rows we must test whether a valid point occurs.
        if args.min_rank == 0:
            nrows += 1
            cap_hist[cap] += 1
            dim_hist[dim] += 1
        else:
            basis = list(unpack_basis(int(key9)))
            npts, _ = points_mask_from_basis(basis, valid_arg)
            if npts:
                nrows += 1
                cap_hist[cap] += 1
                dim_hist[dim] += 1
            else:
                skipped_empty += 1
    count_elapsed = time.time() - count_t0

    suffix = f"rank{args.min_rank}" if args.min_rank else "all"
    bin_path = args.outdir / f"full_wang512_cap{args.max_cap}_len{args.length}_{suffix}_dim{args.max_dim}_{args.tag}.bin"
    write_t0 = time.time()
    written = 0
    with open(bin_path, "wb", buffering=1024 * 1024) as f:
        f.write(MAGIC)
        f.write(struct.pack("<I", nrows))
        for key9, lb0 in lut.items():
            lb = int(lb0)
            cap = args.length - lb
            dim = int(key9) & 0xF
            if cap < 0 or cap > args.max_cap or dim > args.max_dim or dim == 0:
                continue
            basis = list(unpack_basis(int(key9)))
            npts, words = points_mask_from_basis(basis, valid_arg)
            if npts == 0:
                continue
            f.write(struct.pack("<BBH", cap, dim, 0))
            for w in words:
                f.write(struct.pack("<Q", w))
            written += 1
    write_elapsed = time.time() - write_t0

    meta = {
        "status": "ok" if written == nrows else "row_count_mismatch",
        "source_lut": str(LUT),
        "length": args.length,
        "max_cap": args.max_cap,
        "max_dim": args.max_dim,
        "min_rank": args.min_rank,
        "valid_points": len(valid),
        "rank_hist_all_points": dict(sorted((int(k), int(v)) for k, v in rank_hist.items())),
        "rows_counted": nrows,
        "rows_written": written,
        "cap_hist_written": dict(sorted((int(k), int(v)) for k, v in cap_hist.items())),
        "dim_hist_written": dict(sorted((int(k), int(v)) for k, v in dim_hist.items())),
        "all_lut_cap_hist_for_length": dict(sorted((int(k), int(v)) for k, v in all_cap_hist.items())),
        "skipped_empty_rows": skipped_empty,
        "binary_path": str(bin_path),
        "expected_size_bytes": 12 + 68 * nrows,
        "actual_size_bytes": bin_path.stat().st_size,
        "format": "WANG512\\x01; uint32 rows; repeated cap uint8, dim uint8, reserved uint16, mask[8] uint64 little-endian",
        "count_elapsed_sec": count_elapsed,
        "write_elapsed_sec": write_elapsed,
        "elapsed_sec": time.time() - t0,
    }
    meta_path = bin_path.with_suffix(".meta.json")
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    print(json.dumps(meta, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
