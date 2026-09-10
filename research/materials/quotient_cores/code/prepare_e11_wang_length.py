#!/usr/bin/env python3
"""Prepare E11 quotient Wang constraints for arbitrary length N in E11WANG1.

This is the same decoder as prepare_e11_wang_constraints.py but parameterized by
length.  For a putative length-N E11 core decomposition, every E11-containing
restriction row gives occupancy <= N - LB(row).  We usually keep rows with cap
<= max_cap because those drive search and propagation.
"""
from __future__ import annotations

import argparse, json, struct, sys, time
from collections import Counter
from pathlib import Path

S04_SCRIPTS = Path("scripts")
if str(S04_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(S04_SCRIPTS))
from wang_capacity_lazy import rref_basis, unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = Path("data/wang_native/e11_ladder")
MASK9 = (1 << 9) - 1
MAGIC = b"E11WANG1"


def contains_e11(key: int) -> bool:
    d = key & 0xF
    return d > 0 and (((key >> (4 + 9 * (d - 1))) & MASK9) == 1)


def key9_to_basis8(key9: int):
    raw = []
    for b in unpack_basis(key9):
        if b == 1:
            continue
        q = int(b)
        if q & 1:
            q ^= 1
        q8 = 0
        for bit in range(1, 9):
            if (q >> bit) & 1:
                q8 |= 1 << (bit - 1)
        if q8:
            raw.append(q8)
    return tuple(rref_basis(raw, n=8)) if raw else tuple()


def mask_from_basis8(basis8):
    words = [0, 0, 0, 0]
    d = len(basis8)
    for m in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis8):
            if (m >> i) & 1:
                v ^= int(b)
        if v:
            words[v >> 6] |= 1 << (v & 63)
    return tuple(words)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--length", type=int, required=True)
    ap.add_argument("--max-cap", type=int, default=5)
    ap.add_argument("--outdir", type=Path, default=OUTDIR)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    lut, _ = load_lut(LUT_PATH)
    rows = []
    cap_hist_all = Counter()
    dim_hist_written = Counter()
    cap_hist_written = Counter()
    all_e11 = 0
    for key9, lb0 in lut.items():
        if not contains_e11(int(key9)):
            continue
        all_e11 += 1
        lb = int(lb0)
        cap = args.length - lb
        dim8 = (int(key9) & 0xF) - 1
        cap_hist_all[cap] += 1
        if cap < 0 or cap > args.max_cap:
            continue
        basis8 = key9_to_basis8(int(key9))
        words = mask_from_basis8(basis8)
        rows.append((cap, dim8, words))
        cap_hist_written[cap] += 1
        dim_hist_written[dim8] += 1

    bin_path = args.outdir / f"e11_wang_cap{args.max_cap}_len{args.length}.bin"
    with open(bin_path, "wb") as f:
        f.write(MAGIC)
        f.write(struct.pack("<I", len(rows)))
        for cap, dim8, words in rows:
            f.write(struct.pack("<BBHQQQQ", cap, dim8, 0, *words))
    meta = {
        "status": "ok",
        "source_lut": str(LUT_PATH),
        "length": args.length,
        "max_cap": args.max_cap,
        "all_e11_rows": all_e11,
        "rows_written": len(rows),
        "cap_hist_all_e11_for_length": dict(sorted((int(k), int(v)) for k, v in cap_hist_all.items())),
        "cap_hist_written": dict(sorted((int(k), int(v)) for k, v in cap_hist_written.items())),
        "dim_hist_written": dict(sorted((int(k), int(v)) for k, v in dim_hist_written.items())),
        "binary_path": str(bin_path),
        "elapsed_sec": time.time() - t0,
    }
    meta_path = bin_path.with_suffix(".meta.json")
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    print(json.dumps(meta, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
