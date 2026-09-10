#!/usr/bin/env python3
"""Prepare Wang constraint binaries for arbitrary quotient pivots.

Generalizes the E11-specific preparation to any pivot value.
Output: E11WANG1 format (256-bit masks, 255 quotient points).

The generator is target-aware.  If a containing Wang row has cap = target - LB < 0,
that row alone proves the target impossible; such rows are now recorded explicitly
instead of being silently skipped.  Current rank-2/rank-3 quotient n=19 instances
are expected to have no negative-cap rows, but proof-facing regeneration should
always preserve this information.
"""
from __future__ import annotations

import argparse
import json
import os
import struct
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
MAGIC = b"E11WANG1"


def in_span(point: int, basis_vecs: Sequence[int]) -> bool:
    x = int(point)
    for b in sorted((int(v) for v in basis_vecs if v), key=lambda v: -v.bit_length()):
        if x == 0:
            return True
        hb = b.bit_length() - 1
        if (x >> hb) & 1:
            x ^= b
    return x == 0


def quotient_project(a: int, pivot: int) -> int:
    if a == 0 or a == pivot:
        return 0
    h = pivot.bit_length() - 1
    if (a >> h) & 1:
        a ^= pivot
    low = a & ((1 << h) - 1)
    high = (a >> (h + 1)) << h
    return low | high


def subspace_quotient_points(basis: Sequence[int], pivot: int) -> set[int]:
    d = len(basis)
    qpts: set[int] = set()
    for m in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis):
            if (m >> i) & 1:
                v ^= int(b)
        qp = quotient_project(v, pivot)
        if qp > 0:
            qpts.add(qp)
    return qpts


def words_from_points(qpts: Iterable[int]) -> tuple[int, int, int, int]:
    words = [0, 0, 0, 0]
    for p in qpts:
        if p < 1 or p > 255:
            raise ValueError(f"quotient point out of range: {p}")
        words[p >> 6] |= 1 << (p & 63)
    return tuple(words)  # type: ignore[return-value]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot", type=int, required=True, help="9-bit pivot value")
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--max-cap", type=int, default=18)
    ap.add_argument("--outdir", type=str, default=None)
    ap.add_argument("--name", type=str, default=None)
    ap.add_argument("--stop-on-negative", action="store_true",
                    help="write metadata and no ordinary binary if any negative-cap row is present")
    args = ap.parse_args()

    pivot = int(args.pivot)
    target = int(args.target)

    outdir = Path(args.outdir) if args.outdir else SESSION / "workspace/data/wang_native/quotient_binaries"
    outdir.mkdir(parents=True, exist_ok=True)

    name = args.name or f"quotient_p{pivot}_n{target}_cap{args.max_cap}"

    t0 = time.time()
    print("Loading LUT...")
    lut, lut_meta = load_lut(LUT_PATH)
    print(f"  LUT entries: {len(lut)}")

    rows: list[tuple[int, int, tuple[int, int, int, int]]] = []
    total_containing = 0
    cap_hist: Counter[int] = Counter()
    lb_hist: Counter[int] = Counter()
    dim_hist: Counter[int] = Counter()
    skipped: Counter[str] = Counter()
    negative_head: list[dict] = []

    for key9, lb0 in lut.items():
        key9_int = int(key9)
        basis = list(unpack_basis(key9_int))
        if not in_span(pivot, basis):
            continue
        total_containing += 1
        lb = int(lb0)
        cap = target - lb
        dim8 = len(basis) - 1  # quotient dimension

        cap_hist[cap] += 1
        lb_hist[lb] += 1
        dim_hist[dim8] += 1

        if cap < 0:
            skipped["negative_cap"] += 1
            if len(negative_head) < 20:
                negative_head.append({
                    "file_key9": key9_int,
                    "basis9": [int(x) for x in basis],
                    "lb": lb,
                    "cap": cap,
                    "dim9": len(basis),
                    "dim8": dim8,
                })
            continue
        if cap > args.max_cap:
            skipped["cap_above_max"] += 1
            continue
        if cap >= target:
            skipped["cap_at_least_target"] += 1
            continue

        qpts = subspace_quotient_points(basis, pivot)
        if not qpts:
            skipped["empty_projected_subspace"] += 1
            continue

        rows.append((cap, dim8, words_from_points(qpts)))

    status = "ok"
    if skipped.get("negative_cap", 0):
        status = "immediate_impossibility_by_negative_cap"

    bin_path = outdir / f"{name}.bin"
    wrote_binary = not (args.stop_on_negative and skipped.get("negative_cap", 0))
    if wrote_binary:
        with open(bin_path, "wb") as f:
            f.write(MAGIC)
            f.write(struct.pack("<I", len(rows)))
            for cap, dim8, words in rows:
                f.write(struct.pack("<BBHQQQQ", int(cap), int(dim8), 0, *[int(w) for w in words]))

    meta = {
        "status": status,
        "pivot": pivot,
        "target": target,
        "max_cap": int(args.max_cap),
        "total_containing_rows": total_containing,
        "rows_written": len(rows) if wrote_binary else 0,
        "would_write_rows_without_negative_stop": len(rows),
        "binary_written": wrote_binary,
        "cap_hist_all": dict(sorted((int(k), int(v)) for k, v in cap_hist.items())),
        "lb_hist_all": dict(sorted((int(k), int(v)) for k, v in lb_hist.items())),
        "dim_hist_all": dict(sorted((int(k), int(v)) for k, v in dim_hist.items())),
        "skipped": dict(sorted((str(k), int(v)) for k, v in skipped.items())),
        "negative_cap_count": int(skipped.get("negative_cap", 0)),
        "negative_cap_rows_head": negative_head,
        "lut_meta_brief": {
            "coverage_ok": lut_meta.get("coverage_ok"),
            "conflict_count": lut_meta.get("conflict_count"),
            "subspace_count": lut_meta.get("subspace_count") or lut_meta.get("expected_subspace_count"),
        },
        "binary_path": str(bin_path) if wrote_binary else None,
        "elapsed_sec": time.time() - t0,
    }
    meta_path = outdir / f"{name}.meta.json"
    with open(meta_path, "w") as f:
        json.dump(meta, f, indent=2, sort_keys=True)

    print(f"Pivot: {pivot}, target: {target}, max_cap: {args.max_cap}")
    print(f"Total containing rows: {total_containing}")
    print(f"Negative-cap rows: {meta['negative_cap_count']}")
    print(f"Written rows: {meta['rows_written']}")
    print(f"Skipped: {meta['skipped']}")
    print(f"Cap histogram (written): {dict(sorted(Counter(r[0] for r in rows).items())) if wrote_binary else {}}")
    print(f"Binary: {bin_path if wrote_binary else '(not written)'}")
    print(f"Metadata: {meta_path}")
    print(f"Elapsed: {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
