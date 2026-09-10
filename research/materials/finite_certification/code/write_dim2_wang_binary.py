#!/usr/bin/env python3
"""Write inherited Wang occupation rows for a dim-2 quotient node as E11WANG1.

The E11WANG1 row format has 4 uint64 masks for point labels 1..255.  Here the
actual quotient has only 127 nonzero directions; labels 128..255 should be
forbidden when using generic distinct DFS tools.
"""
from __future__ import annotations

import argparse
import pickle
import struct
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from node_local_occupation_closure import LUT_PATH, node_constraints  # type: ignore
from dim2_quotient_det import orbit_basis  # type: ignore

MAGIC = b"E11WANG1"
REC = struct.Struct("<BBHQQQQ")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--orbit-index", type=int, required=True)
    ap.add_argument("--target", type=int, default=18)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    with LUT_PATH.open("rb") as f:
        d = pickle.load(f)
    lut = d["lut"] if isinstance(d, dict) and "lut" in d else d
    W = orbit_basis(args.orbit_index)
    rows, meta = node_constraints(W, lut, args.target)
    out_rows = []
    for mask, cap in rows:
        words = [0, 0, 0, 0]
        for i in range(127):
            if (int(mask) >> i) & 1:
                p = i + 1
                words[p // 64] |= 1 << (p % 64)
        # Compute quotient subspace dimension from popcount = 2^dim - 1.
        pc = int(mask).bit_count()
        dim = (pc + 1).bit_length() - 1
        out_rows.append((int(cap), int(dim), words))
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("wb") as f:
        f.write(MAGIC)
        f.write(struct.pack("<I", len(out_rows)))
        for cap, dim, words in out_rows:
            f.write(REC.pack(cap & 0xFF, dim & 0xFF, 0, *[w & ((1 << 64) - 1) for w in words]))
    print({"out": str(args.out), "rows": len(out_rows), "meta": meta})


if __name__ == "__main__":
    main()
