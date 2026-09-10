#!/usr/bin/env python3
"""Prepare compact binary E11 Wang occupancy constraints for native DFS.

The native enumerator does not read Python pickles. This script decodes the
Wang LUT restricted to subspaces containing the deleted E11 line, projects each
row to the 8-dimensional quotient, and writes rows with cap19 <= max_cap as
fixed-size records:

  magic b'E11WANG1'
  uint32 nrows
  repeated nrows times:
      uint8 cap19, uint8 dim8, uint16 reserved, uint64 mask[4]

The 256-bit row mask uses bit q for quotient point q (1..255), bit 0 unused.
"""
from __future__ import annotations

import argparse
import json
import struct
import sys
import time
from collections import Counter
from pathlib import Path

S04_SCRIPTS = Path("scripts")
if str(S04_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(S04_SCRIPTS))
from wang_capacity_lazy import rref_basis, unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = Path("data/wang_native")
MASK9 = (1 << 9) - 1
N = 19
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


def mask_from_basis8(basis8) -> tuple[int, int, int, int]:
    words = [0, 0, 0, 0]
    d = len(basis8)
    for m in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis8):
            if (m >> i) & 1:
                v ^= b
        if v:
            words[v >> 6] |= 1 << (v & 63)
    return tuple(words)


def orbit_branch_specs(path: Path) -> dict:
    with open(path) as f:
        data = json.load(f)
    orbits = data["point_orbits"]["orbits"]
    specs = []
    earlier = [0, 0, 0, 0]
    reps_are_minima = True
    for i, orb in enumerate(orbits):
        members = [int(x) for x in orb["members"]]
        rep = int(orb["rep"])
        reps_are_minima = reps_are_minima and rep == min(members)
        specs.append({
            "branch": i,
            "rep": rep,
            "orbit_size": len(members),
            "earlier_forbid_words_hex": [hex(x) for x in earlier],
            "earlier_forbid_point_count": sum(x.bit_count() for x in earlier),
        })
        for p in members:
            earlier[p >> 6] |= 1 << (p & 63)
    return {
        "num_branches": len(specs),
        "reps_are_orbit_minima": reps_are_minima,
        "reps": [s["rep"] for s in specs],
        "branch_specs": specs,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-cap", type=int, default=5)
    ap.add_argument("--outdir", type=Path, default=OUTDIR)
    ap.add_argument("--orbit-json", type=Path, default=Path("data/e11_orbits/e11_quotient_orbits.json"))
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    print(f"Loading LUT {LUT_PATH}")
    lut, meta = load_lut(LUT_PATH)
    rows = []
    cap_hist = Counter()
    dim_hist = Counter()
    lb_hist = Counter()
    all_e11 = 0
    for key9, lb0 in lut.items():
        if not contains_e11(key9):
            continue
        all_e11 += 1
        lb = int(lb0)
        cap = N - lb
        dim8 = (int(key9) & 0xF) - 1
        cap_hist[cap] += 1
        dim_hist[dim8] += 1
        lb_hist[lb] += 1
        if cap < 0 or cap > args.max_cap or cap >= N:
            continue
        basis8 = key9_to_basis8(int(key9))
        words = mask_from_basis8(basis8)
        # cap=0, dim8=0 has no points and is vacuous for nonzero supports; keep
        # it harmlessly because the native enumerator can handle empty masks.
        rows.append((cap, dim8, words))

    bin_path = args.outdir / f"e11_wang_cap{args.max_cap}.bin"
    with open(bin_path, "wb") as f:
        f.write(MAGIC)
        f.write(struct.pack("<I", len(rows)))
        for cap, dim8, words in rows:
            f.write(struct.pack("<BBHQQQQ", cap, dim8, 0, *words))

    branches = orbit_branch_specs(args.orbit_json)
    branch_path = args.outdir / "e11_orbit_branch_specs.json"
    branch_path.write_text(json.dumps(branches, indent=2, sort_keys=True) + "\n")

    meta_out = {
        "status": "ok",
        "max_cap": args.max_cap,
        "binary_path": str(bin_path),
        "row_count_written": len(rows),
        "all_e11_rows": all_e11,
        "cap19_hist_all_e11": dict(sorted((int(k), int(v)) for k, v in cap_hist.items())),
        "dim8_hist_all_e11": dict(sorted((int(k), int(v)) for k, v in dim_hist.items())),
        "lb_hist_all_e11": dict(sorted((int(k), int(v)) for k, v in lb_hist.items())),
        "branch_spec_path": str(branch_path),
        "branch_specs": branches,
        "elapsed_sec": time.time() - t0,
    }
    meta_path = args.outdir / f"e11_wang_cap{args.max_cap}.meta.json"
    meta_path.write_text(json.dumps(meta_out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": "ok",
        "binary_path": str(bin_path),
        "row_count_written": len(rows),
        "all_e11_rows": all_e11,
        "cap_hist_written": dict(sorted((int(k), int(v)) for k, v in Counter(r[0] for r in rows).items())),
        "branch_reps": branches["reps"],
        "reps_are_orbit_minima": branches["reps_are_orbit_minima"],
        "elapsed_sec": time.time() - t0,
    }, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
