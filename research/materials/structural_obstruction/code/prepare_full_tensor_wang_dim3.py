#!/usr/bin/env python3
"""Prepare full-tensor Wang constraints restricted to dim<=3 for domain DFS.

For the rank>=2 exclusion (462 points), we only need dim<=3 constraints for
domain propagation. This gives ~832K rows instead of 7M, making the DFS feasible.
Uses a different binary format with 512-bit masks.
"""
import json, struct, sys, time, pickle
from collections import Counter
from pathlib import Path

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, unpack_basis
from core_capacity_from_wang_lut import load_lut

LUT = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = Path("data/wang_native/full_tensor")
OUTDIR.mkdir(parents=True, exist_ok=True)
MAGIC = b"WANG512\x01"  # new format with 512-bit masks

def gf2_rank_rows(rows):
    basis = [0] * 9
    r = 0
    for x0 in rows:
        x = x0
        while x:
            p = x.bit_length() - 1
            if basis[p]: x ^= basis[p]
            else: basis[p] = x; r += 1; break
    return r

def a_func_rank(a):
    rows = [0, 0, 0]
    for idx in range(9):
        if (a >> idx) & 1:
            i, j = divmod(idx, 3)
            rows[i] |= 1 << j
    return gf2_rank_rows(rows)

def points_from_basis(basis):
    d = len(basis)
    pts = set()
    for m in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis):
            if (m >> i) & 1: v ^= b
        pts.add(v)
    return pts

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-cap", type=int, default=5)
    ap.add_argument("--max-dim", type=int, default=3)
    ap.add_argument("--length", type=int, default=20)
    ap.add_argument("--min-rank", type=int, default=2)
    args = ap.parse_args()
    
    N = args.length
    t0 = time.time()
    print(f"Loading LUT...")
    lut, _ = load_lut(LUT)
    
    # Valid points
    valid = set()
    rank_cnt = Counter()
    for a in range(1, 512):
        r = a_func_rank(a)
        rank_cnt[r] += 1
        if r >= args.min_rank:
            valid.add(a)
    print(f"Valid points (rank>={args.min_rank}): {len(valid)}")
    print(f"Rank distribution: {dict(sorted(rank_cnt.items()))}")
    
    # Process LUT
    rows = []
    cap_hist = Counter()
    for key9, lb0 in lut.items():
        lb = int(lb0)
        cap = N - lb
        dim = int(key9) & 0xF
        if cap < 0 or cap > args.max_cap: continue
        if dim > args.max_dim: continue
        
        basis = list(unpack_basis(int(key9)))
        pts = points_from_basis(basis) & valid
        if not pts: continue
        
        # 512-bit mask: 8 x 64-bit words
        words = [0] * 8
        for p in pts:
            words[p >> 6] |= 1 << (p & 63)
        
        cap_hist[cap] += 1
        rows.append((cap, dim, len(pts), tuple(words)))
    
    print(f"Constraint rows (dim<={args.max_dim}, cap<={args.max_cap}): {len(rows)}")
    print(f"Cap histogram: {dict(sorted(cap_hist.items()))}")
    
    suffix = f"rank{args.min_rank}_dim{args.max_dim}"
    bin_path = OUTDIR / f"full_wang_cap{args.max_cap}_len{N}_{suffix}.bin"
    
    with open(bin_path, "wb") as f:
        f.write(MAGIC)
        f.write(struct.pack("<I", len(rows)))
        for cap, dim, npts, words in rows:
            f.write(struct.pack("<BBH", cap, dim, 0))
            for w in words:
                f.write(struct.pack("<Q", w))
    
    meta = {
        "status": "ok",
        "length": N, "max_cap": args.max_cap, "max_dim": args.max_dim,
        "min_rank": args.min_rank, "valid_points": len(valid),
        "constraint_rows": len(rows),
        "cap_hist": dict(sorted(cap_hist.items())),
        "binary_path": str(bin_path),
        "format": "WANG512 (8 x 64-bit words per mask)",
        "elapsed_sec": time.time() - t0,
    }
    meta_path = bin_path.with_suffix(".meta.json")
    with open(meta_path, "w") as f:
        json.dump(meta, f, indent=2)
    print(json.dumps(meta, indent=2))

if __name__ == "__main__":
    main()
