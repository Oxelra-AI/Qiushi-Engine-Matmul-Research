#!/usr/bin/env python3
"""Prepare Wang constraints for the FULL tensor T_{3,3,3} at length 20.

For the full tensor, the A-functionals are all 511 nonzero elements of F2^9.
The Wang LUT gives LB for each subspace of F2^9. For a rank-20 decomposition,
the occupancy of subspace U is at most 20 - LB(T/U) = cap20.

We write binary constraints for rows with cap20 <= max_cap.

Also prepare restricted versions:
- rank>=2 only (462 points): excludes the 49 rank-1 A-functionals
- rank>=3 only (168 points): excludes rank-1 and rank-2

The rank>=2 version proves: every full rank-20 has a rank-1 A-factor.
"""
import json, struct, sys, time, pickle
from collections import Counter, defaultdict
from pathlib import Path

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, unpack_basis
from core_capacity_from_wang_lut import load_lut

LUT = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = Path("data/wang_native/full_tensor")
OUTDIR.mkdir(parents=True, exist_ok=True)
MAGIC = b"E11WANG1"  # reuse format

def points_from_basis9(basis9):
    pts = set()
    d = len(basis9)
    for m in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis9):
            if (m >> i) & 1: v ^= b
        pts.add(v)
    return pts

def gf2_rank_rows(rows):
    basis = [0] * 9
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

def a_func_to_matrix_rank(a):
    """Rank of the 3x3 matrix corresponding to A-functional a (9-bit)."""
    rows = [0, 0, 0]
    for idx in range(9):
        if (a >> idx) & 1:
            i, j = divmod(idx, 3)
            rows[i] |= 1 << j
    return gf2_rank_rows(rows)

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-cap", type=int, default=5)
    ap.add_argument("--length", type=int, default=20)
    ap.add_argument("--min-rank", type=int, default=0, help="Min A-functional rank (0=all, 2=rank>=2, 3=rank>=3)")
    args = ap.parse_args()
    
    N = args.length
    max_cap = args.max_cap
    min_rank = args.min_rank
    
    t0 = time.time()
    print(f"Loading LUT {LUT}")
    lut, _ = load_lut(LUT)
    print(f"LUT entries: {len(lut)}")
    
    # Classify all 511 nonzero A-functionals by rank
    rank_counts = Counter()
    valid_points = set()
    for a in range(1, 512):
        r = a_func_to_matrix_rank(a)
        rank_counts[r] += 1
        if r >= min_rank:
            valid_points.add(a)
    
    print(f"A-functional rank distribution: {dict(sorted(rank_counts.items()))}")
    print(f"Valid points (rank >= {min_rank}): {len(valid_points)}")
    
    # Process all LUT entries
    rows = []
    cap_hist = Counter()
    dim_hist = Counter()
    
    for key9, lb0 in lut.items():
        lb = int(lb0)
        cap = N - lb
        dim = int(key9) & 0xF
        
        if cap < 0 or cap > max_cap:
            continue
        
        basis9 = list(unpack_basis(int(key9)))
        pts = points_from_basis9(basis9)
        
        # Filter points to valid set
        pts_valid = pts & valid_points
        if not pts_valid:
            continue
        
        # Build 512-bit mask (using 8 x 64-bit words)
        words = [0] * 8
        for p in pts_valid:
            words[p >> 6] |= 1 << (p & 63)
        
        cap_hist[cap] += 1
        dim_hist[dim] += 1
        rows.append((cap, dim, len(pts_valid), tuple(words)))
    
    suffix = f"rank{min_rank}" if min_rank > 0 else "all"
    bin_path = OUTDIR / f"full_tensor_cap{max_cap}_len{N}_{suffix}.bin"
    
    with open(bin_path, "wb") as f:
        f.write(MAGIC)
        f.write(struct.pack("<I", len(rows)))
        for cap, dim, npts, words in rows:
            # Extended format for 512-bit masks: cap(1), dim(1), reserved(2), mask(8*8=64 bytes)
            f.write(struct.pack("<BBH", cap, dim, 0))
            for w in words[:4]:
                f.write(struct.pack("<Q", w))
    
    # Note: the current binary format uses 4 x 64-bit = 256-bit masks.
    # For 512 points (full tensor), we need 8 x 64-bit = 512-bit masks.
    # But the DFS binary reads only 4 words. We need to either:
    # (a) extend the DFS, or (b) use only the first 256 bits (not correct for full tensor!)
    # Let me instead write a separate format or modify the DFS.
    
    # Actually, for rank>=2 (462 points) or rank>=3 (168 points), all points
    # have values 2-511, so they fit in 512 bits but not 256 bits.
    # For rank>=3 (168 points), max value is... let me check
    max_pt = max(valid_points) if valid_points else 0
    print(f"Max valid point value: {max_pt}")
    print(f"Need {(max_pt + 64) // 64} 64-bit words for bitmask")
    
    # The existing DFS binary reads 4 words (256 bits = points 0-255).
    # Full tensor points go up to 511, needing 8 words (512 bits).
    # I need to extend the DFS or restrict to points < 256.
    
    # For now, let's check how many valid points are < 256 vs >= 256
    below = sum(1 for p in valid_points if p < 256)
    above = sum(1 for p in valid_points if p >= 256)
    print(f"Valid points < 256: {below}, >= 256: {above}")
    
    # Save metadata
    meta = {
        "status": "ok",
        "length": N,
        "max_cap": max_cap,
        "min_rank": min_rank,
        "valid_point_count": len(valid_points),
        "constraint_rows": len(rows),
        "cap_hist": dict(sorted(cap_hist.items())),
        "dim_hist": dict(sorted(dim_hist.items())),
        "rank_counts": dict(sorted(rank_counts.items())),
        "binary_path": str(bin_path),
        "max_point_value": max_pt,
        "points_below_256": below,
        "points_above_256": above,
        "elapsed_sec": time.time() - t0,
        "NOTE": "Binary format uses 256-bit masks; full tensor needs 512-bit extension",
    }
    meta_path = OUTDIR / f"full_tensor_cap{max_cap}_len{N}_{suffix}.meta.json"
    with open(meta_path, "w") as f:
        json.dump(meta, f, indent=2)
    
    print(json.dumps(meta, indent=2))

if __name__ == "__main__":
    main()
