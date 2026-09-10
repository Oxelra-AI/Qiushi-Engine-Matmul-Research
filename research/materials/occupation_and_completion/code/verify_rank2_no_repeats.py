#!/usr/bin/env python3
"""Verify that rank>=2 A-factors cannot repeat in a length-20 decomposition.

Every rank>=2 point must lie in many cap=1 hyperplanes (dim8=8, LB=19).
Cap=1 means at most 1 term in that hyperplane, so multiplicity must be 1.
If every rank>=2 point is in at least one cap=1 hyperplane, repeats are impossible.
"""
import json, sys, time, pickle
from collections import Counter
from pathlib import Path

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, unpack_basis
from core_capacity_from_wang_lut import load_lut

LUT = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUT = Path("data/wang_native/full_tensor")

def gf2_rank_rows(rows):
    basis = [0]*9; r = 0
    for x0 in rows:
        x = x0
        while x:
            p = x.bit_length()-1
            if basis[p]: x ^= basis[p]
            else: basis[p]=x; r+=1; break
    return r

def a_rank(a):
    rows = [0,0,0]
    for idx in range(9):
        if (a>>idx)&1:
            i,j = divmod(idx,3)
            rows[i] |= 1<<j
    return gf2_rank_rows(rows)

def main():
    t0 = time.time()
    lut, _ = load_lut(LUT)
    
    # Classify A-functionals
    rank2plus = set()
    for a in range(1, 512):
        if a_rank(a) >= 2:
            rank2plus.add(a)
    print(f"Rank>=2 A-functionals: {len(rank2plus)}")
    
    # Find all dim=8 (hyperplane) Wang rows with LB=19 (cap20=1)
    cap1_hyperplanes = []  # list of sets of nonzero points
    for key9, lb0 in lut.items():
        dim = int(key9) & 0xF
        if dim != 8: continue
        lb = int(lb0)
        if 20 - lb != 1: continue  # cap20 = 1
        basis = list(unpack_basis(int(key9)))
        pts = set()
        d = len(basis)
        for m in range(1, 1<<d):
            v = 0
            for i, b in enumerate(basis):
                if (m>>i)&1: v ^= b
            pts.add(v)
        cap1_hyperplanes.append(pts)
    
    print(f"Cap=1 hyperplanes (LB=19): {len(cap1_hyperplanes)}")
    print(f"Total hyperplanes (dim=8): should be 511")
    
    # For each rank>=2 point, count how many cap=1 hyperplanes contain it
    min_count = 999
    min_point = -1
    count_hist = Counter()
    for p in sorted(rank2plus):
        cnt = sum(1 for hp in cap1_hyperplanes if p in hp)
        count_hist[cnt] += 1
        if cnt < min_count:
            min_count = cnt
            min_point = p
    
    print(f"\nMinimum cap=1 hyperplane count for any rank>=2 point: {min_count} (point {min_point})")
    print(f"This means every rank>=2 point has multiplicity bound <= 1 (since cap=1 hyperplane limits it)")
    
    if min_count >= 1:
        print("\n==> CONFIRMED: No rank>=2 A-factor can repeat in any valid 20-term decomposition.")
        print("    Therefore the distinct-support DFS is sufficient for the rank>=2 exclusion.")
    
    # Also check: can rank-1 points repeat?
    rank1 = [a for a in range(1,512) if a_rank(a) == 1]
    for p in rank1[:5]:
        cnt = sum(1 for hp in cap1_hyperplanes if p in hp)
        print(f"  Rank-1 point {p}: in {cnt} cap=1 hyperplanes")
    
    result = {
        "status": "ok",
        "rank2plus_count": len(rank2plus),
        "cap1_hyperplanes": len(cap1_hyperplanes),
        "min_cap1_count_for_rank2": min_count,
        "min_point": min_point,
        "repeats_impossible": min_count >= 1,
        "elapsed_sec": time.time() - t0,
    }
    outpath = OUT / "rank2_repeat_impossible.json"
    with open(outpath, "w") as f:
        json.dump(result, f, indent=2)
    print(f"\nSaved {outpath}")

if __name__ == "__main__":
    main()
