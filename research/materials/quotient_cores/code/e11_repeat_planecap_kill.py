#!/usr/bin/env python3
"""Kill repeated quotient directions by plane-cap arithmetic.

For each repeatable direction p (line_cap >= 2), compute the maximum number of
other distinct points that can coexist with p doubled, using plane constraints.
"""
import json, sys, time, pickle
from collections import Counter, defaultdict
from pathlib import Path

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, unpack_basis
from core_capacity_from_wang_lut import load_lut

LUT = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUT = Path("data/wang_validation")
OUT.mkdir(parents=True, exist_ok=True)
MASK9 = (1 << 9) - 1
REPEATABLE = [1, 2, 3, 4, 32, 36]

def contains_e11(k):
    d = k & 0xF
    return d > 0 and ((k >> (4 + 9*(d-1))) & MASK9) == 1

def key9_to_basis8(k):
    raw = []
    for b in unpack_basis(k):
        if b == 1: continue
        q = int(b)
        if q & 1: q ^= 1
        q8 = 0
        for bit in range(1,9):
            if (q >> bit) & 1: q8 |= 1 << (bit-1)
        if q8: raw.append(q8)
    return tuple(rref_basis(raw, n=8)) if raw else ()

def points_from_basis(b8):
    pts = set()
    d = len(b8)
    for m in range(1, 1<<d):
        v = 0
        for i, bi in enumerate(b8):
            if (m >> i) & 1: v ^= bi
        pts.add(v)
    return pts

def main():
    t0 = time.time()
    print("Loading LUT...")
    lut, _ = load_lut(LUT)

    # Build per-point plane cap data
    point_plane_caps = defaultdict(list)  # point -> list of cap values
    
    for k, lb0 in lut.items():
        if not contains_e11(k): continue
        dim8 = (int(k) & 0xF) - 1
        if dim8 != 2: continue
        lb = int(lb0)
        cap19 = 19 - lb
        b8 = key9_to_basis8(int(k))
        pts = points_from_basis(b8)
        for p in pts:
            point_plane_caps[p].append(cap19)

    print(f"  Decoded plane caps in {time.time()-t0:.1f}s")

    # Analyze each repeatable direction
    print("\n=== REPEAT DIRECTION PLANE-CAP ANALYSIS ===")
    results = {}
    for p in REPEATABLE:
        caps = point_plane_caps.get(p, [])
        n_planes = len(caps)
        cap_hist = Counter(caps)
        
        # With p doubled: plane with cap c allows min(2, max(0, c-2)) extra points
        max_extras = 0
        details = {}
        for c in sorted(cap_hist.keys()):
            cnt = cap_hist[c]
            contrib = min(2, max(0, c - 2))
            details[c] = {"count": cnt, "per_plane": contrib, "total": cnt * contrib}
            max_extras += cnt * contrib
        
        killed = max_extras < 17
        results[p] = {
            "planes_through_p": n_planes,
            "cap_hist": dict(sorted(cap_hist.items())),
            "details": details,
            "max_extras": max_extras,
            "need_17": 17,
            "killed": killed,
        }
        tag = "KILLED" if killed else "FEASIBLE"
        print(f"  p={p:3d}: {n_planes} planes, max_extras={max_extras}, need=17 => {tag}")
        for c in sorted(details):
            d = details[c]
            print(f"    cap={c}: {d['count']} planes × {d['per_plane']} extras = {d['total']}")

    all_killed = all(r["killed"] for r in results.values())
    print(f"\nAll repeatable directions killed: {all_killed}")
    
    # Also check 3-flat constraints for even tighter bound
    if not all_killed:
        print("\n=== CHECKING 3-FLAT CONSTRAINTS FOR SURVIVING DIRECTIONS ===")
        surviving = [p for p in REPEATABLE if not results[p]["killed"]]
        # Build per-point 3-flat caps
        point_3flat_caps = defaultdict(list)
        for k, lb0 in lut.items():
            if not contains_e11(k): continue
            dim8 = (int(k) & 0xF) - 1
            if dim8 != 3: continue
            lb = int(lb0)
            cap19 = 19 - lb
            b8 = key9_to_basis8(int(k))
            pts = points_from_basis(b8)
            for p in pts:
                if p in surviving:
                    point_3flat_caps[p].append(cap19)
        
        for p in surviving:
            caps3 = point_3flat_caps.get(p, [])
            ch = Counter(caps3)
            print(f"  p={p}: {len(caps3)} 3-flats, cap_hist={dict(sorted(ch.items()))}")

    out = {
        "status": "ok",
        "elapsed_sec": time.time() - t0,
        "repeatable_directions": REPEATABLE,
        "results": {str(p): r for p, r in results.items()},
        "all_killed": all_killed,
    }
    outpath = OUT / "e11_repeat_planecap_kill.json"
    with open(outpath, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(f"\nSaved {outpath}")

if __name__ == "__main__":
    main()
