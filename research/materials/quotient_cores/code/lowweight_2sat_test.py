#!/usr/bin/env python3
"""analysisc: Targeted 2-SAT filter test for low-weight rank-19 supports.

Random supports have average weight ~76, far from the rank-19 regime (≥27).
This script generates supports biased toward low weight to test the filter
where it actually matters.
"""
import json, time, sys
from pathlib import Path
from collections import Counter
import numpy as np

sys.path.insert(0, str(Path("scripts")))
from excess_geometry_2sat import (
    support_capacities, support_sharing, solve_purity_2sat,
    CROSS_PAIRS, LATIN_TRIPLES, SLICE_BLOCKS
)

ROOT = Path("research/research_record")
OUT = ROOT / "workspace/data/excess_geometry/rank19_lowweight_2sat_test.json"

def hamming(x: int) -> int:
    return bin(x).count('1')

# Precompute directions by weight
DIRS_BY_WT = {}
for d in range(1, 256):
    w = hamming(d)
    DIRS_BY_WT.setdefault(w, []).append(d)

def generate_low_weight_support(rng: np.random.Generator, target_weight_range=(27, 40)):
    """Generate a 19-point support with total weight in target range, all caps ≥ 3."""
    lo, hi = target_weight_range
    for _ in range(2000):
        # Strategy: use mostly low-weight directions
        # Start with 8 weight-1 dirs (covers each slice once, weight=8)
        base = list(DIRS_BY_WT[1])  # 8 directions, weight 1 each
        remaining = 19 - 8  # need 11 more
        pool = [d for d in range(1, 256) if d not in base and hamming(d) <= 3]
        if len(pool) < remaining:
            continue
        extra = sorted(rng.choice(pool, size=remaining, replace=False).tolist())
        support = sorted(set(base + extra))
        if len(support) != 19:
            continue
        caps = support_capacities(support)
        w = sum(caps)
        if lo <= w <= hi and min(caps) >= 3:
            return support
    return None

def generate_constrained_support(rng: np.random.Generator, max_dir_weight=2):
    """Generate support using only directions of weight ≤ max_dir_weight."""
    pool = [d for d in range(1, 256) if hamming(d) <= max_dir_weight]
    for _ in range(5000):
        dirs = sorted(rng.choice(pool, size=19, replace=False).tolist())
        caps = support_capacities(dirs)
        if min(caps) >= 3:
            return dirs
    return None

def classify(support):
    caps = support_capacities(support)
    sharing = support_sharing(support)
    res = solve_purity_2sat(caps, sharing)
    n_cap3 = sum(1 for c in caps if c == 3)
    n_cap4 = sum(1 for c in caps if c == 4)
    cross_sharing = 0
    for s1, s2 in CROSS_PAIRS:
        if (s1, s2) in sharing:
            if (caps[s1] <= 3 and caps[s2] <= 4) or (caps[s2] <= 3 and caps[s1] <= 4):
                cross_sharing += 1
    return {
        "sat": res["sat"],
        "weight": sum(caps),
        "caps": caps,
        "n_cap3": n_cap3,
        "n_cap4": n_cap4,
        "n_cap34": n_cap3 + n_cap4,
        "cross_sharing_34": cross_sharing,
    }


def main():
    t0 = time.time()
    rng = np.random.default_rng(12345)
    results = {}

    # --- Test 1: Weight-2 only supports (weight = 19*2 = 38) ---
    print("=== Test 1: Weight ≤ 2 directions only ===")
    w2_sat = 0; w2_unsat = 0; w2_fail = 0; w2_total = 5000
    w2_records = []
    for _ in range(w2_total):
        s = generate_constrained_support(rng, max_dir_weight=2)
        if s is None:
            w2_fail += 1; continue
        c = classify(s)
        w2_records.append(c)
        if c["sat"]: w2_sat += 1
        else: w2_unsat += 1
    
    found = len(w2_records)
    print(f"  Generated: {found}/{w2_total}")
    if found:
        wts = [r["weight"] for r in w2_records]
        cap34 = Counter(r["n_cap34"] for r in w2_records)
        print(f"  Weight range: {min(wts)}-{max(wts)}, mean={np.mean(wts):.1f}")
        print(f"  SAT: {w2_sat} ({100*w2_sat/found:.1f}%), UNSAT: {w2_unsat} ({100*w2_unsat/found:.1f}%)")
        print(f"  Cap-3/4 count: {dict(sorted(cap34.items()))}")
        # UNSAT rate by cap34 count
        for nc in sorted(cap34):
            sub = [r for r in w2_records if r["n_cap34"] == nc]
            nu = sum(1 for r in sub if not r["sat"])
            print(f"    {nc} cap34: {nu}/{len(sub)} UNSAT ({100*nu/len(sub):.1f}%)")
    
    results["weight_le2"] = {
        "total": w2_total, "found": found,
        "sat": w2_sat, "unsat": w2_unsat,
        "unsat_pct": round(100 * w2_unsat / max(found, 1), 2),
        "weight_range": [min(wts), max(wts)] if found else [],
    }

    # --- Test 2: Mixed weight-1 + weight-2 (lowest possible) ---
    print("\n=== Test 2: 8 weight-1 + 11 weight-2 (weight = 30) ===")
    w1_dirs = DIRS_BY_WT[1]  # exactly 8
    w2_dirs = DIRS_BY_WT[2]  # exactly 28
    mix_sat = 0; mix_unsat = 0; mix_found = 0; mix_cap34_hist = Counter()
    N_MIX = 50000
    for _ in range(N_MIX):
        extra = sorted(rng.choice(w2_dirs, size=11, replace=False).tolist())
        support = sorted(set(w1_dirs + extra))
        if len(support) != 19:
            continue
        caps = support_capacities(support)
        if min(caps) < 3:
            continue
        mix_found += 1
        c = classify(support)
        mix_cap34_hist[c["n_cap34"]] += 1
        if c["sat"]: mix_sat += 1
        else: mix_unsat += 1
    
    print(f"  Found {mix_found}/{N_MIX} valid (all caps ≥ 3)")
    if mix_found:
        print(f"  SAT: {mix_sat} ({100*mix_sat/mix_found:.1f}%), UNSAT: {mix_unsat} ({100*mix_unsat/mix_found:.1f}%)")
        print(f"  Cap-3/4 count: {dict(sorted(mix_cap34_hist.items()))}")

    results["weight30_mix"] = {
        "total": N_MIX, "found": mix_found,
        "sat": mix_sat, "unsat": mix_unsat,
        "unsat_pct": round(100 * mix_unsat / max(mix_found, 1), 2),
    }

    # --- Test 3: Low-weight targeted (27-35) ---
    print("\n=== Test 3: Targeted low weight (27-40) ===")
    low_sat = 0; low_unsat = 0; low_found = 0
    low_wt_hist = Counter()
    low_cap34_unsat = Counter()
    N_LOW = 10000
    for _ in range(N_LOW):
        s = generate_low_weight_support(rng, (27, 40))
        if s is None:
            continue
        low_found += 1
        c = classify(s)
        low_wt_hist[(c["weight"], c["sat"])] += 1
        if c["sat"]: low_sat += 1
        else:
            low_unsat += 1
            low_cap34_unsat[c["n_cap34"]] += 1
    
    print(f"  Found: {low_found}/{N_LOW}")
    if low_found:
        print(f"  SAT: {low_sat} ({100*low_sat/low_found:.1f}%), UNSAT: {low_unsat} ({100*low_unsat/low_found:.1f}%)")
        print(f"  UNSAT by cap34: {dict(sorted(low_cap34_unsat.items()))}")
        # By weight
        for w in sorted(set(k[0] for k in low_wt_hist)):
            tot = sum(low_wt_hist.get((w, True), 0) + low_wt_hist.get((w, False), 0) for _ in [0])
            tot = low_wt_hist.get((w, True), 0) + low_wt_hist.get((w, False), 0)
            nu = low_wt_hist.get((w, False), 0)
            if tot > 0:
                print(f"    weight {w}: {tot} total, {nu} UNSAT ({100*nu/tot:.1f}%)")
    
    results["low_weight_targeted"] = {
        "total": N_LOW, "found": low_found,
        "sat": low_sat, "unsat": low_unsat,
        "unsat_pct": round(100 * low_unsat / max(low_found, 1), 2),
    }
    
    results["elapsed_sec"] = round(time.time() - t0, 3)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(results, indent=2) + "\n")
    print(f"\nSaved to {OUT}")


if __name__ == "__main__":
    main()
