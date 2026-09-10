#!/usr/bin/env python3
"""analysisb: Test the purity-side 2-SAT filter on random rank-19 supports.

Measures: what fraction of random 19-point subsets of F₂⁸\{0} fail the 2-SAT?
Also tests the known L15 near-support and weight-stratified random samples.
"""
import json, time, sys
from pathlib import Path
from collections import Counter
from itertools import combinations
import numpy as np

sys.path.insert(0, str(Path("scripts")))
from excess_geometry_2sat import (
    support_capacities, support_sharing, solve_purity_2sat,
    CROSS_PAIRS, LATIN_TRIPLES, SLICE_BLOCKS
)

ROOT = Path("research/research_record")
OUT = ROOT / "workspace/data/excess_geometry/rank19_2sat_filter_test.json"

ALL_DIRS = list(range(1, 256))  # 255 nonzero directions in F₂⁸

def hamming_weight(x: int) -> int:
    return bin(x).count('1')

def random_support(rng: np.random.Generator, size: int = 19) -> list[int]:
    """Random size-subset of F₂⁸\\{0}."""
    idx = rng.choice(255, size=size, replace=False)
    return sorted(ALL_DIRS[i] for i in idx)

def classify_2sat(support: list[int]) -> dict:
    caps = support_capacities(support)
    sharing = support_sharing(support)
    result = solve_purity_2sat(caps, sharing)
    total_wt = sum(caps)
    min_cap = min(caps)
    n_cap3 = sum(1 for c in caps if c == 3)
    n_cap4 = sum(1 for c in caps if c == 4)
    n_cap34 = n_cap3 + n_cap4
    # count cross-pair sharings between cap3/cap4
    cross_active = 0
    for s1, s2 in CROSS_PAIRS:
        if (s1, s2) not in sharing:
            continue
        if (caps[s1] <= 3 and caps[s2] <= 4) or (caps[s2] <= 3 and caps[s1] <= 4):
            cross_active += 1
    return {
        "sat": result["sat"],
        "caps": caps,
        "total_weight": total_wt,
        "min_cap": min_cap,
        "n_cap3": n_cap3,
        "n_cap4": n_cap4,
        "n_cap34": n_cap34,
        "cross_active": cross_active,
    }


def main():
    t0 = time.time()
    rng = np.random.default_rng(42)
    results = {}

    # --- Test 1: L15 near-support ---
    L15 = [1, 2, 3, 4, 8, 20, 24, 31, 32, 64, 73, 109, 127, 128, 141, 160, 182, 192, 219]
    r15 = classify_2sat(L15)
    results["L15_near_support"] = r15
    print(f"L15: sat={r15['sat']}, caps={r15['caps']}, weight={r15['total_weight']}, "
          f"cap3={r15['n_cap3']}, cap4={r15['n_cap4']}, cross_active={r15['cross_active']}")

    # --- Test 2: analysis 9-violation support ---
    S53 = [1, 2, 3, 4, 8, 20, 24, 31, 32, 36, 64, 73, 127, 128, 141, 160, 182, 192, 219]
    r53 = classify_2sat(S53)
    results["support"] = r53
    print(f"S53: sat={r53['sat']}, caps={r53['caps']}, weight={r53['total_weight']}, "
          f"cap3={r53['n_cap3']}, cap4={r53['n_cap4']}, cross_active={r53['cross_active']}")

    # --- Test 3: Random 19-point supports ---
    N_SAMPLES = 20000
    sat_count = 0
    unsat_count = 0
    weight_bins: dict[str, dict] = {}
    cap34_bins: dict[int, dict] = {}
    
    for trial in range(N_SAMPLES):
        supp = random_support(rng, 19)
        c = classify_2sat(supp)
        if c["sat"]:
            sat_count += 1
        else:
            unsat_count += 1
        
        # Bin by total weight range
        w = c["total_weight"]
        wbin = f"{(w // 5) * 5}-{(w // 5) * 5 + 4}"
        if wbin not in weight_bins:
            weight_bins[wbin] = {"total": 0, "sat": 0, "unsat": 0}
        weight_bins[wbin]["total"] += 1
        if c["sat"]:
            weight_bins[wbin]["sat"] += 1
        else:
            weight_bins[wbin]["unsat"] += 1
        
        # Bin by number of cap-3/cap-4 slices
        nc = c["n_cap34"]
        if nc not in cap34_bins:
            cap34_bins[nc] = {"total": 0, "sat": 0, "unsat": 0}
        cap34_bins[nc]["total"] += 1
        if c["sat"]:
            cap34_bins[nc]["sat"] += 1
        else:
            cap34_bins[nc]["unsat"] += 1
    
    unsat_pct = 100 * unsat_count / N_SAMPLES
    print(f"\nRandom 19-point supports ({N_SAMPLES}):")
    print(f"  SAT: {sat_count} ({100 * sat_count / N_SAMPLES:.1f}%)")
    print(f"  UNSAT: {unsat_count} ({unsat_pct:.1f}%)")
    print(f"\n  By total weight:")
    for k in sorted(weight_bins):
        b = weight_bins[k]
        pct = 100 * b["unsat"] / b["total"] if b["total"] else 0
        print(f"    {k}: {b['total']} total, {b['unsat']} UNSAT ({pct:.1f}%)")
    print(f"\n  By #cap-3/4 slices:")
    for nc in sorted(cap34_bins):
        b = cap34_bins[nc]
        pct = 100 * b["unsat"] / b["total"] if b["total"] else 0
        print(f"    {nc}: {b['total']} total, {b['unsat']} UNSAT ({pct:.1f}%)")

    # --- Test 4: Weight-constrained random (close to minimum weight 27) ---
    print("\n--- Low-weight random supports (weight ≤ 35) ---")
    low_wt_sat = 0
    low_wt_unsat = 0
    low_wt_total = 0
    attempts = 0
    max_attempts = 500000
    while low_wt_total < 2000 and attempts < max_attempts:
        supp = random_support(rng, 19)
        caps = support_capacities(supp)
        w = sum(caps)
        attempts += 1
        if w > 35:
            continue
        low_wt_total += 1
        c = classify_2sat(supp)
        if c["sat"]:
            low_wt_sat += 1
        else:
            low_wt_unsat += 1
    
    if low_wt_total:
        print(f"  Found {low_wt_total} supports with weight ≤ 35 in {attempts} attempts")
        print(f"  SAT: {low_wt_sat}, UNSAT: {low_wt_unsat} ({100*low_wt_unsat/low_wt_total:.1f}%)")
    else:
        print(f"  No low-weight supports found in {attempts} attempts")
    
    results["random_19pt"] = {
        "samples": N_SAMPLES,
        "sat": sat_count, "unsat": unsat_count,
        "unsat_pct": round(unsat_pct, 2),
        "by_weight": {k: weight_bins[k] for k in sorted(weight_bins)},
        "by_cap34_count": {str(k): cap34_bins[k] for k in sorted(cap34_bins)},
    }
    results["low_weight_random"] = {
        "max_weight": 35,
        "attempts": attempts,
        "found": low_wt_total,
        "sat": low_wt_sat, "unsat": low_wt_unsat,
        "unsat_pct": round(100 * low_wt_unsat / max(low_wt_total, 1), 2),
    }
    results["elapsed_sec"] = round(time.time() - t0, 3)
    
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(results, indent=2) + "\n")
    print(f"\nSaved to {OUT}")


if __name__ == "__main__":
    main()
