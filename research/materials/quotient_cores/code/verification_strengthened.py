#!/usr/bin/env python3
"""analysise: review-verified strengthened purity checker.

Implements the full weighted leakage inequality from the review verification:
  For each slice s and each cap-3 slice u sharing h_su items with s:
    e_B(s) >= h_su * 1[j_s != j_u]
    e_C(s) >= h_su * 1[i_s != i_u]
  Hence: h_su * (1[j_s!=j_u] + 1[i_s!=i_u]) <= m_s - 3

  Key new obstructions (review-verified):
  1. Cap-5 + cross-pair cap-3 sharing 1 item -> (e_B,e_C) >= (1,1), so neither pure
  2. Cap-5 + 2 non-own row groups -> (e_B,e_C) = (2,0) exactly: force NOT B-pure AND C-pure
  3. Cap-5 + 2 non-own row groups AND one sharing is cross-pair -> e_B+e_C >= 3 -> DIRECT UNSAT
"""
import json, time, sys
from pathlib import Path
from collections import Counter, defaultdict
from itertools import combinations
import numpy as np

sys.path.insert(0, str(Path("scripts")))
from excess_geometry_2sat import (
    support_capacities, support_sharing, CROSS_PAIRS, LATIN_TRIPLES, SLICE_BLOCKS
)

ROOT = Path("research/research_record")
OUT = ROOT / "workspace/data/excess_geometry/verification_strengthened_test.json"


def compute_sharing_details(support):
    """For each pair of slices, count how many terms are shared."""
    us = support
    sharing_count = defaultdict(int)
    sharing_set = set()
    for u in us:
        active = [s for s in range(8) if (u >> s) & 1]
        for s1, s2 in combinations(active, 2):
            sharing_count[(s1, s2)] += 1
            sharing_set.add((s1, s2))
    return dict(sharing_count), sharing_set


def check_strengthened_obstructions(support):
    """Apply full review-verified strengthened purity conditions.
    
    Returns dict with pass/fail and obstruction details.
    """
    caps = support_capacities(support)
    sharing_count, sharing_set = compute_sharing_details(support)
    
    obstructions = []
    
    for s in range(8):
        j_s, i_s = SLICE_BLOCKS[s]
        m_s = caps[s]
        if m_s < 3:
            obstructions.append({"type": "insufficient_capacity", "slice": s, "cap": m_s})
            continue
        
        # Find all cap-3 slices sharing with s
        cap3_sharing = []
        for u in range(8):
            if u == s or caps[u] > 3:
                continue
            pair = (min(s, u), max(s, u))
            if pair not in sharing_set:
                continue
            h_su = sharing_count.get(pair, 0)
            j_u, i_u = SLICE_BLOCKS[u]
            cap3_sharing.append({
                "u": u, "h_su": h_su, "j_u": j_u, "i_u": i_u,
                "diff_j": j_u != j_s, "diff_i": i_u != i_s,
                "is_cross": j_u != j_s and i_u != i_s,
            })
        
        if not cap3_sharing:
            continue
        
        # Compute lower bounds on e_B, e_C from cap-3 sharing
        # e_B >= sum over non-own row groups: max h_su among cap-3 with that row group
        by_nonown_j = defaultdict(int)  # non-own row group -> max sharing count
        by_nonown_i = defaultdict(int)
        for info in cap3_sharing:
            if info["diff_j"]:
                by_nonown_j[info["j_u"]] = max(by_nonown_j[info["j_u"]], info["h_su"])
            if info["diff_i"]:
                by_nonown_i[info["i_u"]] = max(by_nonown_i[info["i_u"]], info["h_su"])
        
        eB_lb = sum(by_nonown_j.values())  # lower bound on e_B
        eC_lb = sum(by_nonown_i.values())  # lower bound on e_C
        excess_budget = m_s - 3
        
        if eB_lb + eC_lb > excess_budget:
            obstructions.append({
                "type": "weighted_leakage_violation",
                "slice": s, "cap": m_s,
                "eB_lb": eB_lb, "eC_lb": eC_lb,
                "excess_budget": excess_budget,
                "cap3_details": cap3_sharing,
            })
            continue
        
        # Specific per-sharing checks
        for info in cap3_sharing:
            h = info["h_su"]
            cost = h * (int(info["diff_j"]) + int(info["diff_i"]))
            if cost > excess_budget:
                obstructions.append({
                    "type": "single_cap3_excess_overflow",
                    "slice": s, "cap3_slice": info["u"],
                    "h_su": h, "cost": cost, "budget": excess_budget,
                })
    
    # Check cap-5 + cross-pair cap-3 + additional row-group trigger = direct UNSAT
    for s in range(8):
        if caps[s] != 5:
            continue
        j_s, i_s = SLICE_BLOCKS[s]
        
        nonown_row_groups = defaultdict(list)
        for u in range(8):
            if caps[u] > 3 or u == s:
                continue
            pair = (min(s, u), max(s, u))
            if pair not in sharing_set:
                continue
            j_u, i_u = SLICE_BLOCKS[u]
            if j_u != j_s:
                nonown_row_groups[j_u].append({"u": u, "j_u": j_u, "i_u": i_u})
        
        if len(nonown_row_groups) >= 2:
            # Two non-own row groups → e_B >= 2
            # Check if any sharing cap-3 also has diff col group
            has_cross = False
            for grp_info_list in nonown_row_groups.values():
                for info in grp_info_list:
                    if info["i_u"] != i_s:
                        has_cross = True
            if has_cross:
                obstructions.append({
                    "type": "cap5_cross_double_row_trigger",
                    "slice": s, "j_s": j_s, "i_s": i_s,
                    "nonown_rows": dict(nonown_row_groups),
                    "explanation": "e_B >= 2 from two non-own row groups, "
                                 "e_C >= 1 from cross-pair sharing → e_B+e_C >= 3 > 2",
                })
    
    return {
        "sat": len(obstructions) == 0,
        "n_obstructions": len(obstructions),
        "obstructions": obstructions[:5],  # cap for output
    }


def solve_base_2sat(caps, sharing_set):
    """Original base 2-SAT."""
    from excess_geometry_2sat import solve_purity_2sat
    return solve_purity_2sat(caps, sharing_set)


def main():
    t0 = time.time()
    rng = np.random.default_rng(42)
    
    DIRS_BY_WT = {}
    for d in range(1, 256):
        w = bin(d).count('1')
        DIRS_BY_WT.setdefault(w, []).append(d)
    w1 = DIRS_BY_WT[1]
    w2 = DIRS_BY_WT[2]
    
    # Test: weight-30 supports (most relevant)
    print("=== Weight-30: base 2-SAT vs extended 2-SAT vs review-strengthened ===")
    base_s = ext_s = verification_s = 0
    total = 0
    N = 50000
    
    for _ in range(N):
        extra = sorted(rng.choice(w2, size=11, replace=False).tolist())
        support = sorted(set(w1 + extra))
        if len(support) != 19:
            continue
        caps = support_capacities(support)
        if min(caps) < 3:
            continue
        total += 1
        
        _, sharing_set = compute_sharing_details(support)
        
        base = solve_base_2sat(caps, sharing_set)
        if base["sat"]: base_s += 1
        
        from extended_2sat import solve_extended_purity_2sat
        ext = solve_extended_purity_2sat(caps, sharing_set)
        if ext["sat"]: ext_s += 1
        
        verification_r = check_strengthened_obstructions(support)
        if verification_r["sat"]: verification_s += 1
    
    print(f"  Total valid: {total}")
    print(f"  Base 2-SAT survivors:     {base_s} ({100*base_s/total:.2f}%)")
    print(f"  Extended 2-SAT survivors:  {ext_s} ({100*ext_s/total:.2f}%)")
    print(f"  review-strengthened:         {verification_s} ({100*verification_s/total:.2f}%)")
    
    # Low-weight targeted
    print("\n=== Low-weight (27-40): comparison ===")
    pool = [d for d in range(1, 256) if bin(d).count('1') <= 3]
    b3 = e3 = t3 = 0; tot3 = 0
    for _ in range(20000):
        base_dirs = list(w1)
        extra = sorted(rng.choice(pool, size=11, replace=False).tolist())
        support = sorted(set(base_dirs + extra))
        if len(support) != 19:
            continue
        caps = support_capacities(support)
        w = sum(caps)
        if w > 40 or min(caps) < 3:
            continue
        tot3 += 1
        _, sharing_set = compute_sharing_details(support)
        
        base = solve_base_2sat(caps, sharing_set)
        if base["sat"]: b3 += 1
        
        ext = solve_extended_purity_2sat(caps, sharing_set)
        if ext["sat"]: e3 += 1
        
        verification_r = check_strengthened_obstructions(support)
        if verification_r["sat"]: t3 += 1
    
    if tot3:
        print(f"  Total valid: {tot3}")
        print(f"  Base 2-SAT:    {b3} ({100*b3/tot3:.1f}%)")
        print(f"  Extended:      {e3} ({100*e3/tot3:.1f}%)")
        print(f"  Strengthened:  {t3} ({100*t3/tot3:.1f}%)")
    
    payload = {
        "weight30": {
            "total": total,
            "base_sat": base_s, "ext_sat": ext_s, "verification_sat": verification_s,
        },
        "low_weight": {
            "total": tot3,
            "base_sat": b3, "ext_sat": e3, "verification_sat": t3,
        },
        "elapsed_sec": round(time.time() - t0, 3),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"\nSaved to {OUT}")


if __name__ == "__main__":
    main()
