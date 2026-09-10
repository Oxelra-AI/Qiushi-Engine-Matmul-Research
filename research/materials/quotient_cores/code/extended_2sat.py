#!/usr/bin/env python3
"""analysisd: Extended 2-SAT with cap-5 forced purity from cross-group sharing.

Extension: if a cap-5 slice shares terms with cap-3 slices from BOTH non-own
row groups, e_B >= 2 (linearly independent outside-block projections), forcing
e_C = 0 (C-pure).  Similarly for column groups.  These become unit clauses
in the 2-SAT.

We also track the weaker single-group case (e_B >= 1 from one non-own group).
"""
import json, time, sys
from pathlib import Path
from collections import Counter
from itertools import combinations
import numpy as np

sys.path.insert(0, str(Path("scripts")))
from excess_geometry_2sat import (
    support_capacities, support_sharing, CROSS_PAIRS, LATIN_TRIPLES, SLICE_BLOCKS
)

ROOT = Path("research/research_record")
OUT = ROOT / "workspace/data/excess_geometry/extended_2sat_analysis.json"


def solve_extended_purity_2sat(caps, sharing):
    """Extended 2-SAT with cap-5 forced purity from cross-group sharing.
    
    Returns dict with sat, forced, obstructions, and extension info.
    """
    # Build base clauses
    clauses = []
    
    # Cap-3: forced both pure
    for s in range(8):
        if caps[s] <= 3:
            clauses.append([2*s+1])   # B_s
            clauses.append([2*s+2])   # C_s
    
    # Cap-4: at least one pure
    for s in range(8):
        if caps[s] == 4:
            clauses.append([2*s+1, 2*s+2])
    
    # Sharing incompatibility
    for s1, s2 in sharing:
        j1, i1 = SLICE_BLOCKS[s1]
        j2, i2 = SLICE_BLOCKS[s2]
        if j1 != j2:
            clauses.append([-(2*s1+1), -(2*s2+1)])
        if i1 != i2:
            clauses.append([-(2*s1+2), -(2*s2+2)])
    
    # ── Cap-5 extension ──
    extension_info = {"cap5_forced_B": [], "cap5_forced_C": [], 
                      "cap5_single_B_leak": [], "cap5_single_C_leak": []}
    
    for s in range(8):
        if caps[s] != 5:
            continue
        j_s, i_s = SLICE_BLOCKS[s]
        
        # Find cap-3 slices sharing with s and their row/col groups
        sharing_cap3_j = set()  # row groups of sharing cap-3 slices
        sharing_cap3_i = set()  # col groups of sharing cap-3 slices
        for s2 in range(8):
            if caps[s2] > 3:
                continue
            pair = (min(s, s2), max(s, s2))
            if pair not in sharing:
                continue
            j2, i2 = SLICE_BLOCKS[s2]
            if j2 != j_s:
                sharing_cap3_j.add(j2)
            if i2 != i_s:
                sharing_cap3_i.add(i2)
        
        # Two non-own row groups → e_B >= 2 → force C-pure
        if len(sharing_cap3_j) >= 2:
            clauses.append([2*s+2])  # C_s = True
            extension_info["cap5_forced_C"].append(s)
        elif len(sharing_cap3_j) == 1:
            extension_info["cap5_single_B_leak"].append(s)
        
        # Two non-own col groups → e_C >= 2 → force B-pure
        if len(sharing_cap3_i) >= 2:
            clauses.append([2*s+1])  # B_s = True
            extension_info["cap5_forced_B"].append(s)
        elif len(sharing_cap3_i) == 1:
            extension_info["cap5_single_C_leak"].append(s)
    
    # Solve 2-SAT with DPLL
    n = 16
    def propagate(asgn, cls):
        asgn = dict(asgn)
        changed = True
        while changed:
            changed = False
            new_cls = []
            for cl in cls:
                simp = []
                sat = False
                for lit in cl:
                    v = abs(lit) - 1
                    if v in asgn:
                        if (lit > 0) == asgn[v]:
                            sat = True; break
                    else:
                        simp.append(lit)
                if sat: continue
                if not simp: return None
                if len(simp) == 1:
                    v = abs(simp[0]) - 1
                    val = simp[0] > 0
                    if v in asgn:
                        if asgn[v] != val: return None
                    else:
                        asgn[v] = val; changed = True
                new_cls.append(simp)
            cls = new_cls
        return asgn, cls

    def dpll(asgn, cls):
        result = propagate(asgn, cls)
        if result is None: return None
        asgn, cls = result
        if not cls: return asgn
        for cl in cls:
            for lit in cl:
                v = abs(lit) - 1
                if v not in asgn:
                    for val in [True, False]:
                        test = dict(asgn); test[v] = val
                        sol = dpll(test, cls)
                        if sol is not None: return sol
                    return None
        return asgn

    sol = dpll({}, clauses)
    sat = sol is not None
    out = {"sat": sat, "n_clauses": len(clauses), "extension": extension_info}
    
    if sat:
        base = propagate({}, clauses)
        forced = base[0] if base else {}
        out["forced_count"] = len(forced)
    
    return out


def main():
    t0 = time.time()
    rng = np.random.default_rng(42)
    
    # Weight-1 and weight-2 directions
    DIRS_BY_WT = {}
    for d in range(1, 256):
        w = bin(d).count('1')
        DIRS_BY_WT.setdefault(w, []).append(d)
    
    w1 = DIRS_BY_WT[1]  # 8 dirs
    w2 = DIRS_BY_WT[2]  # 28 dirs
    
    # --- Test 1: Base vs Extended on weight-30 supports ---
    print("=== Weight-30 (8 wt-1 + 11 wt-2): base vs extended 2-SAT ===")
    base_sat = 0; ext_sat = 0; ext_only = 0; both_unsat = 0; total = 0
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
        sharing = support_sharing(support)
        
        # Base 2-SAT (no cap-5 extension)
        from excess_geometry_2sat import solve_purity_2sat
        base = solve_purity_2sat(caps, sharing)
        ext = solve_extended_purity_2sat(caps, sharing)
        
        if base["sat"]: base_sat += 1
        if ext["sat"]: ext_sat += 1
        if base["sat"] and not ext["sat"]: ext_only += 1
        if not base["sat"] and not ext["sat"]: both_unsat += 1
    
    print(f"  Valid supports: {total}")
    print(f"  Base 2-SAT: {base_sat} SAT ({100*base_sat/total:.1f}%)")
    print(f"  Extended:    {ext_sat} SAT ({100*ext_sat/total:.1f}%)")
    print(f"  Extension-only kills: {ext_only}")
    print(f"  Improvement: {100*(base_sat-ext_sat)/max(base_sat,1):.1f}% of base survivors eliminated")
    
    # --- Test 2: Low-weight targeted (27-40) ---
    print("\n=== Low-weight targeted (27-40): base vs extended ===")
    pool = [d for d in range(1, 256) if bin(d).count('1') <= 3]
    b2_sat = 0; e2_sat = 0; e2_only = 0; t2 = 0
    cap5_extensions = Counter()
    
    for _ in range(20000):
        # Mix weight-1 base + weight ≤ 3 additions
        base_dirs = list(w1)
        extra = sorted(rng.choice(pool, size=11, replace=False).tolist())
        support = sorted(set(base_dirs + extra))
        if len(support) != 19:
            continue
        caps = support_capacities(support)
        w = sum(caps)
        if w > 40 or min(caps) < 3:
            continue
        t2 += 1
        sharing = support_sharing(support)
        
        base_r = solve_purity_2sat(caps, sharing)
        ext_r = solve_extended_purity_2sat(caps, sharing)
        
        if base_r["sat"]: b2_sat += 1
        if ext_r["sat"]: e2_sat += 1
        if base_r["sat"] and not ext_r["sat"]: e2_only += 1
        
        ext = ext_r["extension"]
        if ext["cap5_forced_B"] or ext["cap5_forced_C"]:
            cap5_extensions["extended"] += 1
    
    if t2:
        print(f"  Valid supports: {t2}")
        print(f"  Base 2-SAT: {b2_sat} SAT ({100*b2_sat/t2:.1f}%)")
        print(f"  Extended:    {e2_sat} SAT ({100*e2_sat/t2:.1f}%)")
        print(f"  Extension-only kills: {e2_only}")
        print(f"  Cap-5 extensions triggered: {cap5_extensions.get('extended', 0)}")
        if b2_sat > 0:
            print(f"  Improvement: {100*(b2_sat-e2_sat)/b2_sat:.1f}% of base survivors")
    
    payload = {
        "weight30_comparison": {
            "total": total,
            "base_sat": base_sat, "ext_sat": ext_sat,
            "extension_only_kills": ext_only,
            "improvement_pct": round(100*(base_sat-ext_sat)/max(base_sat,1), 2),
        },
        "low_weight_comparison": {
            "total": t2,
            "base_sat": b2_sat, "ext_sat": e2_sat,
            "extension_only_kills": e2_only,
            "cap5_extensions": dict(cap5_extensions),
        },
        "elapsed_sec": round(time.time() - t0, 3),
    }
    
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"\nSaved to {OUT}")


if __name__ == "__main__":
    main()
