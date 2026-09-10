#!/usr/bin/env python3
"""analysis: Low-excess factor geometry, purity-side 2-SAT, and structural obstructions
for E11 core decompositions over F₂.

Mathematical foundation:
  Sylvester rank inequality on slice factorizations B_s C_s^T = M_s (rank 3):
    rank(B_s) + rank(C_s) ≤ capacity(s) + 3
  With rank(B_s) ≥ 3, rank(C_s) ≥ 3:
    excess e_B + e_C ≤ capacity(s) - 3  where e_B = rank(B_s) - 3, e_C = rank(C_s) - 3
  
  Cap-3: e_B = e_C = 0 (two-sided purity)
  Cap-4: at least one of e_B, e_C = 0 (one-sided purity)
  
  Global purity-side 2-SAT:
    Variables: B_s (B-pure for slice s), C_s (C-pure for slice s)
    Cap-3: B_s ∧ C_s (unit clauses, both forced)
    Cap-4: B_s ∨ C_s (at least one)
    Sharing + diff row group: ¬B_s1 ∨ ¬B_s2
    Sharing + diff col group: ¬C_s1 ∨ ¬C_s2

Novel A-level obstructions:
  Cross-pair: cap-3 sharing with cap-4 at different (j,i) ⟹ immediate UNSAT
  Latin triple: 3 mutually-sharing cap-≤4 slices, pairwise diff j and i ⟹ UNSAT
"""
from __future__ import annotations
import json, sys, time
from collections import Counter
from itertools import combinations
from pathlib import Path

import numpy as np

ROOT = Path("research/research_record")
POOL_PATH = Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
OUT_DIR = ROOT / "workspace/data/excess_geometry"
GROUPS = [0b000000111, 0b000111000, 0b111000000]  # R_0=C_0, R_1=C_1, R_2=C_2
FULL9 = (1 << 9) - 1


def slice_block(s: int) -> tuple[int, int]:
    """Core slice s -> (j, i) = (row_group, col_group)."""
    a = s + 1
    return a % 3, a // 3


def gf2_rank(M: np.ndarray) -> int:
    A = np.array(M, dtype=np.uint8, copy=True) & 1
    if A.ndim == 1:
        return 1 if A.any() else 0
    if A.shape[0] == 0:
        return 0
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = -1
        for i in range(r, m):
            if A[i, c]:
                piv = i; break
        if piv < 0: continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(m):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
        if r == m: break
    return r


def mask_to_vec9(m: int) -> np.ndarray:
    return np.array([(m >> b) & 1 for b in range(9)], dtype=np.uint8)


# ── Precompute structural invariants ──

SLICE_BLOCKS = [slice_block(s) for s in range(8)]

# Cross pairs: slice pairs with different j AND different i
CROSS_PAIRS: list[tuple[int, int]] = []
for s1 in range(8):
    j1, i1 = SLICE_BLOCKS[s1]
    for s2 in range(s1 + 1, 8):
        j2, i2 = SLICE_BLOCKS[s2]
        if j1 != j2 and i1 != i2:
            CROSS_PAIRS.append((s1, s2))

# Latin triples: 3 slices with pairwise different j and i
LATIN_TRIPLES: list[tuple[int, int, int]] = []
for triple in combinations(range(8), 3):
    js = {SLICE_BLOCKS[s][0] for s in triple}
    ii = {SLICE_BLOCKS[s][1] for s in triple}
    if len(js) == 3 and len(ii) == 3:
        LATIN_TRIPLES.append(triple)


# ── Excess computation from actual B/C factors ──

def compute_slice_excess(vs: list[int], ws: list[int], j: int, i: int) -> dict:
    m = len(vs)
    B = np.array([mask_to_vec9(v) for v in vs])
    C = np.array([mask_to_vec9(w) for w in ws])
    r_B = gf2_rank(B)
    r_C = gf2_rank(C)
    B_out = np.array([mask_to_vec9(v & (FULL9 ^ GROUPS[j])) for v in vs])
    C_out = np.array([mask_to_vec9(w & (FULL9 ^ GROUPS[i])) for w in ws])
    e_B = gf2_rank(B_out)
    e_C = gf2_rank(C_out)
    return {"m": m, "r_B": int(r_B), "r_C": int(r_C),
            "e_B": int(e_B), "e_C": int(e_C),
            "B_pure": e_B == 0, "C_pure": e_C == 0,
            "sylvester_ok": r_B + r_C <= m + 3,
            "excess_ok": e_B + e_C <= m - 3}


# ── A-support level: capacities and sharing ──

def support_capacities(us: list[int]) -> list[int]:
    caps = [0] * 8
    for u in us:
        for s in range(8):
            if (u >> s) & 1:
                caps[s] += 1
    return caps


def support_sharing(us: list[int]) -> set[tuple[int, int]]:
    sharing: set[tuple[int, int]] = set()
    for u in us:
        active = [s for s in range(8) if (u >> s) & 1]
        for s1, s2 in combinations(active, 2):
            sharing.add((s1, s2))
    return sharing


# ── 2-SAT solver (DPLL for ≤16 variables) ──

def solve_purity_2sat(caps: list[int], sharing: set[tuple[int, int]]) -> dict:
    """Build and solve the purity-side 2-SAT.
    Variables 2*s = B_pure(s), 2*s+1 = C_pure(s).
    Literals: positive = var+1, negative = -(var+1).
    """
    clauses: list[list[int]] = []
    for s in range(8):
        if caps[s] <= 3:
            clauses.append([2 * s + 1])      # B_pure forced
            clauses.append([2 * s + 2])      # C_pure forced
        elif caps[s] == 4:
            clauses.append([2 * s + 1, 2 * s + 2])  # at least one
    for s1, s2 in sharing:
        j1, i1 = SLICE_BLOCKS[s1]
        j2, i2 = SLICE_BLOCKS[s2]
        if j1 != j2:
            clauses.append([-(2 * s1 + 1), -(2 * s2 + 1)])
        if i1 != i2:
            clauses.append([-(2 * s1 + 2), -(2 * s2 + 2)])

    n = 16
    # DPLL with unit propagation
    def propagate(asgn: dict[int, bool], cls: list[list[int]]):
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
                if sat:
                    continue
                if not simp:
                    return None  # conflict
                if len(simp) == 1:
                    v = abs(simp[0]) - 1
                    val = simp[0] > 0
                    if v in asgn:
                        if asgn[v] != val:
                            return None
                    else:
                        asgn[v] = val
                        changed = True
                        new_cls.append(simp)
                        continue
                new_cls.append(simp)
            cls = new_cls
        return asgn, cls

    def dpll(asgn: dict[int, bool], cls: list[list[int]]):
        result = propagate(asgn, cls)
        if result is None:
            return None
        asgn, cls = result
        if not cls:
            return asgn
        # pick unset variable from first remaining clause
        for cl in cls:
            for lit in cl:
                v = abs(lit) - 1
                if v not in asgn:
                    for val in [True, False]:
                        test = dict(asgn); test[v] = val
                        sol = dpll(test, cls)
                        if sol is not None:
                            return sol
                    return None
        return asgn

    sol = dpll({}, clauses)
    sat = sol is not None
    out = {"sat": sat, "n_clauses": len(clauses)}

    if sat:
        # count forced variables (those set by unit propagation alone)
        base = propagate({}, clauses)
        forced = base[0] if base else {}
        out["forced_count"] = len(forced)
        out["forced"] = {
            ("B_pure" if v % 2 == 0 else "C_pure") + f"_s{v // 2}": forced[v]
            for v in sorted(forced)
        }
    else:
        # identify which obstructions triggered
        obs = []
        for s1, s2 in CROSS_PAIRS:
            if (s1, s2) not in sharing:
                continue
            a, b = min(s1, s2), max(s1, s2)
            if caps[a] <= 3 and caps[b] <= 4:
                obs.append({"type": "cross_cap3_cap4", "cap3": a, "cap4": b})
            elif caps[b] <= 3 and caps[a] <= 4:
                obs.append({"type": "cross_cap3_cap4", "cap3": b, "cap4": a})
        for trip in LATIN_TRIPLES:
            if not all(caps[s] <= 4 for s in trip):
                continue
            if all((min(a, b), max(a, b)) in sharing for a, b in combinations(trip, 2)):
                obs.append({"type": "latin_triple", "slices": list(trip)})
        out["obstructions"] = obs
    return out


# ── Main analysis ──

def main() -> None:
    t0 = time.time()
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    print("=== E11 core structure ===")
    print(f"Slice blocks: {SLICE_BLOCKS}")
    print(f"Cross pairs ({len(CROSS_PAIRS)}): {CROSS_PAIRS}")
    print(f"Latin triples ({len(LATIN_TRIPLES)}):")
    for lt in LATIN_TRIPLES:
        print(f"  {lt} -> blocks {[SLICE_BLOCKS[s] for s in lt]}")

    # ── Part 1: Pool verification ──
    pool = np.load(POOL_PATH)
    N, cols = pool.shape
    R = cols // 3
    print(f"\n=== Part 1: Rank-{R} pool ({N} rows) excess verification ===")

    all_sylvester = True
    all_excess = True
    excess_hist: Counter = Counter()  # (cap, e_B, e_C)
    cap4_count = 0
    cap4_oneside = 0
    sat_2sat = 0
    unsat_2sat = 0
    forced_counts: list[int] = []
    cross_obs_in_pool = 0

    for idx in range(N):
        row = pool[idx]
        us = [int(row[3 * t]) for t in range(R)]
        vs_all = [int(row[3 * t + 1]) for t in range(R)]
        ws_all = [int(row[3 * t + 2]) for t in range(R)]
        caps = support_capacities(us)
        sharing = support_sharing(us)

        for s in range(8):
            j, i = SLICE_BLOCKS[s]
            active = [t for t in range(R) if (us[t] >> s) & 1]
            if not active:
                continue
            exc = compute_slice_excess([vs_all[t] for t in active],
                                       [ws_all[t] for t in active], j, i)
            if not exc["sylvester_ok"]:
                all_sylvester = False
            if not exc["excess_ok"]:
                all_excess = False
            excess_hist[(exc["m"], exc["e_B"], exc["e_C"])] += 1
            if exc["m"] == 4:
                cap4_count += 1
                if exc["B_pure"] or exc["C_pure"]:
                    cap4_oneside += 1

        res = solve_purity_2sat(caps, sharing)
        if res["sat"]:
            sat_2sat += 1
            forced_counts.append(res["forced_count"])
        else:
            unsat_2sat += 1
            if res.get("obstructions"):
                cross_obs_in_pool += 1

    print(f"Sylvester: {all_sylvester}  |  Excess: {all_excess}")
    print(f"Cap-4: {cap4_oneside}/{cap4_count} one-sided pure")
    print(f"2-SAT: {sat_2sat} SAT, {unsat_2sat} UNSAT")
    if forced_counts:
        avg_forced = sum(forced_counts) / len(forced_counts)
        print(f"Forced vars: mean={avg_forced:.1f}, min={min(forced_counts)}, max={max(forced_counts)}")

    # Excess distribution
    cap_summary = {}
    for (m, eB, eC), cnt in sorted(excess_hist.items()):
        key = f"cap{m}"
        if key not in cap_summary:
            cap_summary[key] = {"total": 0, "excess_pairs": {}}
        cap_summary[key]["total"] += cnt
        cap_summary[key]["excess_pairs"][f"({eB},{eC})"] = cnt

    print("\nExcess distribution:")
    for k, v in sorted(cap_summary.items()):
        print(f"  {k}: {v['total']} total, {v['excess_pairs']}")

    # ── Part 2: Rank-19 structural analysis ──
    print("\n=== Part 2: Rank-19 structural analysis ===")

    # For each possible cap-3/cap-4 distribution in rank 19, check if ANY
    # sharing pattern can create a 2-SAT obstruction
    print("Cross-pair obstruction condition:")
    print("  If cap-3 slice s1 shares term with cap-4 slice s2, and (s1,s2) is a cross pair")
    print("  (different j AND different i), then s2 can be neither B-pure nor C-pure → UNSAT.")
    print(f"  There are {len(CROSS_PAIRS)} cross pairs and {len(LATIN_TRIPLES)} Latin triples.\n")

    # Enumerate cross-pair patterns for all 8 slices
    print("Row-group and col-group sharing constraints between slices:")
    for s1, s2 in CROSS_PAIRS:
        j1, i1 = SLICE_BLOCKS[s1]
        j2, i2 = SLICE_BLOCKS[s2]
        print(f"  ({s1},{s2}): blocks ({j1},{i1}) vs ({j2},{i2}) - diff j, diff i")

    # For rank-19, total weight >= 27.  Minimum cap-3 count p gives
    # remaining 8-p slices with cap >= 4.  For p cap-3 slices:
    # weight from cap-3 = 3p, remaining weight >= 4*(8-p) for cap >= 4.
    # Total: 3p + 4(8-p) = 32-p >= 27 iff p <= 5.  ✓
    # But also: 19 terms, each with weight >= 1.  Sum of caps = total weight.
    # If all cap-3: 8*3=24 terms active (counting multiplicity), total weight = 24.
    # Hmm no, total weight = sum of Hamming weights of 19 directions.
    
    # Analyze: for each pair of slices, what is the MINIMUM number of
    # shared terms (directions with both bits set)?
    # For slices s1, s2 with capacities m1, m2 in 19-term support:
    # Directions with bit s1: m1.  With bit s2: m2.  With neither: 19 - m1 - m2 + overlap.
    # Since we need 19 distinct nonzero F2^8 directions:
    # overlap = m1 + m2 - (19 - free), where free = |directions with neither bit|
    # Minimum overlap when free is maximized.
    # Each direction has at most 8 bits, so 19 directions use 19 positions in F2^8\{0} (max 255).
    # overlap >= max(0, m1 + m2 - 19)

    # For a cross pair (s1, s2) with cap-3 and cap-4:
    # overlap >= max(0, 3 + 4 - 19) = 0.
    # So sharing is NOT forced just by capacities — it depends on which directions are chosen.
    # This means the 2-SAT is a genuine filter, not a vacuous one.

    # Count: for the minimum total-weight case (p=5 cap-3, 3 cap-4, total=27):
    # Which cross pairs connect a cap-3 to a cap-4 slice?
    # This depends on which 5 of 8 slices are cap-3 and which 3 are cap-4.
    
    # For each assignment of 5 cap-3 slices, count cross pairs between cap-3 and cap-4
    print("\n--- Enumeration: 5 cap-3 + 3 cap-4 configurations ---")
    from math import comb
    total_configs = comb(8, 5)
    configs_with_cross = 0
    cross_counts = Counter()
    for cap3_slices in combinations(range(8), 5):
        cap4_slices = [s for s in range(8) if s not in cap3_slices]
        n_cross = 0
        for s1, s2 in CROSS_PAIRS:
            if (s1 in cap3_slices and s2 in cap4_slices) or \
               (s2 in cap3_slices and s1 in cap4_slices):
                n_cross += 1
        cross_counts[n_cross] += 1
        if n_cross > 0:
            configs_with_cross += 1

    print(f"  Total 5-of-8 configurations: {total_configs}")
    print(f"  Configs with ≥1 cap3-cap4 cross pair: {configs_with_cross}/{total_configs}")
    print(f"  Cross pair count distribution: {dict(sorted(cross_counts.items()))}")
    print("  → ANY sharing in a cross pair forces UNSAT for that support.")

    # Also: Latin triple analysis for all cap-4 (p=0 case)
    print("\n--- Latin triple analysis for 8 cap-4 slices ---")
    print(f"  {len(LATIN_TRIPLES)} Latin triples exist.")
    print("  If all 8 slices are cap-4 and any Latin triple has mutual sharing → UNSAT.")
    print("  A direction with Hamming weight ≥ 3 hitting all three slices of a Latin triple")
    print("  creates mutual sharing → immediate UNSAT.")

    # For each Latin triple, which weight-3+ directions hit all three?
    for lt in LATIN_TRIPLES:
        mask = 0
        for s in lt:
            mask |= (1 << s)
        # Count 8-bit nonzero vectors with bits at all positions in mask
        hits = 0
        for v in range(1, 256):
            if v & mask == mask:
                hits += 1
        print(f"  Triple {lt}: any of {hits} directions (out of 255) creates mutual sharing")

    # ── Build output ──
    excess_json = {}
    for (m, eB, eC), cnt in sorted(excess_hist.items()):
        excess_json[f"cap{m}_eB{eB}_eC{eC}"] = cnt

    payload = {
        "schema": "s0908_excess_geometry_2sat_v1",
        "theorem": {
            "statement": "For E11 core slice with capacity m and block (R_j, C_i): "
                        "e_B + e_C ≤ m-3 where e_B = rank(B_s)-3, e_C = rank(C_s)-3. "
                        "Cap-3: two-sided purity. Cap-4: one-sided purity.",
            "proof": "Sylvester: rank(B_s C_s^T) ≥ rank(B_s)+rank(C_s)-m. "
                    "Since B_s C_s^T = M_s has rank 3: rank(B_s)+rank(C_s) ≤ m+3. "
                    "col(M_s)⊆span(B_s), row(M_s)⊆span(C_s) ⟹ rank(B_s)≥3, rank(C_s)≥3.",
        },
        "structure": {
            "slice_blocks": {str(s): list(SLICE_BLOCKS[s]) for s in range(8)},
            "cross_pairs": [[s1, s2] for s1, s2 in CROSS_PAIRS],
            "cross_pair_count": len(CROSS_PAIRS),
            "latin_triples": [list(lt) for lt in LATIN_TRIPLES],
            "latin_triple_count": len(LATIN_TRIPLES),
        },
        "obstructions": {
            "cross_pair_cap3_cap4": "Cap-3 slice forces both B-pure and C-pure. "
                                   "A sharing cap-4 slice in a cross pair (diff j AND diff i) "
                                   "is forced ¬B-pure AND ¬C-pure, contradicting cap-4 requirement.",
            "latin_triple_cap4": "Three mutually-sharing cap-≤4 slices in a Latin triple: "
                                "at most 1 B-pure (all j differ) + at most 1 C-pure (all i differ) "
                                "= at most 2 pure, but 3 needed → UNSAT.",
        },
        "pool_verification": {
            "pool_path": str(POOL_PATH),
            "rows": N, "terms_per_row": R,
            "sylvester_all_ok": all_sylvester,
            "excess_all_ok": all_excess,
            "cap4_oneside_pure": f"{cap4_oneside}/{cap4_count}",
            "twosat_sat": sat_2sat, "twosat_unsat": unsat_2sat,
            "forced_vars_mean": round(sum(forced_counts) / max(len(forced_counts), 1), 1),
            "forced_vars_min": min(forced_counts) if forced_counts else 0,
            "forced_vars_max": max(forced_counts) if forced_counts else 0,
            "excess_distribution": excess_json,
            "cap_summary": cap_summary,
        },
        "rank19_analysis": {
            "min_total_weight": 27,
            "max_cap3_slices": 5,
            "cap3_5_of_8_configs": {
                "total": total_configs,
                "with_cross_pair": configs_with_cross,
                "cross_count_dist": {str(k): v for k, v in sorted(cross_counts.items())},
            },
        },
        "elapsed_sec": round(time.time() - t0, 3),
    }

    outpath = OUT_DIR / "excess_geometry_2sat.json"
    outpath.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"\nSaved to {outpath}")
    print(f"Elapsed: {payload['elapsed_sec']}s")


if __name__ == "__main__":
    main()
