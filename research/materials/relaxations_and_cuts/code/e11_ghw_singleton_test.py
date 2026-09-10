#!/usr/bin/env python3
"""Generalized Hamming Weight vs Singleton bound for E11 core rank-19.

MATHEMATICAL FRAMEWORK:
Put the 19 distinct quotient A-directions q_1,...,q_19 ∈ F₂^8 into the columns
of an 8×19 matrix M.  C = rowspace(M) is a [19,8] binary code (rank 8 because
every hyperplane has capacity ≥ 3).

For a subspace Ψ ≤ F₂^8 of dim d, the annihilator A = Ψ^⊥ has dim r = 8-d.
The subcode D_A ≤ C has support {t : q_t ∉ Ψ}, and the Wang constraint gives
|supp(D_A)| ≥ LB(span(E₁₁, lift(Ψ))).

So the r-th generalized Hamming weight satisfies:
  d_r(C) ≥ L_r := min_{dim(V)=9-r, E₁₁∈V} LB(V)

The generalized Singleton bound:
  d_r(C) ≤ n - k + r = 19 - 8 + r = 11 + r

DECISIVE: if L_r > 11 + r for any r, there is no admissible [19,8] code,
proving the E11 core has rank ≥ 20 over F₂.

IMPLEMENTATION: Iterates over all 8.2M entries in the Wang LUT, using an O(1)
packed-key check to identify E₁₁-containing subspaces (the packed RREF key has
last row = 1 iff E₁₁ is in the span).
"""
import json
import pickle
import time
from collections import defaultdict
from pathlib import Path

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = Path("data/ghw_singleton")
OUTDIR.mkdir(parents=True, exist_ok=True)

MASK9 = (1 << 9) - 1


def key_contains_e11(key: int) -> bool:
    """O(1) check: does the RREF subspace contain E₁₁ = 1?
    
    In the packed format, the last RREF row (lowest pivot) is at the highest
    bit position.  The subspace contains 1 iff that row is exactly 1.
    
    Proof: In RREF over F₂, the row with pivot at position 0 has bit 0 = 1
    and all other pivot-position bits = 0.  Non-pivot bits may be nonzero.
    To check if 1 ∈ rowspace: start from v=1, only the pivot-0 row can clear
    bit 0 (since other rows have bit 0 = 0 in RREF).  After XOR with the
    pivot-0 row, remaining bits are at non-pivot positions and cannot be cleared
    by any row.  So v reduces to 0 iff the pivot-0 row is exactly 1.
    """
    d = key & 0xF
    if d == 0:
        return False
    last_row = (key >> (4 + 9 * (d - 1))) & MASK9
    return last_row == 1


def main():
    t0 = time.time()
    
    print("Loading Wang LUT...")
    with open(LUT_PATH, "rb") as f:
        payload = pickle.load(f)
    lut = payload["lut"]
    meta = payload.get("meta", {})
    print(f"  LUT entries: {len(lut)}")
    
    # Track min/max LB by 9-bit dimension for E11-containing subspaces
    min_lb = {}   # dim9 -> min LB
    max_lb = {}   # dim9 -> max LB
    count = defaultdict(int)
    lb_hist = defaultdict(lambda: defaultdict(int))
    
    # Also track all-subspace stats for comparison
    all_min_lb = {}
    all_count = defaultdict(int)
    
    n_e11 = 0
    
    for key, lb_val in lut.items():
        dim9 = key & 0xF
        all_count[dim9] += 1
        if dim9 not in all_min_lb or lb_val < all_min_lb[dim9]:
            all_min_lb[dim9] = lb_val
        
        if key_contains_e11(key):
            n_e11 += 1
            count[dim9] += 1
            lb_hist[dim9][lb_val] += 1
            
            if dim9 not in min_lb or lb_val < min_lb[dim9]:
                min_lb[dim9] = lb_val
            if dim9 not in max_lb or lb_val > max_lb[dim9]:
                max_lb[dim9] = lb_val
    
    elapsed = time.time() - t0
    
    print(f"\nTotal LUT entries: {len(lut)}")
    print(f"E₁₁-containing subspaces: {n_e11}")
    print(f"Expected E₁₁-containing: 417199")
    
    # Verify count by dimension
    # Expected: subspaces of F₂^8 by dim d8 -> E11-containing at dim d9 = d8+1
    expected_d8 = {0: 1, 1: 255, 2: 10795, 3: 97155, 4: 200787, 5: 97155, 6: 10795, 7: 255, 8: 1}
    print(f"\nE₁₁-containing by dim9: {dict(sorted(count.items()))}")
    expected_d9 = {d+1: c for d, c in expected_d8.items()}
    print(f"Expected (dim9=dim8+1): {dict(sorted(expected_d9.items()))}")
    match = all(count.get(d9, 0) == c for d9, c in expected_d9.items())
    print(f"Count match: {match}")
    
    # Compute L_r and check Singleton
    print("\n" + "=" * 72)
    print("GENERALIZED HAMMING WEIGHT vs SINGLETON BOUND FOR E11 RANK-19")
    print("=" * 72)
    print(f"Code parameters: n=19, k=8")
    print(f"Singleton bound: d_r ≤ n - k + r = 11 + r")
    print(f"Wang constraint: d_r ≥ L_r = min_{{dim(V)=9-r, E₁₁∈V}} LB(V)")
    print()
    print(f"{'r':>3} {'dim9':>5} {'#subsp':>8} {'L_r':>5} {'max_lb':>7} "
          f"{'Singleton':>10} {'gap':>5} {'RESULT':>12}")
    print("-" * 62)
    
    results = []
    violation_found = False
    
    for r in range(0, 9):
        dim9 = 9 - r
        singleton = 11 + r
        
        lr = min_lb.get(dim9, None)
        mx = max_lb.get(dim9, None)
        cnt = count.get(dim9, 0)
        
        if lr is None:
            gap_str = "---"
            result_str = "NO DATA"
        else:
            gap = singleton - lr
            if lr > singleton:
                result_str = "*** VIOLATE ***"
                violation_found = True
            elif lr == singleton:
                result_str = "TIGHT"
            else:
                result_str = f"slack {gap}"
            gap_str = str(gap)
        
        print(f"{r:>3} {dim9:>5} {cnt:>8} {lr if lr is not None else '':>5} "
              f"{mx if mx is not None else '':>7} {singleton:>10} {gap_str:>5} "
              f"{result_str:>12}")
        
        results.append({
            "r": r,
            "dim9": dim9,
            "dim8": dim9 - 1,
            "subspace_count": cnt,
            "L_r": lr,
            "max_lb": mx,
            "singleton_bound": singleton,
            "gap": singleton - lr if lr is not None else None,
            "result": result_str.strip(),
            "lb_histogram": dict(sorted(lb_hist.get(dim9, {}).items(),
                                        key=lambda x: x[0])),
        })
    
    print("-" * 62)
    
    if violation_found:
        print("\n*** SINGLETON VIOLATION: No [19,8] binary code satisfies all Wang")
        print("*** constraints. The E11 core has rank ≥ 20 over F₂! ***")
    else:
        print("\nNo Singleton violation found.")
        print("The generalized weight hierarchy is compatible with a [19,8] code.")
        
        # Report tightest constraints
        tightest = min(results[1:], key=lambda x: x["gap"] if x["gap"] is not None else 999)
        print(f"Tightest constraint: r={tightest['r']}, L_r={tightest['L_r']}, "
              f"Singleton={tightest['singleton_bound']}, gap={tightest['gap']}")
    
    # Compare with all-subspace min LBs
    print("\n\nComparison: min LB for ALL subspaces vs E₁₁-containing only:")
    print(f"{'dim9':>5} {'all_min':>8} {'e11_min':>8} {'diff':>6}")
    for d9 in sorted(set(list(all_min_lb.keys()) + list(min_lb.keys()))):
        a = all_min_lb.get(d9)
        e = min_lb.get(d9)
        diff = (e - a) if (a is not None and e is not None) else None
        print(f"{d9:>5} {a if a is not None else '':>8} {e if e is not None else '':>8} "
              f"{diff if diff is not None else '':>6}")
    
    # Validate against known rank-21 pool
    print("\n\nValidation: known rank-21 decompositions should form valid codes.")
    import numpy as np
    import sys
    sys.path.insert(0, str(Path("scripts")))
    from core_capacity_from_wang_lut import CoreQuotient
    
    core = CoreQuotient(pivot=1)
    pool = np.load("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
    N_rows = pool.shape[0]
    R = pool.shape[1] // 3
    
    for row_idx in range(min(N_rows, 10)):
        row = pool[row_idx]
        q_set = set()
        for t in range(R):
            u = int(row[3*t])
            q = core.project9(u)
            if q != 0:
                q_set.add(q)
        
        # Compute code rank
        basis = [0] * 8
        rank = 0
        for q in sorted(q_set):
            v = q
            for p in range(7, -1, -1):
                if (v >> p) & 1:
                    if basis[p]:
                        v ^= basis[p]
                    else:
                        basis[p] = v
                        rank += 1
                        break
        
        # Compute actual GHW values
        # d_1 = min weight of C
        min_wt = 19
        for mask in range(1, 1 << 8):
            wt = 0
            for q in sorted(q_set):
                dot = 0
                v = mask & q
                while v:
                    dot ^= (v & 1)
                    v >>= 1
                wt += dot
            if 0 < wt < min_wt:
                min_wt = wt
        
        print(f"  Row {row_idx}: {len(q_set)} distinct quotient dirs, rank {rank}, "
              f"d_1(C)={min_wt}")
    
    # Save results
    output = {
        "status": "ok",
        "test": "ghw_singleton_e11_core_rank19",
        "code_params": {"n": 19, "k": 8},
        "violation_found": violation_found,
        "e11_containing_subspaces": n_e11,
        "results_by_r": results,
        "elapsed_sec": elapsed,
    }
    
    outpath = OUTDIR / "ghw_singleton_test.json"
    with open(outpath, "w") as f:
        json.dump(output, f, indent=2, sort_keys=True)
    print(f"\nSaved to {outpath}")


if __name__ == "__main__":
    main()
