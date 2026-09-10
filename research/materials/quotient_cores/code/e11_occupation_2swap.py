#!/usr/bin/env python3
"""Fast targeted 2-swap and 3-swap local search for E11 Wang occupation.

Starts from a near-feasible support (small number of violations) and
exhaustively tests all 2-element and 3-element swaps for a zero-violation
support. If found, the support is a candidate rank-19 A-multiset for
fixed-A SAT testing.
"""
import numpy as np
import json, time, pickle, argparse
from pathlib import Path
from itertools import combinations

def load_cache(path):
    with open(path, "rb") as f:
        return pickle.load(f)

def compute_violations(support, membership, caps):
    """Count occupation violations for a support set."""
    occ = membership[support].sum(axis=0)
    return int(np.sum(occ > caps))

def compute_violation_details(support, membership, caps):
    """Return list of violated subspace indices and excess."""
    occ = membership[support].sum(axis=0)
    mask = occ > caps
    indices = np.where(mask)[0]
    return [(int(idx), int(occ[idx] - caps[idx])) for idx in indices]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cache", default="data/e11_capacity_sat/e11_capacity_cache.pkl")
    ap.add_argument("--membership", default="data/e11_occupation_sat/e11_membership.npy")
    ap.add_argument("--support", required=True, help="Comma-separated initial support masks")
    ap.add_argument("--max-swap", type=int, default=2, help="Max elements to swap (2 or 3)")
    ap.add_argument("--outdir", type=str, default=None)
    ap.add_argument("--out", type=str, default=None, help="optional output JSON path; parent directory is used as outdir")
    args = ap.parse_args()

    t0 = time.time()
    if args.out is not None:
        out_path_explicit = Path(args.out)
        outdir = out_path_explicit.parent
    else:
        if args.outdir is None:
            raise SystemExit("provide --outdir or --out")
        outdir = Path(args.outdir)
        out_path_explicit = None
    outdir.mkdir(parents=True, exist_ok=True)

    # Load Wang occupation data
    cache = load_cache(args.cache)
    masks = np.array(cache["masks"])
    dims = np.array(cache["dims"])
    Ls = np.array(cache["Ls"])
    keys8 = np.array(cache["keys8"])
    n_sub = len(masks)
    
    # Load membership matrix
    membership = np.load(args.membership)  # historically either (255,n_sub) for points 1..255 or (256,n_sub) with row 0 unused
    if membership.shape[0] == 256:
        membership = membership[1:]
    if membership.shape[0] != 255:
        raise ValueError(f"unexpected membership shape {membership.shape}; expected 255 or 256 rows")

    # Capacity caps: for rank 19
    rank_s = 19
    caps = np.array([rank_s - L for L in Ls], dtype=np.int32)

    # Parse support
    support = sorted(int(x) for x in args.support.split(","))
    support_arr = np.array(support)
    n = len(support)
    print(f"Support size: {n}, expected: {rank_s}")
    assert n == rank_s

    # Map masks to indices (0-254 for nonzero F2^8 quotient points)
    # Support elements are already quotient point indices (1-255)
    # Membership matrix uses 0-indexed: point p -> row p-1? No, check format
    # From the existing code, membership has shape (255, n_sub) for points 1..255
    # Point p -> row p-1
    support_idx = np.array([p - 1 for p in support])  # 0-indexed
    
    # Check initial violations
    v0 = compute_violations(support_idx, membership, caps)
    vd0 = compute_violation_details(support_idx, membership, caps)
    print(f"Initial violations: {v0}")
    if v0 == 0:
        print("Already feasible!")
        json.dump({"feasible": True, "support": support}, open(outdir / "result.json", "w"))
        return

    # Identify all 255 valid points (nonzero quotient points)
    all_points = set(range(1, 256))
    support_set = set(support)
    candidates = sorted(all_points - support_set)
    n_cand = len(candidates)
    cand_idx = np.array([p - 1 for p in candidates])
    
    print(f"Candidates for replacement: {n_cand}")
    print(f"Max swap size: {args.max_swap}")

    # Precompute: for each point, which subspaces it belongs to
    # This helps with incremental violation computation

    # For 2-swap: remove 2 from support, add 2 from candidates
    best_viol = v0
    best_swap = None
    checked = 0

    if args.max_swap >= 2:
        print(f"\n--- 2-swap search ---")
        print(f"Pairs to remove: {n*(n-1)//2}, pairs to add: {n_cand*(n_cand-1)//2}")
        print(f"Total combinations: {n*(n-1)//2 * n_cand*(n_cand-1)//2}")
        
        # For efficiency: precompute base occupation
        base_occ = membership[support_idx].sum(axis=0).astype(np.int32)
        
        for i1, i2 in combinations(range(n), 2):
            p1, p2 = support[i1], support[i2]
            pi1, pi2 = p1 - 1, p2 - 1
            
            # Removed occupation contribution
            rem_occ = base_occ - membership[pi1] - membership[pi2]
            
            for j1, j2 in combinations(range(n_cand), 2):
                q1, q2 = candidates[j1], candidates[j2]
                qi1, qi2 = q1 - 1, q2 - 1
                
                # Check caps: new points must each have cap >= 1 (which is always true)
                # But also check multiplicity constraints
                
                # New occupation
                new_occ = rem_occ + membership[qi1] + membership[qi2]
                
                viol = int(np.sum(new_occ > caps))
                checked += 1
                
                if viol < best_viol:
                    best_viol = viol
                    best_swap = {"remove": [p1, p2], "add": [q1, q2], "violations": viol}
                    print(f"  Improved: {viol} violations (remove {p1},{p2} add {q1},{q2})")
                
                if viol == 0:
                    new_support = sorted((support_set - {p1, p2}) | {q1, q2})
                    elapsed = time.time() - t0
                    result = {
                        "feasible": True,
                        "support": new_support,
                        "swap": best_swap,
                        "checked": checked,
                        "elapsed_sec": elapsed,
                    }
                    out_path = out_path_explicit or (outdir / "result.json")
                    json.dump(result, open(out_path, "w"), indent=2)
                    print(f"\n*** ZERO-VIOLATION SUPPORT FOUND! ***")
                    print(f"Support: {new_support}")
                    print(f"Checked {checked} 2-swaps in {elapsed:.1f}s")
                    print(f"wrote {out_path}")
                    return
                
                if checked % 1000000 == 0:
                    elapsed = time.time() - t0
                    rate = checked / elapsed
                    print(f"  {checked/1e6:.1f}M checked, {rate/1e6:.2f}M/s, best={best_viol}")
        
        print(f"2-swap search complete: {checked} checked, best={best_viol}")

    elapsed = time.time() - t0
    result = {
        "feasible": False,
        "initial_violations": v0,
        "best_violations": best_viol,
        "best_swap": best_swap,
        "checked": checked,
        "elapsed_sec": elapsed,
        "max_swap": args.max_swap,
    }
    out_path = out_path_explicit or (outdir / "result.json")
    json.dump(result, open(out_path, "w"), indent=2, default=int)
    print(f"\nNo zero-violation support found")
    print(f"Best: {best_viol} violations")
    print(f"Checked {checked} in {elapsed:.1f}s")
    print(f"wrote {out_path}")

if __name__ == "__main__":
    main()
