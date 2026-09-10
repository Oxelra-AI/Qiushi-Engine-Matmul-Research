#!/usr/bin/env python3
"""Stochastic violation minimizer for Wang occupation constraints.

For a target length n and a set of available points, find a support of size n
that minimizes the number of Wang constraint violations. A violation occurs when
|S ∩ mask(U)| > cap(U) = n - LB(U) for a subspace U.

Modes:
  --mode full --target 20: all 511 nonzero F2^9 points, full Wang system
  --mode e11  --target 19: 255 nonzero E11 quotient points, E11 Wang rows

Uses the raw Python LUT for correctness. Hill-climbing with incremental updates.
"""
import argparse, json, os, pickle, random, sys, time
from pathlib import Path

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, unpack_basis
from core_capacity_from_wang_lut import load_lut

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent

MASK9 = (1 << 9) - 1

def contains_e11(key):
    d = key & 0xF
    return d > 0 and (((key >> (4 + 9 * (d - 1))) & MASK9) == 1)

def key9_to_basis8(key9):
    raw = []
    for b in unpack_basis(key9):
        if b == 1: continue
        q = int(b)
        if q & 1: q ^= 1
        q8 = 0
        for bit in range(1, 9):
            if (q >> bit) & 1:
                q8 |= 1 << (bit - 1)
        if q8: raw.append(q8)
    return tuple(rref_basis(raw, n=8)) if raw else ()

def points_from_basis(basis, maxpt):
    d = len(basis)
    pts = set()
    for m in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis):
            if (m >> i) & 1: v ^= b
        if 1 <= v <= maxpt: pts.add(v)
    return frozenset(pts)

def prepare_constraints(lut, mode, target):
    """Return list of (cap, point_frozenset) for binding constraints."""
    rows = []
    npts = 255 if mode == 'e11' else 511
    skipped_trivial = 0
    for key9, lb0 in lut.items():
        lb = int(lb0)
        cap = target - lb
        if cap < 0 or cap >= target:
            skipped_trivial += 1
            continue
        
        if mode == 'e11':
            if not contains_e11(key9): continue
            basis8 = key9_to_basis8(int(key9))
            pts = points_from_basis(basis8, 255)
        else:
            basis = list(unpack_basis(int(key9)))
            pts = points_from_basis(basis, 511)
        
        if not pts: continue
        if cap >= len(pts):  # always satisfied
            continue
        rows.append((cap, pts))
    
    return rows, npts

def evaluate(support_set, constraints):
    """Count violations."""
    total_viol = 0
    violated_rows = 0
    for cap, pts in constraints:
        occ = len(support_set & pts)
        if occ > cap:
            total_viol += occ - cap
            violated_rows += 1
    return violated_rows, total_viol

def hill_climb(support, available, constraints, max_iters=500):
    """Greedy hill-climbing: try swapping each selected point with unselected."""
    best_rows, best_excess = evaluate(support, constraints)
    improved = True
    iters = 0
    while improved and iters < max_iters and best_rows > 0:
        improved = False
        iters += 1
        candidates = list(support)
        random.shuffle(candidates)
        for p_out in candidates:
            new_support = support - {p_out}
            best_swap = None
            best_swap_score = (best_rows, best_excess)
            for p_in in available - support:
                trial = new_support | {p_in}
                vr, ve = evaluate(trial, constraints)
                if (vr, ve) < best_swap_score:
                    best_swap_score = (vr, ve)
                    best_swap = p_in
            if best_swap is not None and best_swap_score < (best_rows, best_excess):
                support = (support - {p_out}) | {best_swap}
                best_rows, best_excess = best_swap_score
                improved = True
                if best_rows == 0:
                    break
        if not improved:
            break
    return support, best_rows, best_excess, iters

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", required=True, choices=["full", "e11"])
    ap.add_argument("--target", type=int, required=True)
    ap.add_argument("--restarts", type=int, default=50)
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--timeout", type=float, default=300)
    args = ap.parse_args()
    
    random.seed(args.seed)
    t0 = time.time()
    
    print(f"Loading LUT from {LUT_PATH}...")
    lut, _ = load_lut(LUT_PATH)
    print(f"  LUT entries: {len(lut)}")
    
    print(f"Preparing constraints for mode={args.mode}, target={args.target}...")
    constraints, npts = prepare_constraints(lut, args.mode, args.target)
    print(f"  Binding constraints: {len(constraints)} (npts={npts})")
    
    # Cap histogram
    cap_hist = {}
    for cap, pts in constraints:
        cap_hist[cap] = cap_hist.get(cap, 0) + 1
    print(f"  Cap histogram: {dict(sorted(cap_hist.items()))}")
    
    available = set(range(1, npts + 1))
    best_overall = None
    best_viol_rows = float('inf')
    best_excess = float('inf')
    results = []
    
    for restart in range(args.restarts):
        if time.time() - t0 > args.timeout:
            print(f"  Timeout after {restart} restarts")
            break
        
        # Random initial support
        support = set(random.sample(list(available), args.target))
        
        # Quick eval
        vr0, ve0 = evaluate(support, constraints)
        
        # Hill-climb
        support, vr, ve, iters = hill_climb(support, available, constraints, max_iters=200)
        
        results.append({
            "restart": restart,
            "initial_violated_rows": vr0,
            "initial_excess": ve0,
            "final_violated_rows": vr,
            "final_excess": ve,
            "hill_climb_iters": iters,
        })
        
        if vr < best_viol_rows or (vr == best_viol_rows and ve < best_excess):
            best_viol_rows = vr
            best_excess = ve
            best_overall = sorted(support)
        
        elapsed = time.time() - t0
        print(f"  restart {restart}: {vr0}→{vr} viol_rows, {ve0}→{ve} excess, "
              f"{iters} iters, best={best_viol_rows}/{best_excess}, {elapsed:.1f}s")
        
        if best_viol_rows == 0:
            print("  FOUND ZERO-VIOLATION SUPPORT!")
            break
    
    elapsed = time.time() - t0
    outdir = SESSION / "workspace/data/wang_native/stochastic_min"
    outdir.mkdir(parents=True, exist_ok=True)
    
    summary = {
        "mode": args.mode,
        "target": args.target,
        "npts": npts,
        "binding_constraints": len(constraints),
        "restarts_completed": len(results),
        "best_violated_rows": best_viol_rows,
        "best_excess": best_excess,
        "best_support": best_overall,
        "violation_floor_across_restarts": min(r["final_violated_rows"] for r in results),
        "elapsed_sec": elapsed,
    }
    
    out_path = outdir / f"stochastic_min_{args.mode}_n{args.target}.json"
    with open(out_path, "w") as f:
        json.dump(summary, f, indent=2)
    print(f"\nSaved {out_path}")
    print(f"RESULT: best {best_viol_rows} violated rows, {best_excess} total excess")

if __name__ == "__main__":
    main()
