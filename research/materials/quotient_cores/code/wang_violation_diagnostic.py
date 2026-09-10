#!/usr/bin/env python3
"""Fast stochastic violation diagnostic for Wang constraints.

Evaluates many random supports against the complete Wang system to find
the minimum violation floor. No hill-climbing — just random sampling.
This is the fastest diagnostic: if no random support achieves 0 violations,
hill-climbing is needed; if many achieve 0, the exclusion route fails.
"""
import argparse, json, os, pickle, random, sys, time
from pathlib import Path
from collections import Counter

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

def contains_point(key, pt, npts):
    """Check if point pt is in the subspace defined by key."""
    d = key & 0xF
    if d == 0: return pt == 0
    basis = list(unpack_basis(key))
    # Check if pt is in span
    aug = list(basis) + [pt]
    r_orig = gf2_rank(basis, npts.bit_length())
    r_aug = gf2_rank(aug, npts.bit_length())
    return r_orig == r_aug

def gf2_rank(vecs, nbits):
    basis = [0] * nbits
    r = 0
    for v in vecs:
        x = v
        while x:
            p = x.bit_length() - 1
            if p >= nbits: break
            if basis[p]:
                x ^= basis[p]
            else:
                basis[p] = x
                r += 1
                break
    return r

def key9_to_basis8(key9):
    raw = []
    for b in unpack_basis(key9):
        if b == 1: continue
        q = int(b)
        if q & 1: q ^= 1
        q8 = 0
        for bit in range(1, 9):
            if (q >> bit) & 1: q8 |= 1 << (bit - 1)
        if q8: raw.append(q8)
    return tuple(rref_basis(raw, n=8)) if raw else ()

def points_from_basis(basis, maxpt):
    d = len(basis)
    pts = []
    for m in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis):
            if (m >> i) & 1: v ^= b
        if 1 <= v <= maxpt: pts.append(v)
    return frozenset(pts)

def prepare_e11_constraints(lut, target):
    """Prepare E11 constraints."""
    rows = []
    for key9, lb0 in lut.items():
        if not contains_e11(key9): continue
        lb = int(lb0)
        cap = target - lb
        if cap <= 0 or cap >= target: continue
        basis8 = key9_to_basis8(int(key9))
        pts = points_from_basis(basis8, 255)
        if not pts or cap >= len(pts): continue
        rows.append((cap, pts))
    return rows, 255

def prepare_full_constraints(lut, target):
    """Prepare full-tensor constraints."""
    rows = []
    for key9, lb0 in lut.items():
        lb = int(lb0)
        cap = target - lb
        if cap <= 0 or cap >= target: continue
        basis = list(unpack_basis(int(key9)))
        pts = points_from_basis(basis, 511)
        if not pts or cap >= len(pts): continue
        rows.append((cap, pts))
    return rows, 511

def evaluate_fast(support_fset, constraints):
    """Count violated rows and total excess."""
    viol_rows = 0
    total_excess = 0
    for cap, pts in constraints:
        occ = len(support_fset & pts)
        if occ > cap:
            viol_rows += 1
            total_excess += occ - cap
    return viol_rows, total_excess

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", required=True, choices=["full", "e11"])
    ap.add_argument("--target", type=int, required=True)
    ap.add_argument("--samples", type=int, default=100)
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--timeout", type=float, default=600)
    args = ap.parse_args()
    
    random.seed(args.seed)
    t0 = time.time()
    
    print(f"Loading LUT...")
    lut, _ = load_lut(LUT_PATH)
    print(f"  LUT entries: {len(lut)}, elapsed: {time.time()-t0:.1f}s")
    
    print(f"Preparing constraints for mode={args.mode}, target={args.target}...")
    if args.mode == 'e11':
        constraints, npts = prepare_e11_constraints(lut, args.target)
    else:
        constraints, npts = prepare_full_constraints(lut, args.target)
    prep_time = time.time() - t0
    print(f"  Binding constraints: {len(constraints)}, elapsed: {prep_time:.1f}s")
    
    cap_hist = Counter(c for c, _ in constraints)
    print(f"  Cap histogram: {dict(sorted(cap_hist.items())[:15])}")
    
    available = list(range(1, npts + 1))
    results = []
    best_viol = float('inf')
    best_support = None
    
    for i in range(args.samples):
        if time.time() - t0 > args.timeout:
            print(f"  Timeout after {i} samples")
            break
        
        support = frozenset(random.sample(available, args.target))
        vr, ve = evaluate_fast(support, constraints)
        results.append((vr, ve))
        
        if vr < best_viol:
            best_viol = vr
            best_support = sorted(support)
        
        if (i+1) % 10 == 0 or vr < best_viol + 5:
            elapsed = time.time() - t0
            print(f"  sample {i+1}: {vr} viol_rows, {ve} excess, "
                  f"best={best_viol}, {elapsed:.1f}s")
    
    elapsed = time.time() - t0
    viol_counts = [r[0] for r in results]
    
    outdir = SESSION / "workspace/data/wang_native/stochastic_min"
    outdir.mkdir(parents=True, exist_ok=True)
    
    summary = {
        "mode": args.mode,
        "target": args.target,
        "npts": npts,
        "binding_constraints": len(constraints),
        "samples": len(results),
        "min_violated_rows": min(viol_counts),
        "max_violated_rows": max(viol_counts),
        "mean_violated_rows": sum(viol_counts) / len(viol_counts),
        "median_violated_rows": sorted(viol_counts)[len(viol_counts)//2],
        "violation_histogram_head": dict(Counter(viol_counts).most_common(20)),
        "best_support": best_support,
        "elapsed_sec": elapsed,
        "cap_histogram": dict(sorted(cap_hist.items())),
    }
    
    out_path = outdir / f"violation_diagnostic_{args.mode}_n{args.target}.json"
    with open(out_path, "w") as f:
        json.dump(summary, f, indent=2)
    print(f"\nSaved {out_path}")
    print(f"RESULT: min {min(viol_counts)} / max {max(viol_counts)} / "
          f"mean {summary['mean_violated_rows']:.1f} violated rows across {len(results)} samples")

if __name__ == "__main__":
    main()
