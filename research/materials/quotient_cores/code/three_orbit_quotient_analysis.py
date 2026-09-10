#!/usr/bin/env python3
"""Three-orbit quotient analysis for R_{F2}(T_{3,3,3}) >= 21.

If R = 20, pick any term's A-factor u_t (nonzero 3x3 matrix over F2).
Quotient by span(u_t): the quotient has rank <= 19. Since GL3 x GL3 acts
on A-factors with 3 orbits (rank 1, 2, 3), checking three representatives
suffices. If all three quotients have no 19-point Wang-admissible support,
then R >= 21.

Rank-1 representative: E_{00} = value 1 (the E11 case)
Rank-2 representative: E_{00}+E_{11} = value 17
Rank-3 representative: I_3 = E_{00}+E_{11}+E_{22} = value 273
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
OUTDIR = SESSION / "workspace/data/wang_native/three_orbit"

PIVOTS = {
    'rank1': {'value': 1, 'name': 'E00', 'matrix': '[[1,0,0],[0,0,0],[0,0,0]]'},
    'rank2': {'value': 17, 'name': 'E00+E11', 'matrix': '[[1,0,0],[0,1,0],[0,0,0]]'},
    'rank3': {'value': 273, 'name': 'I3', 'matrix': '[[1,0,0],[0,1,0],[0,0,1]]'},
}

def matrix_rank_f2(val):
    """Compute rank of 3x3 F2 matrix encoded as 9-bit value."""
    rows = [0, 0, 0]
    for idx in range(9):
        if (val >> idx) & 1:
            i, j = divmod(idx, 3)
            rows[i] |= 1 << j
    # Gaussian elimination on 3-bit rows
    rank = 0
    basis = [0, 0, 0]
    for r in rows:
        x = r
        while x:
            p = x.bit_length() - 1
            if basis[p]:
                x ^= basis[p]
            else:
                basis[p] = x
                rank += 1
                break
    return rank

def in_span(point, basis_vecs):
    """Check if point is in span of basis_vecs over F2."""
    x = point
    # Sort by descending bit length (pivot position)
    for b in sorted(basis_vecs, key=lambda v: -(v.bit_length())):
        if x == 0: return True
        hb = b.bit_length() - 1
        if (x >> hb) & 1:
            x ^= b
    return x == 0

def quotient_project(a, pivot):
    """Project 9-bit value a to 8-bit quotient by span(pivot).
    Returns 0 if a is in span(pivot), else a nonzero 8-bit value."""
    if a == 0: return 0
    if a == pivot: return 0
    h = pivot.bit_length() - 1  # highest bit of pivot
    if (a >> h) & 1:
        a ^= pivot  # clear the h-th bit by XOR with pivot
    # Now bit h of a is 0. Remove bit position h.
    low = a & ((1 << h) - 1)
    high = (a >> (h + 1)) << h
    return low | high

def prepare_quotient_constraints(lut, pivot, target):
    """Extract Wang constraints for quotient by span(pivot) at given target."""
    rows = []
    total_containing = 0
    skip_cap = 0
    skip_empty = 0
    
    for key9, lb0 in lut.items():
        key9 = int(key9)
        basis = list(unpack_basis(key9))
        # Check if pivot is in this subspace
        if not in_span(pivot, basis):
            continue
        total_containing += 1
        
        lb = int(lb0)
        cap = target - lb
        if cap <= 0 or cap >= target:
            skip_cap += 1
            continue
        
        # Generate all subspace points and project to quotient
        d = len(basis)
        qpts = set()
        for m in range(1, 1 << d):
            v = 0
            for i, b in enumerate(basis):
                if (m >> i) & 1:
                    v ^= b
            qp = quotient_project(v, pivot)
            if qp > 0:
                qpts.add(qp)
        
        if not qpts:
            skip_empty += 1
            continue
        if cap >= len(qpts):  # always satisfied
            continue
        
        rows.append((cap, frozenset(qpts)))
    
    return rows, total_containing, skip_cap, skip_empty

def evaluate(support_fset, constraints):
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
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--samples", type=int, default=30)
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--pivots", nargs='+', default=['rank1', 'rank2', 'rank3'])
    args = ap.parse_args()
    
    random.seed(args.seed)
    OUTDIR.mkdir(parents=True, exist_ok=True)
    
    print("Loading LUT...")
    t0 = time.time()
    lut, _ = load_lut(LUT_PATH)
    print(f"  LUT entries: {len(lut)}, loaded in {time.time()-t0:.1f}s")
    
    # Verify pivot ranks
    for pname, pdata in PIVOTS.items():
        r = matrix_rank_f2(pdata['value'])
        print(f"  Pivot {pname}: value={pdata['value']}, matrix rank={r}, expected={pname[-1]}")
        assert str(r) == pname[-1], f"Rank mismatch for {pname}"
    
    all_results = {}
    
    for pname in args.pivots:
        pdata = PIVOTS[pname]
        pivot = pdata['value']
        print(f"\n{'='*60}")
        print(f"QUOTIENT BY span({pdata['name']}) [value={pivot}, {pname}]")
        print(f"{'='*60}")
        
        tp = time.time()
        constraints, total, skip_cap, skip_empty = prepare_quotient_constraints(
            lut, pivot, args.target)
        prep_time = time.time() - tp
        
        cap_hist = Counter(c for c, _ in constraints)
        
        print(f"  Total LUT rows containing pivot: {total}")
        print(f"  Skipped (cap<=0 or cap>=target): {skip_cap}")
        print(f"  Skipped (empty quotient mask): {skip_empty}")
        print(f"  Binding constraints: {len(constraints)}")
        print(f"  Cap histogram: {dict(sorted(cap_hist.items())[:12])}")
        print(f"  Preparation time: {prep_time:.1f}s")
        
        # Random violation diagnostic
        available = list(range(1, 256))
        violations = []
        best_viol = float('inf')
        best_support = None
        
        for i in range(args.samples):
            support = frozenset(random.sample(available, args.target))
            vr, ve = evaluate(support, constraints)
            violations.append(vr)
            if vr < best_viol:
                best_viol = vr
                best_support = sorted(support)
            if (i+1) % 10 == 0:
                print(f"    sample {i+1}/{args.samples}: current={vr}, best={best_viol}")
        
        result = {
            "pivot_name": pname,
            "pivot_value": pivot,
            "pivot_matrix": pdata['matrix'],
            "target": args.target,
            "total_containing_rows": total,
            "binding_constraints": len(constraints),
            "cap_histogram": dict(sorted(cap_hist.items())),
            "samples": len(violations),
            "min_violations": min(violations) if violations else None,
            "max_violations": max(violations) if violations else None,
            "mean_violations": sum(violations) / len(violations) if violations else None,
            "best_support": best_support,
            "preparation_sec": prep_time,
        }
        all_results[pname] = result
        
        print(f"  RESULT: min {result['min_violations']} / "
              f"max {result['max_violations']} / "
              f"mean {result['mean_violations']:.1f} violated rows")
    
    # Comparison
    print(f"\n{'='*60}")
    print("COMPARATIVE SUMMARY")
    print(f"{'='*60}")
    for pname in args.pivots:
        r = all_results[pname]
        print(f"  {pname} ({r['pivot_matrix']}): "
              f"{r['binding_constraints']} constraints, "
              f"violations {r['min_violations']}-{r['max_violations']} "
              f"(mean {r['mean_violations']:.1f})")
    
    out_path = OUTDIR / f"three_orbit_diagnostic_n{args.target}.json"
    with open(out_path, "w") as f:
        json.dump(all_results, f, indent=2)
    print(f"\nSaved {out_path}")

if __name__ == "__main__":
    main()
