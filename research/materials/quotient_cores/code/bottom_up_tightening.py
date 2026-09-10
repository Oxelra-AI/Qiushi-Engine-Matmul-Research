#!/usr/bin/env python3
"""Bottom-up LUT tightening: check if dim-5 and dim-6 LB values are exact.

For a dim-d subspace W, LB(W) is a lower bound on R(T/W). The quotient tensor
T/W has A-dimension 9-d, giving 2^{9-d}-1 nonzero A-directions.

The occupation system for T/W at target LB(W)+1 uses descendant LUT entries:
for each dim-(d+1) subspace V ⊃ W, the constraint is
    |support ∩ (V/W)| ≤ target - LB(V)

If this system is infeasible, we can raise LB(W) to LB(W)+1.

For dim 5 (A-dim 4): 15 nonzero directions, ~15 dim-6 descendants
For dim 6 (A-dim 3): 7 nonzero directions, ~7 dim-7 descendants
"""
from __future__ import annotations
import json, os, pickle, sys, time
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
LUT_PATH = SCRIPT_DIR / ".." / ".." / ".." / ".." / "data/wang_f2_lb20/wang_subspace_lut.pkl"
OUTDIR = SESSION / "workspace/data/wang_analysis"
OUTDIR.mkdir(parents=True, exist_ok=True)

def unpack_basis(key):
    k = int(key)
    d = k & 0xF
    x = k >> 4
    basis = []
    for _ in range(d):
        basis.append(x & 0x1FF)
        x >>= 9
    return basis

def pack_basis(basis):
    d = len(basis)
    x = 0
    for i, b in enumerate(basis):
        x |= (int(b) << (9 * i))
    return (x << 4) | d

def rref_basis(basis):
    """Reduced row echelon form of basis vectors over GF(2)."""
    rows = [int(b) for b in basis if b]
    # Sort by highest bit, descending
    rows.sort(key=lambda x: x.bit_length(), reverse=True)
    rref = []
    for v in rows:
        for rb in rref:
            top = rb.bit_length() - 1
            if top >= 0 and (v >> top) & 1:
                v ^= rb
        if v == 0:
            continue
        # Reduce existing rows
        for i in range(len(rref)):
            top = v.bit_length() - 1
            if top >= 0 and (rref[i] >> top) & 1:
                rref[i] ^= v
        rref.append(v)
    rref.sort(key=lambda x: x.bit_length(), reverse=True)
    return tuple(rref)

def in_span(point, rref):
    v = int(point)
    for rb in rref:
        top = rb.bit_length() - 1
        if top >= 0 and (v >> top) & 1:
            v ^= rb
    return v == 0

def quotient_project(point, rref):
    """Project a 9-bit point to quotient F2^9 / span(rref)."""
    v = int(point)
    for rb in rref:
        top = rb.bit_length() - 1
        if top >= 0 and (v >> top) & 1:
            v ^= rb
    # v now has zero in all pivot positions; read off free bits
    pivots = set(rb.bit_length() - 1 for rb in rref if rb)
    free_bits = sorted([i for i in range(9) if i not in pivots])
    q = 0
    for qi, fi in enumerate(free_bits):
        if (v >> fi) & 1:
            q |= (1 << qi)
    return q

def find_child_hyperplanes(W_rref, q_dim, lut):
    """Find all dim-(d+1) subspaces containing W.
    
    These correspond to hyperplanes in the quotient space F2^q_dim.
    Each nonzero vector in F2^q_dim defines a hyperplane (its kernel under
    the standard inner product).
    
    Returns: list of (child_key, child_lb, quotient_hyperplane_mask)
    """
    d = len(W_rref)
    pivots = set(rb.bit_length() - 1 for rb in W_rref if rb)
    free_bits = sorted([i for i in range(9) if i not in pivots])
    
    results = []
    # Each nonzero q in F2^q_dim defines a hyperplane H_q = {p : <p,q>=0}
    # The corresponding child is W + span{lift(q)}
    for q in range(1, 1 << q_dim):
        # Lift q back to F2^9
        lift = 0
        for qi, fi in enumerate(free_bits):
            if (q >> qi) & 1:
                lift |= (1 << fi)
        
        # Child basis = W ∪ {lift}
        child_basis = list(W_rref) + [lift]
        child_rref = rref_basis(child_basis)
        child_key = pack_basis(child_rref)
        
        child_lb = lut.get(child_key)
        if child_lb is None:
            # Try matching by RREF
            continue
        
        # Hyperplane mask: which of the 2^q_dim - 1 quotient points are in H_q?
        # H_q = {p in F2^q_dim : <p,q> = 0 (standard inner product)}
        mask = 0
        for p in range(1, 1 << q_dim):
            if bin(p & q).count('1') % 2 == 0:
                mask |= (1 << (p - 1))  # point p maps to bit p-1 in mask
        
        results.append({
            "q_vector": q,
            "child_key": child_key,
            "child_lb": child_lb,
            "hyperplane_mask": mask,
            "hyperplane_size": bin(mask).count('1'),
        })
    
    return results

def check_occupation_feasibility(n_points, target, constraints):
    """Check if a target-size multiset from n_points can satisfy all constraints.
    
    Each constraint: (mask, cap) meaning sum of x_p for p in mask <= cap.
    Uses simple enumeration or CP-SAT for small problems.
    """
    try:
        from ortools.sat.python import cp_model
        model = cp_model.CpModel()
        # Variables: x_p for each nonzero point (0..mult_max)
        xs = [model.NewIntVar(0, target, f'x_{p}') for p in range(n_points)]
        model.Add(sum(xs) == target)
        
        for mask, cap in constraints:
            pts_in_mask = [p for p in range(n_points) if (mask >> p) & 1]
            if pts_in_mask:
                model.Add(sum(xs[p] for p in pts_in_mask) <= cap)
        
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = 10
        status = solver.Solve(model)
        
        if status == cp_model.FEASIBLE or status == cp_model.OPTIMAL:
            sol = [solver.Value(x) for x in xs]
            return {"feasible": True, "solution": sol}
        elif status == cp_model.INFEASIBLE:
            return {"feasible": False, "proven": True}
        else:
            return {"feasible": None, "proven": False, "status": str(status)}
    except ImportError:
        return {"feasible": None, "error": "ortools not available"}

def main():
    t0 = time.time()
    
    with open(LUT_PATH, "rb") as f:
        data = pickle.load(f)
    lut = data['lut']
    meta = data['meta']
    
    # Get orbit representatives for dim 5 and dim 6
    orbits_by_dim = defaultdict(list)
    for orb in meta['orbit_sizes']:
        orbits_by_dim[orb['dim']].append(orb)
    
    print("=== Bottom-up tightening check ===\n")
    
    results = {"dim6": [], "dim5": []}
    
    # --- DIM 6 first (simpler: 7 quotient points) ---
    print("--- Dim 6 orbits (q_dim=3, 7 points) ---")
    dim6_orbits = orbits_by_dim[6]
    n_checked_6 = 0
    n_tightened_6 = 0
    
    # Find one representative key for each orbit
    dim6_by_lb = defaultdict(list)
    for key, lb_val in lut.items():
        basis = unpack_basis(key)
        if len(basis) == 6:
            dim6_by_lb[lb_val].append(key)
    
    # Check a sample from each LB level
    for lb_val in sorted(dim6_by_lb.keys()):
        keys = dim6_by_lb[lb_val][:3]  # check up to 3 per LB level
        for key in keys:
            basis = unpack_basis(key)
            W_rref = rref_basis(basis)
            q_dim = 9 - len(W_rref)
            assert q_dim == 3
            
            target = lb_val + 1
            n_pts = (1 << q_dim) - 1  # 7
            
            children = find_child_hyperplanes(W_rref, q_dim, lut)
            
            # Build constraints
            constraints = []
            for ch in children:
                cap = target - ch["child_lb"]
                if cap < 0:
                    # Immediately infeasible
                    constraints.append((ch["hyperplane_mask"], cap))
                    break
                constraints.append((ch["hyperplane_mask"], cap))
            
            result = check_occupation_feasibility(n_pts, target, constraints)
            
            if result.get("feasible") == False:
                n_tightened_6 += 1
                print(f"  LB={lb_val} -> {lb_val+1} TIGHTENED! key={key}, children={len(children)}")
                results["dim6"].append({
                    "key": str(key), "old_lb": lb_val, "new_lb": lb_val+1,
                    "tightened": True, "children": len(children),
                })
            elif result.get("feasible") == True:
                results["dim6"].append({
                    "key": str(key), "old_lb": lb_val, "new_lb": lb_val,
                    "tightened": False, "solution": result.get("solution"),
                })
            else:
                results["dim6"].append({
                    "key": str(key), "old_lb": lb_val, "status": "unknown",
                })
            
            n_checked_6 += 1
    
    print(f"  Dim-6: checked {n_checked_6}, tightened {n_tightened_6}")
    
    # --- DIM 5 (15 quotient points) ---
    print("\n--- Dim 5 orbits (q_dim=4, 15 points) ---")
    dim5_by_lb = defaultdict(list)
    for key, lb_val in lut.items():
        basis = unpack_basis(key)
        if len(basis) == 5:
            dim5_by_lb[lb_val].append(key)
    
    n_checked_5 = 0
    n_tightened_5 = 0
    
    for lb_val in sorted(dim5_by_lb.keys()):
        keys = dim5_by_lb[lb_val][:2]  # check 2 per LB level
        for key in keys:
            basis = unpack_basis(key)
            W_rref = rref_basis(basis)
            q_dim = 9 - len(W_rref)
            assert q_dim == 4
            
            target = lb_val + 1
            n_pts = (1 << q_dim) - 1  # 15
            
            children = find_child_hyperplanes(W_rref, q_dim, lut)
            
            constraints = []
            neg_cap = False
            for ch in children:
                cap = target - ch["child_lb"]
                if cap < 0:
                    neg_cap = True
                constraints.append((ch["hyperplane_mask"], cap))
            
            if neg_cap:
                print(f"  LB={lb_val} -> {lb_val+1} TRIVIALLY TIGHTENED (negative cap)")
                n_tightened_5 += 1
                results["dim5"].append({
                    "key": str(key), "old_lb": lb_val, "new_lb": lb_val+1,
                    "tightened": True, "reason": "negative_cap",
                })
                n_checked_5 += 1
                continue
            
            result = check_occupation_feasibility(n_pts, target, constraints)
            
            if result.get("feasible") == False:
                n_tightened_5 += 1
                print(f"  LB={lb_val} -> {lb_val+1} TIGHTENED! key={key}, children={len(children)}")
                results["dim5"].append({
                    "key": str(key), "old_lb": lb_val, "new_lb": lb_val+1,
                    "tightened": True, "children": len(children),
                })
            elif result.get("feasible") == True:
                results["dim5"].append({
                    "key": str(key), "old_lb": lb_val, "new_lb": lb_val,
                    "tightened": False,
                })
            else:
                results["dim5"].append({
                    "key": str(key), "old_lb": lb_val, "status": "unknown",
                })
            
            n_checked_5 += 1
    
    print(f"  Dim-5: checked {n_checked_5}, tightened {n_tightened_5}")
    
    elapsed = time.time() - t0
    
    out_data = {
        "dim6_checked": n_checked_6,
        "dim6_tightened": n_tightened_6,
        "dim5_checked": n_checked_5,
        "dim5_tightened": n_tightened_5,
        "details": results,
        "elapsed_sec": round(elapsed, 2),
    }
    
    out = OUTDIR / "bottom_up_tightening_pilot.json"
    out.write_text(json.dumps(out_data, indent=2, sort_keys=True) + "\n")
    print(f"\nSaved {out}")

if __name__ == "__main__":
    main()
