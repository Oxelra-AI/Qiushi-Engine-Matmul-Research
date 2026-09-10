#!/usr/bin/env python3
"""CORRECTED bottom-up LB tightening with proper constraint model.

For a dim-d node W, the occupation constraint from child V_q (dim d+1):
    x_q <= target - LB(V_q)     [POINT constraint, not hyperplane]

Optionally also include grandchild constraints (dim d+2):
    sum_{p in H_V'} x_p <= target - LB(V')  [HYPERPLANE constraint]

The previous version incorrectly used hyperplane masks for immediate children.
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

def pack_basis(basis_rref):
    d = len(basis_rref)
    x = 0
    for i, b in enumerate(basis_rref):
        x |= (int(b) << (9 * i))
    return (x << 4) | d

def rref_basis(basis):
    rows = [int(b) for b in basis if b]
    rows.sort(key=lambda x: x.bit_length(), reverse=True)
    rref = []
    for v in rows:
        for rb in rref:
            top = rb.bit_length() - 1
            if top >= 0 and (v >> top) & 1:
                v ^= rb
        if v == 0:
            continue
        for i in range(len(rref)):
            top = v.bit_length() - 1
            if top >= 0 and (rref[i] >> top) & 1:
                rref[i] ^= v
        rref.append(v)
    rref.sort(key=lambda x: x.bit_length(), reverse=True)
    return tuple(rref)

def get_free_bits(rref):
    pivots = set(rb.bit_length() - 1 for rb in rref if rb)
    return sorted([i for i in range(9) if i not in pivots])

def lift_quotient_point(q, free_bits):
    """Lift a quotient point back to F2^9."""
    v = 0
    for qi, fi in enumerate(free_bits):
        if (q >> qi) & 1:
            v |= (1 << fi)
    return v

def check_point_only(n_pts, target, point_caps):
    """Point-only feasibility: sum x_q = target, x_q <= cap_q for each q.
    Feasible iff sum min(x_q, cap_q) >= target, i.e., sum cap_q >= target.
    """
    total_cap = sum(max(0, c) for c in point_caps.values())
    return total_cap >= target

def check_with_cpsat(n_pts, target, point_caps, hyperplane_constraints):
    """Full feasibility check with both point and hyperplane constraints."""
    try:
        from ortools.sat.python import cp_model
        model = cp_model.CpModel()
        xs = [model.NewIntVar(0, target, f'x_{p}') for p in range(n_pts)]
        model.Add(sum(xs) == target)
        
        # Point constraints from immediate children
        for q_idx, cap in point_caps.items():
            if cap < 0:
                model.Add(xs[q_idx] == 0)  # impossible to use this point
                if False:  # The point is forbidden, but the problem might still be feasible
                    pass
            else:
                model.Add(xs[q_idx] <= cap)
        
        # Hyperplane constraints from grandchildren
        for mask, cap in hyperplane_constraints:
            pts = [p for p in range(n_pts) if (mask >> p) & 1]
            if pts:
                model.Add(sum(xs[p] for p in pts) <= max(0, cap))
        
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = 5
        status = solver.Solve(model)
        
        if status in (cp_model.FEASIBLE, cp_model.OPTIMAL):
            return {"feasible": True, "solution": [solver.Value(x) for x in xs]}
        elif status == cp_model.INFEASIBLE:
            return {"feasible": False}
        else:
            return {"feasible": None, "status": str(status)}
    except ImportError:
        return {"feasible": None, "error": "no ortools"}

def main():
    t0 = time.time()
    
    with open(LUT_PATH, "rb") as f:
        data = pickle.load(f)
    lut = data['lut']
    meta = data['meta']
    
    # Build index by dimension
    keys_by_dim = defaultdict(list)
    for key in lut:
        basis = unpack_basis(key)
        keys_by_dim[len(basis)].append(key)
    
    print("=== CORRECTED Bottom-up tightening ===\n")
    
    results = {}
    
    for target_dim in [6, 5, 4]:
        q_dim = 9 - target_dim
        n_pts = (1 << q_dim) - 1
        
        print(f"\n--- Dim {target_dim} (q_dim={q_dim}, {n_pts} points) ---")
        
        # Sample keys by LB level
        by_lb = defaultdict(list)
        for key in keys_by_dim[target_dim]:
            by_lb[lut[key]].append(key)
        
        dim_results = []
        n_checked = 0
        n_tightened_point = 0
        n_tightened_full = 0
        
        for lb_val in sorted(by_lb.keys()):
            samples = by_lb[lb_val][:3]
            for key in samples:
                basis = unpack_basis(key)
                W_rref = rref_basis(basis)
                free_bits = get_free_bits(W_rref)
                
                target = lb_val + 1
                
                # Find immediate children (dim+1) and their LBs
                point_caps = {}
                missing_children = 0
                for q in range(1, 1 << q_dim):
                    lift_v = lift_quotient_point(q, free_bits)
                    child_basis = list(W_rref) + [lift_v]
                    child_rref = rref_basis(child_basis)
                    child_key = pack_basis(child_rref)
                    child_lb = lut.get(child_key)
                    if child_lb is None:
                        missing_children += 1
                        point_caps[q-1] = target  # unknown = no constraint
                    else:
                        point_caps[q-1] = target - child_lb
                
                # Point-only check
                point_feasible = check_point_only(n_pts, target, point_caps)
                
                if not point_feasible:
                    n_tightened_point += 1
                    n_tightened_full += 1
                    cap_list = [point_caps.get(i, target) for i in range(n_pts)]
                    cap_sum = sum(max(0, c) for c in cap_list)
                    
                    print(f"  LB={lb_val} -> {lb_val+1} POINT-TIGHTENED! "
                          f"cap_sum={cap_sum} < target={target}, "
                          f"missing={missing_children}")
                    
                    dim_results.append({
                        "key": str(key), "old_lb": lb_val, "new_lb": lb_val+1,
                        "tightened": True, "method": "point_only",
                        "cap_sum": cap_sum, "target": target,
                        "caps": {str(k): v for k,v in point_caps.items()},
                        "missing_children": missing_children,
                    })
                else:
                    # Try with grandchild hyperplane constraints too
                    hyperplane_constraints = []
                    for key2 in keys_by_dim.get(target_dim + 2, []):
                        # Check if this grandchild contains W
                        # This is expensive; skip for now and just report point result
                        pass
                    
                    # For now, report that point-only is feasible
                    cap_list = [point_caps.get(i, target) for i in range(n_pts)]
                    cap_sum = sum(max(0, c) for c in cap_list)
                    child_lbs = []
                    for q in range(1, 1 << q_dim):
                        lift_v = lift_quotient_point(q, free_bits)
                        child_basis = list(W_rref) + [lift_v]
                        child_rref = rref_basis(child_basis)
                        child_key = pack_basis(child_rref)
                        child_lb = lut.get(child_key)
                        child_lbs.append(child_lb)
                    
                    # Try CP-SAT with point constraints only
                    cpsat_result = check_with_cpsat(n_pts, target, point_caps, [])
                    
                    print(f"  LB={lb_val}: point cap_sum={cap_sum} >= target={target} → "
                          f"FEASIBLE (child LBs: {Counter(child_lbs)}), "
                          f"cpsat={cpsat_result.get('feasible')}")
                    
                    dim_results.append({
                        "key": str(key), "old_lb": lb_val,
                        "tightened": False, "method": "point_only",
                        "cap_sum": cap_sum, "target": target,
                        "child_lb_hist": dict(Counter(child_lbs)),
                        "cpsat_feasible": cpsat_result.get("feasible"),
                    })
                
                n_checked += 1
        
        print(f"\n  Summary: checked {n_checked}, point-tightened {n_tightened_point}")
        results[f"dim{target_dim}"] = {
            "checked": n_checked, "tightened_point": n_tightened_point,
            "details": dim_results,
        }
    
    elapsed = time.time() - t0
    results["elapsed_sec"] = round(elapsed, 2)
    
    out = OUTDIR / "bottom_up_corrected_pilot.json"
    out.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n")
    print(f"\nSaved {out}")

if __name__ == "__main__":
    main()
