#!/usr/bin/env python3
"""CORRECTED capacity-feasibility test for E11 restricted core.

Key insight: The Wang dim-2 orbits are under the FULL group GL(3,2)×GL(3,2)⋊C2,
not under Stab(E11). Two functionals in the same Stab(E11) orbit can have
DIFFERENT Wang lower bounds. So we assign LBs per-functional using
invariants that distinguish the 6 Wang orbit types containing E11.

Classification of f' (9-bit functional with M11=0) by Wang orbit type:
1. rank(f')=1, f'*e1≠0 OR f'^T*e1≠0: LB=17 (E12/E21 type) [24 functionals]
2. rank(f')=1, f'*e1=0 AND f'^T*e1=0: LB=18 (E22 type) [9 functionals]
3. rank(f')=2, f'*e1≠0 AND f'^T*e1≠0: LB=18 (E12+E21 type)
4. rank(f')=2, exactly one of f'*e1, f'^T*e1 nonzero: LB=18 (E13+E22 type)
5. rank(f')=2, f'*e1=0 AND f'^T*e1=0: LB=18 (E23+E32 type) [6 functionals]
6. rank(f')=3: LB=18 (E13+E22+E31 type) [72 functionals]

Net: 24 functionals at LB=17, 231 at LB=18.
"""
import json
import numpy as np
from pathlib import Path
from collections import defaultdict

def mat_rank_f2(M):
    A = M.copy()
    n, m = A.shape
    rank = 0
    for col in range(m):
        pivot = None
        for row in range(rank, n):
            if A[row, col]: pivot = row; break
        if pivot is None: continue
        if pivot != rank: A[[rank, pivot]] = A[[pivot, rank]]
        for row in range(n):
            if row != rank and A[row, col]:
                A[row] = (A[row] + A[rank]) % 2
        rank += 1
    return rank

def mask_to_mat(v):
    M = np.zeros((3, 3), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            if v & (1 << (3*i+j)): M[i, j] = 1
    return M

def classify_functional(f_9bit):
    """Classify a 9-bit functional (with bit0=0) into a Wang orbit type.
    Returns the Wang lower bound for the [E11, f'] restriction."""
    F = mask_to_mat(f_9bit)
    assert F[0, 0] == 0, f"M11 must be 0, got {f_9bit}"
    
    rk = mat_rank_f2(F)
    e1 = np.array([1, 0, 0], dtype=np.uint8)
    Fe1 = (F @ e1) % 2       # First column of F
    FTe1 = (F.T @ e1) % 2    # First row of F (transposed)
    Fe1_nz = np.any(Fe1 != 0)
    FTe1_nz = np.any(FTe1 != 0)
    
    if rk == 1:
        if Fe1_nz or FTe1_nz:
            return 17, "E12_type"  # rank 1, touches e1
        else:
            return 18, "E22_type"  # rank 1, misses e1
    elif rk == 2:
        return 18, f"rank2_{Fe1_nz}_{FTe1_nz}"
    else:  # rk == 3
        return 18, "rank3"

def solve_capacity(target_rank, lb_table, verbose=True):
    """Solve capacity ILP with OR-Tools CP-SAT."""
    from ortools.sat.python import cp_model
    
    model = cp_model.CpModel()
    points = list(range(1, 256))
    x = {p: model.NewIntVar(0, target_rank, f'x_{p}') for p in points}
    model.Add(sum(x[p] for p in points) == target_rank)
    
    constraint_count = 0
    constraints_by_lb = defaultdict(int)
    
    for f_8bit in range(1, 256):
        lb = lb_table[f_8bit]
        if lb <= 0: continue
        
        capacity = target_rank - lb
        if capacity < 0:
            if verbose:
                print(f"  TRIVIALLY INFEASIBLE: LB={lb} > rank={target_rank} for f={f_8bit}")
            return "INFEASIBLE", None
        
        violators = [p for p in points if bin(f_8bit & p).count('1') % 2 == 1]
        model.Add(sum(x[p] for p in violators) <= capacity)
        constraint_count += 1
        constraints_by_lb[lb] += 1
    
    if verbose:
        print(f"  Constraints: {constraint_count} total, by LB: {dict(sorted(constraints_by_lb.items()))}")
    
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 120
    status = solver.Solve(model)
    
    status_name = {
        cp_model.OPTIMAL: "FEASIBLE",
        cp_model.FEASIBLE: "FEASIBLE",
        cp_model.INFEASIBLE: "INFEASIBLE",
        cp_model.UNKNOWN: "UNKNOWN",
    }.get(status, f"STATUS_{status}")
    
    solution = None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        solution = {p: solver.Value(x[p]) for p in points if solver.Value(x[p]) > 0}
    
    return status_name, solution

def verify_solution(solution, lb_table, target_rank):
    """Independently verify a solution against all constraints."""
    total = sum(solution.values())
    assert total == target_rank, f"Total points {total} != {target_rank}"
    
    violations = 0
    for f_8bit in range(1, 256):
        lb = lb_table[f_8bit]
        if lb <= 0: continue
        capacity = target_rank - lb
        
        count = 0
        for p, mult in solution.items():
            if bin(f_8bit & p).count('1') % 2 == 1:
                count += mult
        
        if count > capacity:
            violations += 1
    
    return violations

def main():
    outdir = Path("data/restricted_cores")
    outdir.mkdir(parents=True, exist_ok=True)
    
    print("=" * 70)
    print("CORRECTED CAPACITY FEASIBILITY TEST FOR E11 CORE")
    print("=" * 70)
    
    # analysis: Classify all 255 functionals
    print("\n1. Classifying functionals by Wang orbit type...")
    lb_table = {}  # 8-bit functional -> Wang LB
    type_counts = defaultdict(int)
    type_details = defaultdict(list)
    
    for f_8bit in range(1, 256):
        f_9bit = f_8bit << 1  # Extend to 9-bit with M11=0
        lb, ftype = classify_functional(f_9bit)
        lb_table[f_8bit] = lb
        type_counts[ftype] += 1
        type_details[ftype].append(f_8bit)
    
    print("  Type counts:")
    for ftype, count in sorted(type_counts.items()):
        lbs = set(lb_table[f] for f in type_details[ftype])
        print(f"    {ftype}: {count} functionals, LBs={lbs}")
    
    lb_counts = defaultdict(int)
    for f, lb in lb_table.items():
        lb_counts[lb] += 1
    print(f"\n  Summary: {dict(sorted(lb_counts.items()))}")
    
    # analysis: Pairwise infeasibility argument
    print("\n2. Pairwise analysis for r=19 (capacity LB18=1)...")
    # For any 2 distinct points p,q: #{f: f.p=1, f.q=1} = 2^6 = 64
    # #{LB-18 among these 64}
    p, q = 1, 2  # Example pair
    shared = [f for f in range(1,256) if bin(f&p).count('1')%2==1 and bin(f&q).count('1')%2==1]
    shared_lb18 = sum(1 for f in shared if lb_table[f] == 18)
    print(f"  Example pair (1,2): {len(shared)} shared violating functionals, {shared_lb18} at LB=18")
    
    # Check all projective pairs
    min_shared_lb18 = 255
    max_shared_lb18 = 0
    for p in range(1, 256):
        for q in range(p+1, 256):
            shared_lb18 = sum(1 for f in range(1,256) 
                            if bin(f&p).count('1')%2==1 and bin(f&q).count('1')%2==1 and lb_table[f]==18)
            min_shared_lb18 = min(min_shared_lb18, shared_lb18)
            max_shared_lb18 = max(max_shared_lb18, shared_lb18)
    print(f"  Over ALL pairs: min shared LB-18 = {min_shared_lb18}, max = {max_shared_lb18}")
    
    if min_shared_lb18 > 0:
        print(f"  => ANY 2 distinct points share ≥{min_shared_lb18} LB-18 functionals!")
        print(f"  => For r=19 (capacity 1): 2 violators on same functional => INFEASIBLE")
        print(f"  => PROVEN: R_F2(core_E11) ≥ 20, hence R_F2(T) ≥ 21")
    
    # analysis: Solve ILP for r = 19, 20, 21, 22, 23
    results = {
        "lb_distribution": dict(sorted(lb_counts.items())),
        "type_counts": {k: v for k, v in sorted(type_counts.items())},
        "ilp_results": {},
    }
    
    for r in [19, 20, 21, 22, 23]:
        print(f"\n{'=' * 70}")
        print(f"SOLVING ILP FOR rank = {r}")
        print(f"{'=' * 70}")
        
        status, solution = solve_capacity(r, lb_table, verbose=True)
        print(f"\n  STATUS: {status}")
        
        results["ilp_results"][r] = {"status": status}
        
        if solution:
            violations = verify_solution(solution, lb_table, r)
            print(f"  Solution: {len(solution)} distinct points, total multiplicity {sum(solution.values())}")
            print(f"  Verification: {violations} constraint violations")
            results["ilp_results"][r]["solution_points"] = len(solution)
            results["ilp_results"][r]["violations"] = violations
            
            for p, cnt in sorted(solution.items()):
                bits = bin(p)[2:].zfill(8)
                rk = mat_rank_f2(mask_to_mat(p << 1))
                print(f"    point {p} (0b{bits}, rank={rk}): count={cnt}")
    
    # analysis: Find minimum feasible r
    print(f"\n{'=' * 70}")
    print("SUMMARY")
    print(f"{'=' * 70}")
    for r in sorted(results["ilp_results"].keys()):
        print(f"  rank {r}: {results['ilp_results'][r]['status']}")
    
    # Save results
    outpath = outdir / "capacity_feasibility_corrected.json"
    with open(outpath, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {outpath}")

if __name__ == '__main__':
    main()
