#!/usr/bin/env python3
"""Decisive E11 core capacity solver: LP + CP-SAT with all Wang constraints.

Uses research_record's complete subspace enumeration to build the full constraint
system, then solves with OR-Tools CP-SAT (better at integer feasibility than
HiGHS milp) and optionally checks the LP relaxation first.

Infeasible at s=19 proves R_F2(E11) >= 20 and closes the constructive route.
Feasible produces an admissible A-factor multiset for SAT testing.
"""
import argparse, json, pickle, sys, time
from pathlib import Path
from collections import Counter

# Import functions from research_record's code
SCRIPTS = Path("scripts")
sys.path.insert(0, str(SCRIPTS))
from core_capacity_from_wang_lut import CoreQuotient, PIVOTS
from wang_capacity_lazy import (
    pack_basis, unpack_basis, rref_basis, rref_key,
    subspace_points_from_basis,
)
from wang_capacity_orbit_closed import extension_keys


def load_lut(path):
    with open(path, 'rb') as f:
        d = pickle.load(f)
    return d['lut'], d.get('meta', {})


def enumerate_subspace_keys(n=8):
    """Enumerate all subspace keys of F2^n dimension by dimension."""
    levels = {0: {pack_basis(tuple())}}
    all_keys = set(levels[0])
    for d in range(n):
        nxt = set()
        for key in levels[d]:
            for ekey in extension_keys(unpack_basis(key), n=n):
                if (ekey & 0xF) == d + 1:
                    nxt.add(ekey)
        levels[d + 1] = nxt
        all_keys.update(nxt)
        print(f"  enum dim {d+1}: {len(nxt):,}")
    return sorted(all_keys)


def build_constraints(core, lut, s, keys8):
    """Build constraint data: for each core subspace, compute capacity."""
    constraints = []  # (point_set, cap, key8, L, dim)
    for key8 in keys8:
        key9 = core.key9_from_key8(key8)
        L = lut[key9]
        cap = s - L
        pts = subspace_points_from_basis(unpack_basis(key8))
        dim = key8 & 0xF
        constraints.append((pts, cap, key8, L, dim))
    return constraints


def solve_lp_relaxation(constraints, s, n_vars=255):
    """Solve LP relaxation using scipy to check if LP is infeasible."""
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import lil_matrix

    # Variables x_1, ..., x_255 (0-indexed as 0..254)
    # Minimize 0 (feasibility check)
    # Equality: sum = s
    # Inequalities: for each constraint, sum_{p in pts} x_{p-1} <= cap

    # Filter to nontrivial constraints
    nontrivial = [(pts, cap) for pts, cap, _, _, _ in constraints if pts and cap < s]
    print(f"LP: {n_vars} vars, {len(nontrivial)} nontrivial ineq + 1 eq")

    A_ub = lil_matrix((len(nontrivial), n_vars))
    b_ub = np.empty(len(nontrivial))
    for i, (pts, cap) in enumerate(nontrivial):
        for p in pts:
            A_ub[i, p - 1] = 1.0
        b_ub[i] = cap

    A_eq = np.ones((1, n_vars))
    b_eq = np.array([s], dtype=float)

    c = np.zeros(n_vars)
    bounds = [(0, s)] * n_vars

    t0 = time.time()
    res = linprog(c, A_ub=A_ub.tocsr(), b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=bounds, method='highs')
    elapsed = time.time() - t0
    return {
        'status': int(res.status),
        'message': res.message,
        'success': bool(res.success),
        'elapsed_sec': elapsed,
        'feasible': res.success,
    }


def solve_cpsat(constraints, s, n_vars=255, time_limit=1200):
    """Solve using OR-Tools CP-SAT."""
    from ortools.sat.python import cp_model

    model = cp_model.CpModel()
    x = [model.new_int_var(0, s, f'x_{i+1}') for i in range(n_vars)]

    # sum = s
    model.add(sum(x) == s)

    # Subspace constraints
    added = 0
    for pts, cap, key8, L, dim in constraints:
        if pts and cap < s:  # skip vacuous
            model.add(sum(x[p-1] for p in pts) <= cap)
            added += 1

    print(f"CP-SAT: {n_vars} vars, {added} constraints, time_limit={time_limit}s")

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = 8
    solver.parameters.log_search_progress = True

    t0 = time.time()
    status = solver.solve(model)
    elapsed = time.time() - t0

    status_name = {
        cp_model.OPTIMAL: 'OPTIMAL',
        cp_model.FEASIBLE: 'FEASIBLE',
        cp_model.INFEASIBLE: 'INFEASIBLE',
        cp_model.MODEL_INVALID: 'MODEL_INVALID',
        cp_model.UNKNOWN: 'UNKNOWN',
    }.get(status, f'status_{status}')

    solution = None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = {}
        for i in range(n_vars):
            v = solver.value(x[i])
            if v > 0:
                sol[i + 1] = v
        solution = sol

    return {
        'status': status_name,
        'elapsed_sec': elapsed,
        'solution': solution,
        'solution_support': len(solution) if solution else None,
        'solution_total': sum(solution.values()) if solution else None,
        'wall_time': solver.wall_time,
    }


def verify_solution(sol, core, lut, s, keys8):
    """Check all constraints against a solution."""
    violations = []
    for key8 in keys8:
        key9 = core.key9_from_key8(key8)
        L = lut[key9]
        cap = s - L
        pts = subspace_points_from_basis(unpack_basis(key8))
        occ = sum(sol.get(p, 0) for p in pts)
        if occ > cap:
            violations.append({
                'key8': key8, 'dim': key8 & 0xF,
                'L': L, 'cap': cap, 'occ': occ, 'excess': occ - cap
            })
    return violations


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path,
                    default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=19)
    ap.add_argument('--time-limit', type=float, default=1200)
    ap.add_argument('--lp-only', action='store_true')
    ap.add_argument('--json-out', type=Path,
                    default=Path('data/e11_complete_capacity/result.json'))
    args = ap.parse_args()

    print("Loading LUT...")
    lut, meta = load_lut(args.lut)
    print(f"LUT: {len(lut):,} subspaces, coverage_ok={meta.get('coverage_ok')}")

    pivot = PIVOTS['E11']
    core = CoreQuotient(pivot)
    s = args.rank

    print(f"\nEnumerating all F2^8 subspaces...")
    keys8 = enumerate_subspace_keys(8)
    print(f"Total subspace keys: {len(keys8):,}")

    print(f"\nBuilding core constraints (s={s})...")
    constraints = build_constraints(core, lut, s, keys8)

    # Statistics
    L_counts = Counter(L for _, _, _, L, _ in constraints)
    neg_cap = sum(1 for _, cap, _, _, _ in constraints if cap < 0)
    print(f"L distribution: {dict(sorted(L_counts.items()))}")
    print(f"Negative capacity constraints: {neg_cap}")
    if neg_cap > 0:
        for pts, cap, key8, L, dim in constraints:
            if cap < 0 and pts:
                print(f"  IMMEDIATE INFEASIBILITY: dim={dim}, L={L}, cap={cap}, |pts|={len(pts)}")
                break

    # LP relaxation
    print(f"\n=== LP RELAXATION ===")
    lp_result = solve_lp_relaxation(constraints, s)
    print(f"LP: {lp_result}")

    cpsat_result = None
    verification = None
    if not args.lp_only:
        print(f"\n=== CP-SAT INTEGER SOLVE ===")
        cpsat_result = solve_cpsat(constraints, s, time_limit=args.time_limit)
        print(f"CP-SAT: status={cpsat_result['status']}, elapsed={cpsat_result['elapsed_sec']:.1f}s")

        if cpsat_result['solution']:
            print(f"  support={cpsat_result['solution_support']}, total={cpsat_result['solution_total']}")
            print(f"  Verifying against all {len(keys8)} constraints...")
            violations = verify_solution(cpsat_result['solution'], core, lut, s, keys8)
            verification = {
                'violation_count': len(violations),
                'violations_head': violations[:20]
            }
            if violations:
                print(f"  VIOLATIONS: {len(violations)}")
            else:
                print(f"  VERIFIED: solution passes all {len(keys8)} constraints")

    result = {
        'problem': 'E11 complete core Wang occupation capacity',
        'field': 'F2',
        'core_name': 'E11',
        'pivot': pivot,
        'rank_s': s,
        'total_subspace_constraints': len(keys8),
        'L_distribution': dict(sorted(L_counts.items())),
        'negative_capacity_count': neg_cap,
        'lp_result': lp_result,
        'cpsat_result': cpsat_result,
        'verification': verification,
        'meaning': 'INFEASIBLE proves R_F2(E11) >= 20, closing E11 constructive route. FEASIBLE gives admissible A-multiset for SAT testing.',
    }

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(result, indent=2, sort_keys=True, default=str) + '\n')
    print(f"\nSaved {args.json_out}")


if __name__ == '__main__':
    main()
