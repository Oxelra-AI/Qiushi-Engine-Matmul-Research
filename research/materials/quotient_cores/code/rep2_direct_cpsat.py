#!/usr/bin/env python3
"""analysis: Direct CP-SAT encoding for the rep2 adjacent-pair branch.

Instead of iteratively adding violated rows, encode ALL constraining
Wang rows upfront as a CP-SAT model:
  - 509 binary variables for candidate points
  - exact cardinality = 18
  - for each Wang row Φ with prefix occupancy c and lb L:
    sum_{p ∈ Φ ∩ candidates} x_p ≤ (20 - L) - c

This is a direct attack on the rep2 branch feasibility.
"""
from __future__ import annotations
import argparse
import json
import pickle
import sys
import time
from collections import defaultdict
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

from wang_capacity_lazy import unpack_basis, subspace_points_from_basis

def span_of(basis):
    """Full GF(2) span of the given basis vectors (including 0)."""
    s = {0}
    for b in basis:
        s |= {x ^ b for x in s}
    return frozenset(s)

N = 9
MASK_ALL = (1 << N) - 1

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    parser.add_argument('--out', default='data/rep2_direct/result.json')
    parser.add_argument('--time-limit', type=int, default=600, help='CP-SAT time limit in seconds')
    parser.add_argument('--max-residual', type=int, default=17, help='only encode rows with residual <= this')
    args = parser.parse_args()

    out_dir = Path(args.out).parent
    out_dir.mkdir(parents=True, exist_ok=True)

    # Fixed prefix
    prefix = [1, 2]
    prefix_set = set(prefix)

    # Candidate points: all projective points except the prefix
    candidates = [p for p in range(1, 512) if p not in prefix_set]
    cand_set = set(candidates)
    cand_idx = {p: i for i, p in enumerate(candidates)}
    assert len(candidates) == 509
    target = 18  # must select exactly 18 from candidates

    print(f"Loading LUT {args.lut}...")
    t0 = time.time()
    with open(args.lut, 'rb') as f:
        data = pickle.load(f)
    lut = {int(k): int(v) for k, v in data['lut'].items()}
    print(f"  {len(lut)} rows, {time.time()-t0:.1f}s")

    # Phase 1: scan all LUT rows and collect constraints
    print("\nScanning LUT rows...")
    t1 = time.time()
    constraints = []  # (frozen_indices, capacity)
    constraint_dedup = {}  # (tuple(sorted_indices), capacity) -> count
    skipped_trivial = 0
    skipped_highres = 0
    prefix_violations = 0
    res_hist = defaultdict(int)

    for key_idx, (key, lb) in enumerate(lut.items()):
        if key_idx % 2_000_000 == 0 and key_idx > 0:
            print(f"  processed {key_idx:,}/{len(lut):,}, constraints so far: {len(constraint_dedup):,}")

        basis = unpack_basis(key)
        sp = span_of(basis)

        # prefix occupancy
        c = sum(1 for p in prefix if p in sp)
        cap = 20 - lb
        residual = cap - c

        if residual < 0:
            prefix_violations += 1
            continue

        # Candidate points in this subspace
        cand_in = [cand_idx[p] for p in sp if p in cand_set]

        if residual >= len(cand_in):
            skipped_trivial += 1
            continue

        if residual > args.max_residual:
            skipped_highres += 1
            continue

        res_hist[residual] += 1

        # Constraint: sum of x_p for p in cand_in <= residual
        sig = (tuple(sorted(cand_in)), residual)
        constraint_dedup[sig] = constraint_dedup.get(sig, 0) + 1

    elapsed_scan = time.time() - t1
    print(f"\nScan complete in {elapsed_scan:.1f}s")
    print(f"  prefix_violations: {prefix_violations}")
    print(f"  skipped_trivial: {skipped_trivial}")
    print(f"  skipped_highres: {skipped_highres}")
    print(f"  unique constraints: {len(constraint_dedup)}")
    print(f"  residual histogram: {dict(sorted(res_hist.items()))}")

    # Phase 2: Build CP-SAT model
    print(f"\nBuilding CP-SAT model with {len(constraint_dedup)} constraints...")
    from ortools.sat.python import cp_model

    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x{i}') for i in range(len(candidates))]

    # Exact cardinality
    model.Add(sum(x) == target)

    constraint_count = 0
    for (indices, cap), _ in constraint_dedup.items():
        model.Add(sum(x[i] for i in indices) <= cap)
        constraint_count += 1

    print(f"  variables: {len(x)}")
    print(f"  constraints: {constraint_count}")

    # Solve
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.time_limit
    solver.parameters.num_workers = 8

    print(f"\nSolving (time_limit={args.time_limit}s)...")
    t2 = time.time()
    status = solver.Solve(model)
    elapsed_solve = time.time() - t2

    status_name = {
        cp_model.OPTIMAL: 'OPTIMAL',
        cp_model.FEASIBLE: 'FEASIBLE',
        cp_model.INFEASIBLE: 'INFEASIBLE',
        cp_model.MODEL_INVALID: 'MODEL_INVALID',
        cp_model.UNKNOWN: 'UNKNOWN',
    }.get(status, f'UNKNOWN_{status}')

    print(f"\nStatus: {status_name} ({elapsed_solve:.1f}s)")

    result = {
        'schema': 'rep2_direct_cpsat_v1',
        'prefix': prefix,
        'target': target,
        'candidate_count': len(candidates),
        'lut_rows': len(lut),
        'unique_constraints': len(constraint_dedup),
        'max_residual': args.max_residual,
        'prefix_violations': prefix_violations,
        'skipped_trivial': skipped_trivial,
        'skipped_highres': skipped_highres,
        'residual_histogram': {str(k): v for k, v in sorted(res_hist.items())},
        'status': status_name,
        'solve_elapsed_sec': round(elapsed_solve, 2),
        'scan_elapsed_sec': round(elapsed_scan, 2),
    }

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        selected = [candidates[i] for i in range(len(candidates)) if solver.Value(x[i])]
        result['selected_points'] = selected
        result['selected_count'] = len(selected)
        print(f"  Selected {len(selected)} points: {selected[:20]}...")

        # Check against full LUT
        full_support = set(prefix + selected)
        violations = 0
        worst_viol = None
        for key, lb in lut.items():
            basis = unpack_basis(key)
            sp = span_of(basis)
            occ = len(full_support & sp)
            cap = 20 - lb
            if occ > cap:
                violations += 1
                if worst_viol is None or (occ - cap) > worst_viol[1]:
                    worst_viol = (int(key), occ - cap, lb, occ)
        result['full_lut_violations'] = violations
        result['worst_violation'] = worst_viol
        print(f"  Full LUT violations: {violations}")
        if worst_viol:
            print(f"  Worst: key={hex(worst_viol[0])}, excess={worst_viol[1]}, lb={worst_viol[2]}, occ={worst_viol[3]}")
    elif status == cp_model.INFEASIBLE:
        print("  REP2 BRANCH IS INFEASIBLE!")
        result['infeasible'] = True

    Path(args.out).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved to {args.out}")

if __name__ == '__main__':
    main()
