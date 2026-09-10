#!/usr/bin/env python3
"""analysis: Staged CP-SAT for rep2 with residual cutoff.

Start with low-residual constraints, solve, check against full LUT,
add violated constraints, and repeat. This is a more principled version
of the iterative separation that starts with 500K+ constraints instead
of just edges.
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

from wang_capacity_lazy import unpack_basis

N = 9
MASK_ALL = (1 << N) - 1

def span_of(basis):
    s = {0}
    for b in basis:
        s |= {x ^ b for x in s}
    return frozenset(s)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    parser.add_argument('--out', default='data/rep2_staged/result.json')
    parser.add_argument('--time-limit', type=int, default=300)
    parser.add_argument('--initial-max-residual', type=int, default=2)
    parser.add_argument('--max-rounds', type=int, default=10)
    parser.add_argument('--violations-per-round', type=int, default=50000)
    args = parser.parse_args()

    out_dir = Path(args.out).parent
    out_dir.mkdir(parents=True, exist_ok=True)

    prefix = [1, 2]
    prefix_set = set(prefix)
    candidates = [p for p in range(1, 512) if p not in prefix_set]
    cand_set = set(candidates)
    cand_idx = {p: i for i, p in enumerate(candidates)}
    target = 18

    print(f"Loading LUT {args.lut}...")
    with open(args.lut, 'rb') as f:
        data = pickle.load(f)
    lut = {int(k): int(v) for k, v in data['lut'].items()}
    print(f"  {len(lut)} rows")

    # Precompute: for each LUT row, store (cand_indices_frozenset, capacity)
    # Only store rows that are non-trivially constraining
    print("\nPrecomputing row constraints...")
    t0 = time.time()
    all_rows = []  # (key, cand_indices_tuple, capacity, residual)
    for key, lb in lut.items():
        basis = unpack_basis(key)
        sp = span_of(basis)
        c = sum(1 for p in prefix if p in sp)
        cap = 20 - lb
        residual = cap - c
        if residual < 0:
            continue
        ci = tuple(sorted(cand_idx[p] for p in sp if p in cand_set))
        if residual >= len(ci):
            continue
        all_rows.append((int(key), ci, int(residual)))
    print(f"  {len(all_rows)} constraining rows ({time.time()-t0:.1f}s)")

    # Sort by residual (most constraining first)
    all_rows.sort(key=lambda r: (r[2], len(r[1])))

    # Phase: staged solving
    from ortools.sat.python import cp_model

    round_log = []
    included_keys = set()
    total_constraints = 0

    for rnd in range(args.max_rounds):
        print(f"\n=== Round {rnd} ===")

        if rnd == 0:
            # Include all rows with residual <= initial_max_residual
            batch = [(k, ci, r) for k, ci, r in all_rows
                     if r <= args.initial_max_residual and k not in included_keys]
        else:
            # Include violated rows from last model, sorted by residual
            batch = violation_batch

        if not batch:
            print("  No new constraints to add.")
            break

        for k, ci, r in batch:
            included_keys.add(k)
        total_constraints += len(batch)

        # Rebuild model
        model = cp_model.CpModel()
        x = [model.NewBoolVar(f'x{i}') for i in range(len(candidates))]
        model.Add(sum(x) == target)

        # Add all included constraints
        constraint_list = [(ci, r) for k, ci, r in all_rows if k in included_keys]
        for ci, r in constraint_list:
            model.Add(sum(x[i] for i in ci) <= r)

        print(f"  Constraints in model: {len(constraint_list)} (added {len(batch)} this round)")

        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = args.time_limit
        solver.parameters.num_workers = 8

        t1 = time.time()
        status = solver.Solve(model)
        elapsed = time.time() - t1

        status_name = {
            cp_model.OPTIMAL: 'OPTIMAL',
            cp_model.FEASIBLE: 'FEASIBLE',
            cp_model.INFEASIBLE: 'INFEASIBLE',
            cp_model.MODEL_INVALID: 'MODEL_INVALID',
            cp_model.UNKNOWN: 'UNKNOWN',
        }.get(status, f'UNKNOWN_{status}')

        ri = {'round': rnd, 'status': status_name, 'elapsed_sec': round(elapsed, 1),
              'constraints_in_model': len(constraint_list), 'batch_size': len(batch)}

        if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            selected_idx = [i for i in range(len(candidates)) if solver.Value(x[i])]
            selected_pts = [candidates[i] for i in selected_idx]
            ri['selected_points'] = selected_pts
            ri['selected_count'] = len(selected_pts)

            # Scan ALL rows for violations
            selected_set = set(selected_idx)
            violations = []
            for k, ci, r in all_rows:
                if k in included_keys:
                    continue
                occ = sum(1 for i in ci if i in selected_set)
                if occ > r:
                    violations.append((k, ci, r, occ - r))

            ri['new_violations'] = len(violations)
            print(f"  {status_name} in {elapsed:.1f}s, selected {len(selected_pts)} pts, "
                  f"new violations: {len(violations)}")

            if not violations:
                # Model satisfies ALL constraints — rep2 is feasible!
                ri['full_lut_clean'] = True
                round_log.append(ri)
                break
            else:
                # Add most constraining violations
                violations.sort(key=lambda v: (v[2], -v[3]))  # low residual, high excess first
                violation_batch = [(k, ci, r) for k, ci, r, _ in violations[:args.violations_per_round]]
                round_log.append(ri)

        elif status == cp_model.INFEASIBLE:
            ri['infeasible'] = True
            round_log.append(ri)
            print(f"  INFEASIBLE in {elapsed:.1f}s!")
            break
        else:
            round_log.append(ri)
            print(f"  {status_name} in {elapsed:.1f}s")
            break

    result = {
        'schema': 'rep2_staged_cpsat_v1',
        'prefix': prefix,
        'target': target,
        'candidate_count': len(candidates),
        'total_constraining_rows': len(all_rows),
        'initial_max_residual': args.initial_max_residual,
        'round_log': round_log,
        'total_rounds': len(round_log),
        'final_status': round_log[-1]['status'] if round_log else 'NO_ROUNDS',
    }

    Path(args.out).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved to {args.out}")

if __name__ == '__main__':
    main()
