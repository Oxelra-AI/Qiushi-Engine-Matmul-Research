#!/usr/bin/env python3
"""analysis: Rank-aware staged CP-SAT for rep2.

Critical insight: all previous CP-SAT feasible models were pure rank-1
supports, but we already proved that any length-20 A-support must have
at least 3 higher-rank A-factors (k=18 closure + pure rank-1 exclusion).

This script adds the structural constraint:
  rank-1 candidates ≤ 15 (because prefix {1,2} are rank-1, and max rank-1 total = 17)

This eliminates the entire class of infeasible pure-rank-1 solutions
that CP-SAT was finding.
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

def span_of(basis):
    s = {0}
    for b in basis:
        s |= {x ^ b for x in s}
    return frozenset(s)

def rank1_points():
    pts = set()
    for u in range(1, 8):
        for v in range(1, 8):
            m = 0
            for i in range(3):
                if (u >> i) & 1:
                    m |= v << (3 * i)
            pts.add(m)
    return pts

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    parser.add_argument('--out', default='data/rep2_rankaware/result.json')
    parser.add_argument('--time-limit', type=int, default=300)
    parser.add_argument('--initial-max-residual', type=int, default=2)
    parser.add_argument('--max-rounds', type=int, default=10)
    parser.add_argument('--violations-per-round', type=int, default=100000)
    parser.add_argument('--max-rank1-candidates', type=int, default=15,
                        help='max rank-1 candidates (prefix {1,2} already rank-1, k<=17 total)')
    args = parser.parse_args()

    out_dir = Path(args.out).parent
    out_dir.mkdir(parents=True, exist_ok=True)

    prefix = [1, 2]
    prefix_set = set(prefix)
    candidates = [p for p in range(1, 512) if p not in prefix_set]
    cand_set = set(candidates)
    cand_idx = {p: i for i, p in enumerate(candidates)}
    target = 18

    r1_all = rank1_points()
    r1_candidates = [p for p in candidates if p in r1_all]
    hr_candidates = [p for p in candidates if p not in r1_all]
    r1_cand_indices = [cand_idx[p] for p in r1_candidates]
    hr_cand_indices = [cand_idx[p] for p in hr_candidates]

    print(f"Candidates: {len(candidates)} total, {len(r1_candidates)} rank-1, {len(hr_candidates)} higher-rank")
    print(f"Max rank-1 candidates: {args.max_rank1_candidates}")

    print(f"\nLoading LUT...")
    with open(args.lut, 'rb') as f:
        data = pickle.load(f)
    lut = {int(k): int(v) for k, v in data['lut'].items()}
    print(f"  {len(lut)} rows")

    # Precompute constraints
    print("\nPrecomputing constraints...")
    t0 = time.time()
    all_rows = []
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
    all_rows.sort(key=lambda r: (r[2], len(r[1])))
    print(f"  {len(all_rows)} constraining rows ({time.time()-t0:.1f}s)")

    from ortools.sat.python import cp_model

    round_log = []
    included_keys = set()

    for rnd in range(args.max_rounds):
        print(f"\n=== Round {rnd} ===")

        if rnd == 0:
            batch = [(k, ci, r) for k, ci, r in all_rows
                     if r <= args.initial_max_residual and k not in included_keys]
        else:
            batch = violation_batch

        if not batch:
            print("  No new constraints to add.")
            break

        for k, ci, r in batch:
            included_keys.add(k)

        # Rebuild model
        model = cp_model.CpModel()
        x = [model.NewBoolVar(f'x{i}') for i in range(len(candidates))]

        # Exact cardinality
        model.Add(sum(x) == target)

        # RANK-1 CONSTRAINT: at most max_rank1_candidates rank-1 candidates
        model.Add(sum(x[i] for i in r1_cand_indices) <= args.max_rank1_candidates)

        # Wang constraints
        constraint_list = [(ci, r) for k, ci, r in all_rows if k in included_keys]
        for ci, r in constraint_list:
            model.Add(sum(x[i] for i in ci) <= r)

        print(f"  Constraints: {len(constraint_list)} Wang + 2 structural (added {len(batch)} Wang this round)")

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
              'constraints_wang': len(constraint_list), 'batch_size': len(batch)}

        if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            selected_idx = [i for i in range(len(candidates)) if solver.Value(x[i])]
            selected_pts = [candidates[i] for i in selected_idx]
            r1_count = sum(1 for i in selected_idx if i in set(r1_cand_indices))
            hr_count = len(selected_pts) - r1_count
            ri['selected_points'] = selected_pts
            ri['selected_count'] = len(selected_pts)
            ri['rank1_count'] = r1_count
            ri['higher_rank_count'] = hr_count

            # Scan for violations
            selected_set = set(selected_idx)
            violations = []
            for k, ci, r in all_rows:
                if k in included_keys:
                    continue
                occ = sum(1 for i in ci if i in selected_set)
                if occ > r:
                    violations.append((k, ci, r, occ - r))

            ri['new_violations'] = len(violations)
            print(f"  {status_name} {elapsed:.1f}s: {len(selected_pts)} pts "
                  f"(r1={r1_count}, hr={hr_count}), violations={len(violations)}")

            if not violations:
                ri['full_wang_clean'] = True
                round_log.append(ri)
                print("  *** FULL WANG ADMISSIBLE! ***")
                break
            else:
                violations.sort(key=lambda v: (v[2], -v[3]))
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
        'schema': 'rep2_rankaware_cpsat_v1',
        'prefix': prefix,
        'target': target,
        'candidate_count': len(candidates),
        'rank1_candidates': len(r1_candidates),
        'higher_rank_candidates': len(hr_candidates),
        'max_rank1_candidates': args.max_rank1_candidates,
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
