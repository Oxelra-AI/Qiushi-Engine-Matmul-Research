#!/usr/bin/env python3
r"""analysis: E11-core rank-19 multiset pilot with complete Wang checks.

Unlike the distinct-point v3 script, this model allows repeated projected
A-directions according to the one-dimensional Wang capacities.  It is a
construction-search instrument, not an exhaustive proof: active rows are added
lazily, and fixed-A failures produce candidate-specific no-goods.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402
from fixed_A_saturation import mat_rank_f2  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints, complete_core_wang_scan, saturation_domains, transversal_failures  # noqa: E402
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}


def add_core_row(model, x, key8: int, core: CoreQuotient, lut: dict[int, int], s: int, added: set[int]) -> bool:
    key8 = int(key8)
    if key8 in added:
        return False
    key9 = core.key9_from_key8(key8)
    cap = int(s) - int(lut[key9])
    pts = subspace_points_from_basis(unpack_basis(key8))
    if cap < 0:
        model.Add(0 == 1)
    else:
        model.Add(sum(x[p] for p in pts) <= cap)
    added.add(key8)
    return True


def add_exact_multiset_nogood(model, x, counts: dict[int, int], points: list[int], upper: dict[int, int], tag: str):
    """Exclude exactly this 255-coordinate count vector using equality literals."""
    lits = []
    for p in points:
        val = int(counts.get(p, 0))
        y = model.NewBoolVar(f'eq_{tag}_{p}_{val}')
        model.Add(x[p] == val).OnlyEnforceIf(y)
        # Since domains are integer intervals, x[p] != val is supported by CP-SAT.
        model.Add(x[p] != val).OnlyEnforceIf(y.Not())
        lits.append(y.Not())
    model.AddBoolOr(lits)


def main():
    from ortools.sat.python import cp_model

    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--rank', type=int, default=19)
    ap.add_argument('--max-rounds', type=int, default=8)
    ap.add_argument('--solver-time', type=float, default=180.0)
    ap.add_argument('--add-wang-limit', type=int, default=1000)
    ap.add_argument('--out', type=Path, default=ROOT / 'workspace/data/core_complete_transversal/core_e11_multiset_pilot.json')
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    s = int(args.rank)
    core = CoreQuotient(1)
    T_core = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    lut = load_lut(args.lut)
    records, meta = build_core_constraints(core, lut)
    points = list(range(1, 256))

    # One-dimensional capacities determine per-point domains: six points have cap 2, the rest cap 1 at s=19.
    point_cap = {}
    for p in points:
        key8 = core.key8_from_rows([p])
        key9 = core.key9_from_key8(key8)
        point_cap[p] = max(0, min(s, s - int(lut[key9])))
    cap_dist = Counter(point_cap.values())

    model = cp_model.CpModel()
    x = {p: model.NewIntVar(0, point_cap[p], f'x_{p}') for p in points}
    model.Add(sum(x[p] for p in points) == s)
    # Force at least one repeated direction so this pilot explores outside the distinct-A ansatz.
    repeat_cap_points = [p for p in points if point_cap[p] >= 2]
    y_repeat = []
    for p in repeat_cap_points:
        y = model.NewBoolVar(f'repeat_{p}')
        model.Add(x[p] >= 2).OnlyEnforceIf(y)
        model.Add(x[p] <= 1).OnlyEnforceIf(y.Not())
        y_repeat.append(y)
    if y_repeat:
        model.AddBoolOr(y_repeat)

    added = set()
    added_source = Counter()
    for rec in records:
        if int(rec['dim8']) in (1, 2):
            if add_core_row(model, x, rec['key8'], core, lut, s, added):
                added_source[f"initial_dim{rec['dim8']}"] += 1

    # Contraction lower bounds with multiplicities.
    contraction_lower_count = 0
    contraction_rank_dist = Counter()
    for q in range(1, 1 << T_core.shape[0]):
        M = np.zeros((T_core.shape[1], T_core.shape[2]), dtype=np.uint8)
        for a in range(T_core.shape[0]):
            if (q >> a) & 1:
                M ^= T_core[a]
        rk = mat_rank_f2(M)
        contraction_rank_dist[rk] += 1
        if rk > 0:
            model.Add(sum(x[p] for p in points if ((q & p).bit_count() & 1)) >= rk)
            contraction_lower_count += 1

    print(f'point_cap_dist={dict(cap_dist)} repeat_cap_points={repeat_cap_points}')
    print(f'initial rows={len(added)} contraction_lower={contraction_lower_count}')

    rounds = []
    exact_nogoods = 0
    final_status = None
    for rnd in range(args.max_rounds):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(args.solver_time)
        solver.parameters.num_search_workers = 8
        solver.parameters.random_seed = 4480 + 23 * rnd
        tsolve = time.time()
        status = solver.Solve(model)
        solve_sec = time.time() - tsolve
        status_name = {cp_model.OPTIMAL:'OPTIMAL', cp_model.FEASIBLE:'FEASIBLE', cp_model.INFEASIBLE:'INFEASIBLE', cp_model.UNKNOWN:'UNKNOWN', cp_model.MODEL_INVALID:'MODEL_INVALID'}.get(status, str(status))
        print(f'\nRound {rnd}: status={status_name} solve_sec={solve_sec:.1f} rows={len(added)} nogoods={exact_nogoods}')
        rec = {'round': rnd, 'status': status_name, 'solve_sec': round(solve_sec, 3), 'active_wang_rows': len(added), 'exact_nogoods': exact_nogoods}
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rounds.append(rec); final_status = status_name; break
        counts = {p: solver.Value(x[p]) for p in points if solver.Value(x[p])}
        A_cols = []
        for p, c in sorted(counts.items()):
            A_cols.extend([p] * c)
        rec['counts'] = {str(k): int(v) for k, v in sorted(counts.items())}
        rec['support'] = A_cols
        rec['distinct_A_points'] = len(counts)
        rec['max_multiplicity'] = max(counts.values())
        rec['multiplicity_hist'] = {str(k): v for k, v in sorted(Counter(counts.values()).items())}

        scan = complete_core_wang_scan(f'multiset_round{rnd}', A_cols, s, records, max_head=max(60, args.add_wang_limit))
        sat = saturation_domains(T_core, A_cols)
        lin = sat['summary']['linear_membership']
        trans = transversal_failures(sat['sat_records'], sat['B_domains'], sat['C_domains'], 9, 9, max_report=60)
        rec['complete_wang_scan'] = {k: v for k, v in scan.items() if k != 'violations_head'}
        rec['complete_wang_violations_head'] = scan['violations_head'][:20]
        rec['saturation'] = {
            'saturated_contraction_count': sat['summary']['saturated_contraction_count'],
            'undersaturated_contraction_count': sat['summary']['undersaturated_contraction_count'],
            'zero_domain_term_count': len(sat['summary']['zero_domain_terms']),
            'linear_passed': lin['necessary_linear_test_passed'],
            'linear_affine_dim': lin['affine_solution_dimension_if_consistent'],
            'domain_hist': sat['summary']['term_domain_dims_hist'],
            'transversal_failure_count_reported': trans['failure_count_reported'],
            'transversal_witnesses_head': trans['failures_head'][:12],
        }
        print('  distinct=%s maxmult=%s complete_viol=%s max_excess=%s zero=%s linear=%s trans=%s' % (rec['distinct_A_points'], rec['max_multiplicity'], scan['complete_violation_count'], scan['max_excess'], rec['saturation']['zero_domain_term_count'], rec['saturation']['linear_passed'], rec['saturation']['transversal_failure_count_reported']))

        if scan['complete_violation_count'] == 0 and rec['saturation']['zero_domain_term_count'] == 0 and rec['saturation']['linear_passed'] and rec['saturation']['transversal_failure_count_reported'] == 0:
            rec['candidate_status'] = 'MULTISET_A_SUPPORT_PASSES_CURRENT_COMPLETE_TESTS_NEEDS_RANKONE_SOLVE'
            rounds.append(rec); final_status = 'CANDIDATE_FOUND'; break

        added_now = 0
        for v in sorted(scan['violations_head'], key=lambda z: (-int(z['excess']), -int(z['L'])))[:args.add_wang_limit]:
            if add_core_row(model, x, int(v['key8']), core, lut, s, added):
                added_now += 1
                added_source['complete_scan_violation'] += 1
        rec['learned_wang_rows_added'] = added_now
        if rec['saturation']['zero_domain_term_count'] > 0 or (not rec['saturation']['linear_passed']) or rec['saturation']['transversal_failure_count_reported'] > 0:
            add_exact_multiset_nogood(model, x, counts, points, point_cap, f'r{rnd}')
            exact_nogoods += 1
            rec['exact_multiset_nogood_added'] = True
        rounds.append(rec); final_status = status_name

    result = {
        'schema': 'core_e11_multiset_pilot_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': s,
        'scope': 'Construction-search pilot allowing repeated A directions up to one-dimensional Wang capacities; not proof-producing and not exhaustive after UNKNOWN/time limit.',
        'point_cap_distribution': {str(k): v for k, v in sorted(cap_dist.items())},
        'repeat_cap_points': repeat_cap_points,
        'complete_core_table_meta': meta,
        'contraction_lower_count': contraction_lower_count,
        'contraction_rank_dist': {str(k): v for k, v in sorted(contraction_rank_dist.items())},
        'final_status': final_status,
        'total_rounds': len(rounds),
        'final_wang_rows': len(added),
        'added_source_counts': dict(added_source),
        'exact_multiset_nogoods': exact_nogoods,
        'rounds': rounds,
        'total_elapsed_sec': round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'\nSaved {args.out}')
    print(json.dumps({'final_status': final_status, 'rounds': len(rounds), 'rows': len(added), 'nogoods': exact_nogoods}, sort_keys=True))


if __name__ == '__main__':
    main()
