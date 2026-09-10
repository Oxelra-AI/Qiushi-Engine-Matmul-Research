#!/usr/bin/env python3
r"""analysis: E11-core distinct-support search with complete Wang scan.

This replaces the analysis partial support scan (spans of at most five selected
points) by the full 417,199-row core Wang table.  It also applies saturated
fixed-A linear membership and Rado independent-transversal tests before calling
a support a candidate.

Important scope: variables are Boolean projective A-points.  Therefore an
UNSAT/INFEASIBLE result here concerns the distinct-A ansatz only; it does not
exclude rank-19 core decompositions with repeated projected A-directions.
"""
from __future__ import annotations

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
from complete_core_and_transversal import (  # noqa: E402
    ROOT,
    build_core_constraints,
    complete_core_wang_scan,
    saturation_domains,
    transversal_failures,
)
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}


def add_core_row(model, x, key8: int, core: CoreQuotient, lut: dict[int, int], s: int, added: set[int], source: str) -> bool:
    key8 = int(key8)
    if key8 in added:
        return False
    key9 = core.key9_from_key8(key8)
    if key9 not in lut:
        return False
    cap = int(s) - int(lut[key9])
    if cap < 0:
        model.Add(0 == 1)
    else:
        pts = subspace_points_from_basis(unpack_basis(key8))
        model.Add(sum(x[p] for p in pts) <= cap)
    added.add(key8)
    return True


def main():
    import argparse
    from ortools.sat.python import cp_model

    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--rank', type=int, default=19)
    ap.add_argument('--max-rounds', type=int, default=8)
    ap.add_argument('--solver-time', type=float, default=120.0)
    ap.add_argument('--add-wang-limit', type=int, default=2000)
    ap.add_argument('--out', type=Path, default=ROOT / 'workspace/data/core_complete_transversal/core_e11_saturation_v3_complete.json')
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t_all = time.time()
    s = int(args.rank)
    pivot = 1
    core = CoreQuotient(pivot)
    T_core = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2

    print('Loading LUT and complete core row table...')
    lut = load_lut(args.lut)
    core_records, core_meta = build_core_constraints(core, lut)

    model = cp_model.CpModel()
    points = list(range(1, 256))
    x = {p: model.NewBoolVar(f'x_{p}') for p in points}
    model.Add(sum(x[p] for p in points) == s)

    added: set[int] = set()
    added_source = Counter()

    # Initial rows: all 1D and 2D rows, as in the older core search, now explicitly marked.
    for rec in core_records:
        d = int(rec['dim8'])
        if d in (1, 2):
            if add_core_row(model, x, rec['key8'], core, lut, s, added, f'initial_dim{d}'):
                added_source[f'initial_dim{d}'] += 1

    # Contraction-rank lower bounds for the canonical core tensor.  These are
    # independent of Wang occupation and must be present for a realistic fixed-A
    # construction search.
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
            ci = [p for p in points if ((q & p).bit_count() & 1)]
            model.Add(sum(x[p] for p in ci) >= rk)
            contraction_lower_count += 1

    print(f'Initial complete-table rows added={len(added)} by source={dict(added_source)} contraction_lower={contraction_lower_count} rank_dist={dict(sorted(contraction_rank_dist.items()))}')

    rounds = []
    final_status = None
    exact_support_exclusions = 0
    for rnd in range(args.max_rounds):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(args.solver_time)
        solver.parameters.num_search_workers = 8
        solver.parameters.random_seed = 4400 + 17 * rnd
        tsolve = time.time()
        status = solver.Solve(model)
        solve_sec = time.time() - tsolve
        status_name = {
            cp_model.OPTIMAL: 'OPTIMAL',
            cp_model.FEASIBLE: 'FEASIBLE',
            cp_model.INFEASIBLE: 'INFEASIBLE',
            cp_model.UNKNOWN: 'UNKNOWN',
            cp_model.MODEL_INVALID: 'MODEL_INVALID',
        }.get(status, str(status))
        print(f'\nRound {rnd}: status={status_name} solve_sec={solve_sec:.1f} active_wang={len(added)}')
        rec = {'round': rnd, 'status': status_name, 'solve_sec': round(solve_sec, 3), 'active_wang_rows': len(added)}
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rounds.append(rec)
            final_status = status_name
            break

        support = sorted(p for p in points if solver.Value(x[p]))
        rec['support'] = support

        scan = complete_core_wang_scan(f'v3_round{rnd}', support, s, core_records, max_head=max(40, int(args.add_wang_limit)))
        rec['complete_wang_scan'] = {
            k: v for k, v in scan.items() if k not in ('violations_head',)
        }
        rec['complete_wang_violations_head'] = scan['violations_head'][:20]

        sat = saturation_domains(T_core, support)
        lin = sat['summary']['linear_membership']
        trans = transversal_failures(sat['sat_records'], sat['B_domains'], sat['C_domains'], 9, 9, max_report=20)
        rec['saturation'] = {
            'saturated_contraction_count': sat['summary']['saturated_contraction_count'],
            'undersaturated_contraction_count': sat['summary']['undersaturated_contraction_count'],
            'zero_domain_term_count': len(sat['summary']['zero_domain_terms']),
            'term_domain_dims_hist': sat['summary']['term_domain_dims_hist'],
            'linear_passed': lin['necessary_linear_test_passed'],
            'linear_affine_dim': lin['affine_solution_dimension_if_consistent'],
            'transversal_failure_count_reported': trans['failure_count_reported'],
            'transversal_witnesses_head': trans['failures_head'][:8],
        }

        complete_viol = int(scan['complete_violation_count'])
        zero_terms = rec['saturation']['zero_domain_term_count']
        trans_fail = int(trans['failure_count_reported'])
        linear_passed = bool(lin['necessary_linear_test_passed'])
        print('  complete_viol=%s max_excess=%s zero=%s linear=%s trans_fail=%s domain=%s' % (
            complete_viol, scan['max_excess'], zero_terms, linear_passed, trans_fail, rec['saturation']['term_domain_dims_hist']))

        if complete_viol == 0 and zero_terms == 0 and linear_passed and trans_fail == 0:
            rec['candidate_status'] = 'A_SUPPORT_PASSES_CURRENT_COMPLETE_TESTS'
            rounds.append(rec)
            final_status = 'CANDIDATE_SUPPORT_FOUND'
            print('  *** Fixed-A support passes complete Wang + current saturation tests; B/C rank-one completion required. ***')
            break

        added_now = 0
        for v in sorted(scan['violations_head'], key=lambda w: (-int(w['excess']), -int(w['L']), int(w['dim8']))):
            if added_now >= args.add_wang_limit:
                break
            if add_core_row(model, x, int(v['key8']), core, lut, s, added, 'complete_scan_violation'):
                added_now += 1
                added_source['complete_scan_violation'] += 1
        # If the A support already fails non-Wang fixed-A compatibility, exclude the exact set.
        # This is sound only as a candidate-specific cut, not a family theorem.
        if zero_terms > 0 or (not linear_passed) or trans_fail > 0:
            model.AddBoolOr([x[p].Not() for p in support])
            exact_support_exclusions += 1
            rec['exact_support_excluded_for_fixed_A_failure'] = True
        rec['learned_wang_rows_added'] = added_now
        rec['active_wang_after_learning'] = len(added)
        rounds.append(rec)
        final_status = status_name

    result = {
        'schema': 'core_e11_saturation_v3_complete_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': s,
        'scope': 'Boolean distinct projective A-points only; multiplicity-bearing rank-19 decompositions remain outside this model.',
        'complete_core_table_meta': core_meta,
        'final_status': final_status,
        'total_rounds': len(rounds),
        'active_wang_rows_final': len(added),
        'contraction_lower_count': contraction_lower_count,
        'contraction_rank_dist': {str(k): v for k, v in sorted(contraction_rank_dist.items())},
        'added_source_counts': dict(added_source),
        'exact_support_exclusions': exact_support_exclusions,
        'rounds': rounds,
        'total_elapsed_sec': round(time.time() - t_all, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'\nSaved {args.out}')
    print(json.dumps({'final_status': final_status, 'rounds': len(rounds), 'active_wang_rows_final': len(added), 'exact_support_exclusions': exact_support_exclusions}, sort_keys=True))


if __name__ == '__main__':
    main()
