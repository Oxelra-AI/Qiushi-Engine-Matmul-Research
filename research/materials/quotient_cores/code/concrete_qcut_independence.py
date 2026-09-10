#!/usr/bin/env python3
r"""analysis: test whether a concrete quotient-rank cut is independent of Wang rows.

The tested E11-core B-side cut is
  sources q=150,176 saturated => sum_{p:107(p)=1,150(p)=176(p)=0} x_p >= 3.
We ask CP-SAT for a rank-19 A-multiset satisfying all complete core Wang rows,
all contraction lower bounds, the two source saturation equalities, and the
negation lhs <= 2.  SAT would show the cut is not implied by those support-level
constraints.  UNSAT/UNKNOWN here is computational status, not a proof certificate.
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
from candidate_quotient_cut_scan import eval_candidate  # noqa: E402
from quotient_rank_cuts import build_contractions, point_mask_for_q, quotient_cut_instance, evaluate_cut_on_A  # noqa: E402
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis  # noqa: E402

OUTDIR = ROOT / "workspace/data/quotient_rank_cuts"
ALLMASK = (1 << 255) - 1


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}


def add_weight_eq(model, x, points, q: int, rhs: int):
    model.Add(sum(x[p] for p in points if ((int(q) & p).bit_count() & 1)) == int(rhs))


def add_weight_ge(model, x, points, q: int, rhs: int):
    model.Add(sum(x[p] for p in points if ((int(q) & p).bit_count() & 1)) >= int(rhs))


def mask_points(mask: int):
    bits = int(mask)
    while bits:
        lsb = bits & -bits
        idx = lsb.bit_length() - 1
        yield idx + 1
        bits ^= lsb


def main():
    from ortools.sat.python import cp_model

    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', choices=['multiset', 'distinct'], default='multiset')
    ap.add_argument('--time-limit', type=float, default=300.0)
    ap.add_argument('--out', type=Path, default=OUTDIR / 'concrete_qcut_independence_multiset.json')
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    s = 19
    core = CoreQuotient(1)
    T_core = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    lut = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records, meta = build_core_constraints(core, lut)
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}
    instance = quotient_cut_instance(contractions, masks, 'B', [150, 176], 107)
    outside_mask = int(instance['outside_mask_hex'], 16)
    outside_pts = list(mask_points(outside_mask))

    points = list(range(1, 256))
    point_cap = {}
    for p in points:
        key8 = core.key8_from_rows([p])
        key9 = core.key9_from_key8(key8)
        cap = max(0, min(s, s - int(lut[key9])))
        if args.mode == 'distinct':
            cap = min(1, cap)
        point_cap[p] = cap

    model = cp_model.CpModel()
    x = {p: model.NewIntVar(0, point_cap[p], f'x_{p}') for p in points}
    model.Add(sum(x[p] for p in points) == s)
    # Complete Wang rows.
    for rec in records:
        cap = s - int(rec['L'])
        pts = subspace_points_from_basis(unpack_basis(rec['key8']))
        if cap < 0:
            model.Add(0 == 1)
        else:
            model.Add(sum(x[p] for p in pts) <= cap)
    # Contraction lower bounds.
    contraction_lower_count = 0
    for q, c in contractions.items():
        rk = int(c['rank'])
        if rk > 0:
            add_weight_ge(model, x, points, q, rk)
            contraction_lower_count += 1
    # Guard true and cut negated.
    add_weight_eq(model, x, points, 150, int(contractions[150]['rank']))
    add_weight_eq(model, x, points, 176, int(contractions[176]['rank']))
    model.Add(sum(x[p] for p in outside_pts) <= int(instance['projected_rank_requirement']) - 1)

    build_sec = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.time_limit)
    solver.parameters.num_search_workers = 8
    solver.parameters.random_seed = 4567
    tsolve = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - tsolve
    status_name = {cp_model.OPTIMAL:'OPTIMAL', cp_model.FEASIBLE:'FEASIBLE', cp_model.INFEASIBLE:'INFEASIBLE', cp_model.UNKNOWN:'UNKNOWN', cp_model.MODEL_INVALID:'MODEL_INVALID'}.get(status, str(status))
    result = {
        'schema': 'concrete_qcut_independence_v1',
        'field': 'F2',
        'core': 'E11',
        'mode': args.mode,
        'question': 'Is the concrete B-side quotient-rank cut [150,176]=>target107 implied by complete Wang rows plus contraction lower bounds?',
        'complete_wang_row_count': len(records),
        'complete_core_table_meta': meta,
        'contraction_lower_count': contraction_lower_count,
        'cut_instance': instance,
        'negated_cut': {'source_saturations': {'150': int(contractions[150]['rank']), '176': int(contractions[176]['rank'])}, 'outside_lhs_at_most': int(instance['projected_rank_requirement']) - 1},
        'point_cap_distribution': {str(k): int(v) for k, v in sorted(Counter(point_cap.values()).items())},
        'solver_status': status_name,
        'build_sec': round(build_sec, 3),
        'solve_sec': round(solve_sec, 3),
        'total_elapsed_sec': round(time.time() - t0, 3),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        counts = {p: solver.Value(x[p]) for p in points if solver.Value(x[p])}
        A_cols = []
        for p, c in sorted(counts.items()):
            A_cols.extend([p] * int(c))
        result['counts'] = {str(k): int(v) for k, v in sorted(counts.items())}
        result['support'] = A_cols
        result['complete_wang_scan'] = complete_core_wang_scan('concrete_qcut_negation_model', A_cols, s, records, max_head=20)
        sat = saturation_domains(T_core, A_cols)
        lin = sat['summary']['linear_membership']
        trans = transversal_failures(sat['sat_records'], sat['B_domains'], sat['C_domains'], 9, 9, max_report=20)
        qeval = eval_candidate('concrete_qcut_negation_model', A_cols, contractions, masks, max_store=40)
        result['concrete_cut_evaluation'] = evaluate_cut_on_A(instance, A_cols, masks, contractions)
        result['saturation_summary'] = {
            'saturated_contraction_count': sat['summary']['saturated_contraction_count'],
            'undersaturated_contraction_count': sat['summary']['undersaturated_contraction_count'],
            'zero_domain_term_count': len(sat['summary']['zero_domain_terms']),
            'linear_passed': lin['necessary_linear_test_passed'],
            'linear_affine_dim': lin['affine_solution_dimension_if_consistent'],
            'domain_hist': sat['summary']['term_domain_dims_hist'],
            'transversal_failure_count_reported': trans['failure_count_reported'],
            'transversal_witnesses_head': trans['failures_head'][:8],
            'quotient_cut_violated_guarded_instances': qeval['violated_guarded_instances'],
        }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': status_name, 'mode': args.mode, 'build_sec': round(build_sec,3), 'solve_sec': round(solve_sec,3), 'has_model': status in (cp_model.OPTIMAL, cp_model.FEASIBLE)}, sort_keys=True))
    print(f'Saved {args.out}')


if __name__ == '__main__':
    main()
