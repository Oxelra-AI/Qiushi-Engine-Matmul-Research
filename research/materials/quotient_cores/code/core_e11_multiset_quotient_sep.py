#!/usr/bin/env python3
r"""analysis: E11-core multiset search with guarded quotient-rank cuts.

This extends the analysis multiset pilot by learning family-level consequences of
saturated source contractions.  For source pair S={q1,q2}, side B/C, W=sum of
source side spaces, and target t, the guarded inequality is

    sat(q1) & sat(q2)  ==>  sum_{p: t(p)=1, q1(p)=q2(p)=0} x_p
                              >= rank(pi_W side_space(L(t))).

The target t is not required to be saturated.  This is a construction-search
separator with complete Wang rescanning; it is not a proof-producing lower-bound
certificate unless exported and replayed in an exact proof system later.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Sequence, Tuple

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
from core_e11_multiset_pilot import add_core_row, add_exact_multiset_nogood  # noqa: E402
from candidate_quotient_cut_scan import eval_candidate  # noqa: E402
from quotient_rank_cuts import (  # noqa: E402
    build_contractions,
    point_mask_for_q,
    projection_rank_mod_space,
    sum_basis,
)
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis  # noqa: E402

OUTDIR = ROOT / "workspace/data/quotient_rank_cuts"
ALLMASK = (1 << 255) - 1


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}


class QuotientCutAdder:
    def __init__(self, model, x, points, contractions, masks):
        self.model = model
        self.x = x
        self.points = list(points)
        self.contractions = contractions
        self.masks = masks
        self.sat_lits: Dict[int, object] = {}
        self.cut_keys: set[Tuple[str, int, int, int]] = set()
        self.W_cache: Dict[Tuple[str, int, int], Tuple[Tuple[int, ...], int, int]] = {}
        self.req_cache: Dict[Tuple[str, int, int, int], Tuple[int, Tuple[int, ...], int, int]] = {}

    def weight_expr(self, q: int):
        return sum(self.x[p] for p in self.points if ((int(q) & p).bit_count() & 1))

    def sat_lit(self, q: int):
        q = int(q)
        if q in self.sat_lits:
            return self.sat_lits[q]
        rk = int(self.contractions[q]['rank'])
        y = self.model.NewBoolVar(f'sat_q{q}')
        w = self.weight_expr(q)
        self.model.Add(w == rk).OnlyEnforceIf(y)
        # Contraction lower bounds w >= rk are already imposed.  Therefore not-y
        # is exactly w >= rk+1 for nonzero-rank contractions.
        self.model.Add(w >= rk + 1).OnlyEnforceIf(y.Not())
        self.sat_lits[q] = y
        return y

    def compute_cut(self, side: str, q1: int, q2: int, target: int):
        q1, q2 = sorted((int(q1), int(q2)))
        target = int(target)
        side_key = 'B_space' if side == 'B' else 'C_space'
        wk = (side, q1, q2)
        if wk not in self.W_cache:
            W = sum_basis([self.contractions[q1][side_key], self.contractions[q2][side_key]], 9)
            union = self.masks[q1] | self.masks[q2]
            self.W_cache[wk] = (W, len(W), union)
        W, Wdim, union = self.W_cache[wk]
        rk = (side, q1, q2, target)
        if rk not in self.req_cache:
            req = projection_rank_mod_space(self.contractions[target][side_key], W, 9)
            outside_mask = self.masks[target] & (~union) & ALLMASK
            outside_pts = tuple(p for p in self.points if (outside_mask >> (p - 1)) & 1)
            self.req_cache[rk] = (int(req), outside_pts, int(outside_mask.bit_count()), Wdim)
        return self.req_cache[rk]

    def add_cut(self, side: str, q1: int, q2: int, target: int) -> bool:
        q1, q2 = sorted((int(q1), int(q2)))
        key = (side, q1, q2, int(target))
        if key in self.cut_keys:
            return False
        req, outside_pts, outside_size, Wdim = self.compute_cut(side, q1, q2, int(target))
        if req <= 0:
            return False
        self.model.Add(sum(self.x[p] for p in outside_pts) >= int(req)).OnlyEnforceIf([
            self.sat_lit(q1), self.sat_lit(q2)
        ])
        self.cut_keys.add(key)
        return True


def main():
    from ortools.sat.python import cp_model

    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--rank', type=int, default=19)
    ap.add_argument('--max-rounds', type=int, default=8)
    ap.add_argument('--solver-time', type=float, default=180.0)
    ap.add_argument('--add-wang-limit', type=int, default=1000)
    ap.add_argument('--add-qcut-limit', type=int, default=200)
    ap.add_argument('--out', type=Path, default=OUTDIR / 'core_e11_multiset_quotient_sep.json')
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    s = int(args.rank)
    core = CoreQuotient(1)
    T_core = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    lut = load_lut(args.lut)
    records, meta = build_core_constraints(core, lut)
    points = list(range(1, 256))

    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}

    point_cap = {}
    for p in points:
        key8 = core.key8_from_rows([p])
        key9 = core.key9_from_key8(key8)
        point_cap[p] = max(0, min(s, s - int(lut[key9])))
    cap_dist = Counter(point_cap.values())

    model = cp_model.CpModel()
    x = {p: model.NewIntVar(0, point_cap[p], f'x_{p}') for p in points}
    model.Add(sum(x[p] for p in points) == s)

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

    contraction_lower_count = 0
    contraction_rank_dist = Counter()
    for q, c in contractions.items():
        rk = int(c['rank'])
        contraction_rank_dist[rk] += 1
        if rk > 0:
            model.Add(sum(x[p] for p in points if ((q & p).bit_count() & 1)) >= rk)
            contraction_lower_count += 1

    qadder = QuotientCutAdder(model, x, points, contractions, masks)

    print(f'point_cap_dist={dict(cap_dist)} repeat_cap_points={repeat_cap_points}')
    print(f'initial rows={len(added)} contraction_lower={contraction_lower_count} rank_dist={dict(sorted(contraction_rank_dist.items()))}')

    rounds = []
    exact_nogoods = 0
    final_status = None
    for rnd in range(args.max_rounds):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(args.solver_time)
        solver.parameters.num_search_workers = 8
        solver.parameters.random_seed = 4520 + 29 * rnd
        tsolve = time.time()
        status = solver.Solve(model)
        solve_sec = time.time() - tsolve
        status_name = {cp_model.OPTIMAL:'OPTIMAL', cp_model.FEASIBLE:'FEASIBLE', cp_model.INFEASIBLE:'INFEASIBLE', cp_model.UNKNOWN:'UNKNOWN', cp_model.MODEL_INVALID:'MODEL_INVALID'}.get(status, str(status))
        print(f'\nRound {rnd}: status={status_name} solve_sec={solve_sec:.1f} rows={len(added)} qcuts={len(qadder.cut_keys)} nogoods={exact_nogoods}')
        rec = {'round': rnd, 'status': status_name, 'solve_sec': round(solve_sec, 3), 'active_wang_rows': len(added), 'active_quotient_cuts': len(qadder.cut_keys), 'exact_nogoods': exact_nogoods}
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rounds.append(rec); final_status = status_name; break

        counts = {p: solver.Value(x[p]) for p in points if solver.Value(x[p])}
        A_cols = []
        for p, c in sorted(counts.items()):
            A_cols.extend([p] * int(c))
        rec['counts'] = {str(k): int(v) for k, v in sorted(counts.items())}
        rec['support'] = A_cols
        rec['distinct_A_points'] = len(counts)
        rec['max_multiplicity'] = max(counts.values())
        rec['multiplicity_hist'] = {str(k): int(v) for k, v in sorted(Counter(counts.values()).items())}

        scan = complete_core_wang_scan(f'multiset_qcut_round{rnd}', A_cols, s, records, max_head=max(80, args.add_wang_limit))
        sat = saturation_domains(T_core, A_cols)
        lin = sat['summary']['linear_membership']
        trans = transversal_failures(sat['sat_records'], sat['B_domains'], sat['C_domains'], 9, 9, max_report=40)
        qeval = eval_candidate(f'multiset_qcut_round{rnd}', A_cols, contractions, masks, max_store=max(80, int(args.add_qcut_limit)))
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
            'transversal_witnesses_head': trans['failures_head'][:8],
        }
        rec['quotient_cut_eval'] = {k: v for k, v in qeval.items() if k != 'violations_head'}
        rec['quotient_cut_violations_head'] = qeval['violations_head'][:20]
        print('  distinct=%s maxmult=%s complete_viol=%s max_excess=%s zero=%s linear=%s trans=%s qviol=%s' % (
            rec['distinct_A_points'], rec['max_multiplicity'], scan['complete_violation_count'], scan['max_excess'], rec['saturation']['zero_domain_term_count'], rec['saturation']['linear_passed'], rec['saturation']['transversal_failure_count_reported'], qeval['violated_guarded_instances']))

        if scan['complete_violation_count'] == 0 and rec['saturation']['zero_domain_term_count'] == 0 and rec['saturation']['linear_passed'] and rec['saturation']['transversal_failure_count_reported'] == 0 and qeval['violated_guarded_instances'] == 0:
            rec['candidate_status'] = 'MULTISET_A_SUPPORT_PASSES_CURRENT_COMPLETE_TESTS_NEEDS_RANKONE_SOLVE'
            rounds.append(rec); final_status = 'CANDIDATE_FOUND'; break

        q_added = 0
        learned_qcuts = []
        for v in qeval['violations_head'][:int(args.add_qcut_limit)]:
            if qadder.add_cut(v['side'], int(v['sources'][0]), int(v['sources'][1]), int(v['target'])):
                q_added += 1
                learned_qcuts.append({
                    'side': v['side'],
                    'sources': [int(v['sources'][0]), int(v['sources'][1])],
                    'target': int(v['target']),
                    'source_ranks': [int(v['source_ranks'][0]), int(v['source_ranks'][1])],
                    'W_dim': int(v['W_dim']),
                    'requirement': int(v['requirement']),
                    'outside_point_count': int(v['outside_point_count']),
                    'outside_lhs_on_current_model': int(v['outside_lhs']),
                    'target_rank': int(v['target_rank']),
                    'target_saturated_on_current_model': bool(v['target_saturated']),
                })
        rec['learned_quotient_cuts_added'] = q_added
        rec['learned_quotient_cuts'] = learned_qcuts

        added_now = 0
        learned_wang_rows = []
        for v in sorted(scan['violations_head'], key=lambda z: (-int(z['excess']), -int(z['L'])))[:args.add_wang_limit]:
            if add_core_row(model, x, int(v['key8']), core, lut, s, added):
                added_now += 1
                added_source['complete_scan_violation'] += 1
                learned_wang_rows.append({
                    'key8': int(v['key8']),
                    'key9': int(v['key9']),
                    'basis8': [int(z) for z in v['basis8']],
                    'basis9': [int(z) for z in v['basis9']],
                    'dim8': int(v['dim8']),
                    'dim9': int(v['dim9']),
                    'L': int(v['L']),
                    'cap': int(v['cap']),
                    'occupancy_on_current_model': int(v['occupancy']),
                    'excess_on_current_model': int(v['excess']),
                })
        rec['learned_wang_rows_added'] = added_now
        rec['learned_wang_rows'] = learned_wang_rows

        fixed_A_fail = rec['saturation']['zero_domain_term_count'] > 0 or (not rec['saturation']['linear_passed']) or rec['saturation']['transversal_failure_count_reported'] > 0
        # Exact multiset no-good only if the stronger quotient separator did not
        # already remove this support family instance.  This keeps the run focused
        # on reusable cuts where available.
        if fixed_A_fail and q_added == 0:
            add_exact_multiset_nogood(model, x, counts, points, point_cap, f'r{rnd}')
            exact_nogoods += 1
            rec['exact_multiset_nogood_added'] = True
        rounds.append(rec); final_status = status_name

    result = {
        'schema': 'core_e11_multiset_quotient_sep_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': s,
        'scope': 'Construction-search pilot for repeated A-directions. Uses complete Wang rescanning and guarded quotient-rank cuts; statuses are not proof certificates.',
        'point_cap_distribution': {str(k): int(v) for k, v in sorted(cap_dist.items())},
        'repeat_cap_points': repeat_cap_points,
        'complete_core_table_meta': meta,
        'contraction_lower_count': contraction_lower_count,
        'contraction_rank_dist': {str(k): int(v) for k, v in sorted(contraction_rank_dist.items())},
        'final_status': final_status,
        'total_rounds': len(rounds),
        'final_wang_rows': len(added),
        'final_quotient_cuts': len(qadder.cut_keys),
        'saturation_bool_vars': len(qadder.sat_lits),
        'added_source_counts': dict(added_source),
        'exact_multiset_nogoods': exact_nogoods,
        'rounds': rounds,
        'total_elapsed_sec': round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'\nSaved {args.out}')
    print(json.dumps({'final_status': final_status, 'rounds': len(rounds), 'rows': len(added), 'qcuts': len(qadder.cut_keys), 'nogoods': exact_nogoods}, sort_keys=True))


if __name__ == '__main__':
    main()
