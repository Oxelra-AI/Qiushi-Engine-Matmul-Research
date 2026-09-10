#!/usr/bin/env python3
r"""analysis: Fresh unconditional E11 core separator for ALL rank-19 supports.

This is the decisive experiment: learn Wang rows and unconditional quotient-rank
cuts without a repeat-direction constraint, so the model covers both distinct
and multiset A-supports.  If INFEASIBLE, all E11 rank-19 decompositions over F2
are excluded.

Key design:
- Pure ILP: 255 integer variables x_p in [0, cap_p]
- NO repeat constraint
- Learns unconditional cuts: N_out + sum(w_q - r_q) >= R
- Complete Wang rescanning each round
- Stores ALL learned rows and cuts for independent replay
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence, Set, Tuple
import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient
from fixed_A_saturation import mat_rank_f2
from complete_core_and_transversal import (
    ROOT, build_core_constraints, complete_core_wang_scan,
    saturation_domains, transversal_failures,
)
from quotient_rank_cuts import (
    build_contractions, counts_from_A, point_mask_for_q,
    projection_rank_mod_space, sum_basis,
)
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis

OUTDIR = ROOT / "workspace/data/unconditional_qcuts"
ALLMASK = (1 << 255) - 1


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}


def scan_unconditional_quotient_violations(
    A_cols: Sequence[int],
    contractions: Dict[int, dict],
    masks: Dict[int, int],
    points: List[int],
    existing_cuts: Set[Tuple],
    max_store: int = 200,
) -> dict:
    """Scan pair-source unconditional quotient-rank cuts violated by A_cols."""
    counts = counts_from_A(A_cols)
    nonzero_q = [q for q, c in contractions.items() if int(c['rank']) > 0]

    # Precompute weights
    weights = {}
    for q in nonzero_q:
        weights[q] = sum(int(counts.get(p, 0)) for p in range(1, 256) if ((q & p).bit_count() & 1))

    violations = []
    total_checked = 0
    for i, q1 in enumerate(nonzero_q):
        for q2 in nonzero_q[i + 1:]:
            source_union = masks[q1] | masks[q2]
            rq1 = int(contractions[q1]['rank'])
            rq2 = int(contractions[q2]['rank'])
            wq1 = weights[q1]
            wq2 = weights[q2]
            excess1 = wq1 - rq1
            excess2 = wq2 - rq2
            for side in ('B', 'C'):
                side_key = 'B_space' if side == 'B' else 'C_space'
                W = sum_basis([contractions[q1][side_key], contractions[q2][side_key]], 9)
                if len(W) >= 9:
                    continue
                for target in nonzero_q:
                    req = projection_rank_mod_space(contractions[target][side_key], W, 9)
                    if req <= 0:
                        continue
                    total_checked += 1
                    outside = masks[target] & (~source_union) & ALLMASK
                    N_out = sum(int(counts.get(p, 0)) for p in range(1, 256) if (outside >> (p - 1)) & 1)
                    uncond_lhs = N_out + excess1 + excess2
                    if uncond_lhs < req:
                        key = (side, min(q1, q2), max(q1, q2), target)
                        violations.append({
                            'side': side,
                            'sources': [min(q1, q2), max(q1, q2)],
                            'target': target,
                            'source_ranks': [rq1, rq2],
                            'W_dim': len(W),
                            'requirement': req,
                            'outside_point_count': int(outside.bit_count()),
                            'N_out': N_out,
                            'excess_sum': excess1 + excess2,
                            'uncond_lhs': uncond_lhs,
                            'deficit': req - uncond_lhs,
                            'is_new': key not in existing_cuts,
                        })
    violations.sort(key=lambda v: (-v['deficit'], -v['requirement']))
    return {
        'total_checked': total_checked,
        'violation_count': len(violations),
        'new_violation_count': sum(1 for v in violations if v['is_new']),
        'violations_head': violations[:max_store],
    }


def add_wang_row(model, x, key8, core, lut, s, added):
    """Add a Wang occupancy row to the CP-SAT model."""
    if key8 in added:
        return False
    key9 = core.key9_from_key8(key8)
    L_val = int(lut[key9])
    cap = s - L_val
    pts = subspace_points_from_basis(unpack_basis(key8))
    if cap < 0:
        model.Add(0 == 1)
    else:
        model.Add(sum(x[p] for p in pts) <= cap)
    added.add(key8)
    return True


def add_unconditional_cut(model, x, points, contractions, masks, cut, cut_keys):
    """Add an unconditional quotient-rank cut to the CP-SAT model."""
    q1, q2 = int(cut['sources'][0]), int(cut['sources'][1])
    q1, q2 = min(q1, q2), max(q1, q2)
    target = int(cut['target'])
    side = cut['side']
    key = (side, q1, q2, target)
    if key in cut_keys:
        return False
    req = int(cut['requirement'])
    rq1 = int(contractions[q1]['rank'])
    rq2 = int(contractions[q2]['rank'])
    source_union = masks[q1] | masks[q2]
    outside_mask = masks[target] & (~source_union) & ALLMASK

    # Unconditional: sum of (outside coeff + q1 coeff + q2 coeff) * x_p >= R + rq1 + rq2
    lhs_terms = []
    for p in points:
        coeff = 0
        if (outside_mask >> (p - 1)) & 1:
            coeff += 1
        if ((q1 & p).bit_count() & 1):
            coeff += 1
        if ((q2 & p).bit_count() & 1):
            coeff += 1
        if coeff > 0:
            lhs_terms.append((p, coeff))
    rhs = req + rq1 + rq2
    model.Add(sum(coeff * x[p] for p, coeff in lhs_terms) >= rhs)
    cut_keys.add(key)
    return True


def main():
    from ortools.sat.python import cp_model

    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--rank', type=int, default=19)
    ap.add_argument('--max-rounds', type=int, default=30)
    ap.add_argument('--solver-time', type=float, default=300.0)
    ap.add_argument('--add-wang-limit', type=int, default=500)
    ap.add_argument('--add-qcut-limit', type=int, default=200)
    ap.add_argument('--out', type=Path, default=OUTDIR / 'fresh_unconditional_separator.json')
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
    # NO repeat constraint — covers both distinct and multiset

    added = set()
    added_source = Counter()
    for rec in records:
        if int(rec['dim8']) in (1, 2):
            if add_wang_row(model, x, rec['key8'], core, lut, s, added):
                added_source[f"initial_dim{rec['dim8']}"] += 1

    # Contraction lower bounds
    contraction_lower_count = 0
    contraction_rank_dist = Counter()
    for q, c in contractions.items():
        rk = int(c['rank'])
        contraction_rank_dist[rk] += 1
        if rk > 0:
            model.Add(sum(x[p] for p in points if ((q & p).bit_count() & 1)) >= rk)
            contraction_lower_count += 1

    cut_keys: Set[Tuple] = set()

    print(f'point_cap_dist={dict(cap_dist)} repeat_cap_points=[{",".join(str(p) for p in points if point_cap[p]>=2)}]')
    print(f'initial rows={len(added)} contraction_lower={contraction_lower_count}')

    rounds = []
    final_status = None
    for rnd in range(args.max_rounds):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(args.solver_time)
        solver.parameters.num_search_workers = 8
        solver.parameters.random_seed = 4600 + 31 * rnd
        tsolve = time.time()
        status = solver.Solve(model)
        solve_sec = time.time() - tsolve
        status_name = {
            cp_model.OPTIMAL: 'OPTIMAL', cp_model.FEASIBLE: 'FEASIBLE',
            cp_model.INFEASIBLE: 'INFEASIBLE', cp_model.UNKNOWN: 'UNKNOWN',
            cp_model.MODEL_INVALID: 'MODEL_INVALID',
        }.get(status, str(status))

        print(f'\nRound {rnd}: status={status_name} solve_sec={solve_sec:.1f} wang={len(added)} qcuts={len(cut_keys)}')
        rec = {
            'round': rnd, 'status': status_name,
            'solve_sec': round(solve_sec, 3),
            'active_wang_rows': len(added),
            'active_quotient_cuts': len(cut_keys),
        }
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rounds.append(rec)
            final_status = status_name
            break

        counts = {p: solver.Value(x[p]) for p in points if solver.Value(x[p])}
        A_cols = []
        for p, c in sorted(counts.items()):
            A_cols.extend([p] * int(c))
        rec['support'] = A_cols
        rec['distinct_A'] = len(counts)
        rec['max_mult'] = max(counts.values()) if counts else 0
        rec['mult_hist'] = {str(k): int(v) for k, v in sorted(Counter(counts.values()).items())}

        # Complete Wang scan
        scan = complete_core_wang_scan(f'uncond_round{rnd}', A_cols, s, records, max_head=max(80, args.add_wang_limit))
        rec['complete_wang_violations'] = scan['complete_violation_count']
        rec['max_excess'] = scan['max_excess']

        # Saturation domains
        sat = saturation_domains(T_core, A_cols)
        sat_sum = sat['summary']
        lin = sat_sum['linear_membership']
        rec['saturated_contractions'] = sat_sum['saturated_contraction_count']
        rec['zero_domain_terms'] = len(sat_sum['zero_domain_terms'])
        rec['linear_pass'] = lin['necessary_linear_test_passed']
        rec['affine_dim'] = lin['affine_solution_dimension_if_consistent']

        # Transversal failures
        trans = transversal_failures(sat['sat_records'], sat['B_domains'], sat['C_domains'], 9, 9, max_report=10)
        rec['transversal_failures'] = trans['failure_count_reported']

        # Unconditional quotient-rank violations
        qscan = scan_unconditional_quotient_violations(A_cols, contractions, masks, points, cut_keys, max_store=args.add_qcut_limit)
        rec['uncond_qcut_violations'] = qscan['violation_count']
        rec['uncond_qcut_new'] = qscan['new_violation_count']

        print(f'  distinct={rec["distinct_A"]} maxmult={rec["max_mult"]} wang_viol={rec["complete_wang_violations"]} '
              f'zero_dom={rec["zero_domain_terms"]} linear={rec["linear_pass"]} trans={rec["transversal_failures"]} '
              f'qcut_viol={rec["uncond_qcut_violations"]} qcut_new={rec["uncond_qcut_new"]}')

        # Check if candidate
        if (rec['complete_wang_violations'] == 0 and rec['zero_domain_terms'] == 0
                and rec['linear_pass'] and rec['transversal_failures'] == 0
                and rec['uncond_qcut_violations'] == 0):
            rec['candidate_status'] = 'PASSES_ALL_NECESSARY_TESTS'
            rounds.append(rec)
            final_status = 'CANDIDATE_FOUND'
            break

        # Learn new quotient cuts
        q_added = 0
        learned_qcuts = []
        for v in qscan['violations_head'][:args.add_qcut_limit]:
            if add_unconditional_cut(model, x, points, contractions, masks, v, cut_keys):
                q_added += 1
                learned_qcuts.append({
                    'side': v['side'],
                    'sources': v['sources'],
                    'target': v['target'],
                    'source_ranks': v['source_ranks'],
                    'W_dim': v['W_dim'],
                    'requirement': v['requirement'],
                    'outside_point_count': v['outside_point_count'],
                })
        rec['learned_qcuts_added'] = q_added
        rec['learned_qcuts'] = learned_qcuts

        # Learn Wang rows
        w_added = 0
        learned_wang = []
        for v in sorted(scan['violations_head'], key=lambda z: (-int(z['excess']), -int(z['L'])))[:args.add_wang_limit]:
            if add_wang_row(model, x, int(v['key8']), core, lut, s, added):
                w_added += 1
                added_source['complete_scan_violation'] += 1
                learned_wang.append({
                    'key8': int(v['key8']),
                    'key9': int(v['key9']),
                    'basis8': [int(z) for z in v['basis8']],
                    'dim8': int(v['dim8']),
                    'L': int(v['L']),
                    'cap': int(v['cap']),
                })
        rec['learned_wang_added'] = w_added
        rec['learned_wang'] = learned_wang
        rounds.append(rec)
        final_status = status_name

    result = {
        'schema': 'fresh_unconditional_separator_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': s,
        'scope': 'ALL rank-19 core A-supports (distinct and multiset). No repeat constraint.',
        'point_cap_distribution': {str(k): int(v) for k, v in sorted(cap_dist.items())},
        'complete_core_table_meta': meta,
        'contraction_lower_count': contraction_lower_count,
        'final_status': final_status,
        'total_rounds': len(rounds),
        'final_wang_rows': len(added),
        'final_quotient_cuts': len(cut_keys),
        'added_source_counts': dict(added_source),
        'rounds': rounds,
        'total_elapsed_sec': round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'\nSaved {args.out}')
    print(json.dumps({
        'final_status': final_status,
        'rounds': len(rounds),
        'wang': len(added),
        'qcuts': len(cut_keys),
    }, sort_keys=True))


if __name__ == '__main__':
    main()
