#!/usr/bin/env python3
"""analysis: rep2 support search with contraction-rank lower constraints.

Previous rep2 CP-SAT relaxations used Wang occupation upper bounds and rank-1
structure, then fixed-A saturation rejected many returned supports.  A cheaper
necessary condition should be imposed before solving:

    for every nonzero q in A*,  |{s : q(a_s)=1}| >= rank(T(q))

because T(q) is a B-by-C matrix equal to a sum of exactly those rank-one
matrices b_s c_s^T.  Equality cases also produce the saturated-domain test from
fixed_A_saturation.py.

This script adds these 511 lower constraints to the normalized adjacent-pair
(prefix [1,2]) support relaxation, optionally together with whole prefix-
stabilizer Wang-row orbits from analysis.  Any SAT support is scanned against the
full Wang LUT and passed through saturated-domain linear membership.  An
INFEASIBLE CP-SAT result is only a proof target until converted to a replayable
CNF/PB certificate.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from pathlib import Path
from typing import Optional

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

from wang_capacity_lazy import make_actions, subspace_points_from_basis, transform_key, transform_mask, unpack_basis
from ruling_line_transport import all_rank1_set, all_ruling_triples, simplify_ruling
from rep2_orbit_promotion_pilot import load_tier_keys, full_lut_scan, span_constraints_for_key
from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2, analyze_fixed_A


def contraction_lower_data(prefix: list[int], candidates: list[int]):
    T = build_matmul_tensor_f2()
    rows = []
    immediate_fail = []
    for q in range(1, 512):
        rk = mat_rank_f2(contraction_matrix(T, q))
        prefix_cnt = sum(1 for p in prefix if ((q & p).bit_count() & 1))
        ci = [i for i, p in enumerate(candidates) if ((q & p).bit_count() & 1)]
        req = rk - prefix_cnt
        rec = {'q': q, 'q_hex': hex(q), 'rank': rk, 'prefix_count': prefix_cnt, 'candidate_count': len(ci), 'required_from_candidates': req, 'indices': ci}
        if req > len(ci):
            immediate_fail.append(rec)
        elif req > 0:
            rows.append(rec)
        else:
            # Keep nonbinding rows out of the model but count them in metadata.
            pass
    return rows, immediate_fail


def collect_wang_constraints(lut, prefix_set, cand_set, cand_idx, initial_max_residual: int, orbit_keys: set[int]):
    constraints = {}
    source_counts = {'base_residual': 0, 'orbit': 0, 'both': 0, 'nonbinding_selected_orbit': 0}
    for key, lb in lut.items():
        is_orbit = key in orbit_keys
        parsed = span_constraints_for_key(int(key), int(lb), prefix_set, cand_set, cand_idx)
        if parsed is None:
            if is_orbit:
                source_counts['nonbinding_selected_orbit'] += 1
            continue
        ci, residual, pts_len, dim, cap, prefix_occ = parsed
        is_base = residual <= initial_max_residual
        if is_base or is_orbit:
            constraints[int(key)] = (ci, residual)
            if is_base and is_orbit:
                source_counts['both'] += 1
            elif is_base:
                source_counts['base_residual'] += 1
            else:
                source_counts['orbit'] += 1
    return constraints, source_counts


def expand_orbit_keys(tiers_path: Path, tier: str, top: Optional[int], stab, lut):
    if tier == 'none':
        return {}, [], set()
    tier_obj, tier_entries, tier_keys = load_tier_keys(tiers_path, tier, top)
    orbit_keys = set()
    orbit_records = []
    for e, key in zip(tier_entries, tier_keys):
        rows = unpack_basis(key)
        expanded = {transform_key(rows, img) for img in stab}
        missing = [k for k in expanded if k not in lut]
        if missing:
            raise RuntimeError(f'missing expanded orbit keys for {hex(key)}')
        lbs = sorted({int(lut[k]) for k in expanded})
        orbit_keys.update(expanded)
        orbit_records.append({
            'canonical_key_hex': hex(key),
            'expanded_key_count': len(expanded),
            'lbs_in_expanded_orbit': lbs,
            'tier_hit_model_count': e.get('hit_model_count'),
            'tier_residual_after_prefix': e.get('residual_after_prefix'),
            'tier_lb': e.get('lb'),
            'tier_dim': e.get('dim'),
        })
    return tier_obj, orbit_records, orbit_keys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--tiers', default='data/corrected_strategy/rep2_orbit_promotion_tiers.json')
    ap.add_argument('--tier', choices=['none', 'all5', 'strong4plus', 'hit4plus'], default='none')
    ap.add_argument('--top', type=int, default=None)
    ap.add_argument('--initial-max-residual', type=int, default=2)
    ap.add_argument('--time-limit', type=float, default=300.0)
    ap.add_argument('--out', default='data/rep2_contraction_lower/none/result.json')
    args = ap.parse_args()
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    prefix = [1, 2]
    prefix_set = set(prefix)
    candidates = [p for p in range(1, 512) if p not in prefix_set]
    cand_set = set(candidates)
    cand_idx = {p: i for i, p in enumerate(candidates)}
    target = 18
    r1_all = all_rank1_set()
    r1_indices = [cand_idx[p] for p in candidates if p in r1_all]

    print('Loading LUT...')
    t0 = time.time()
    with open(args.lut, 'rb') as f:
        payload = pickle.load(f)
    lut = {int(k): int(v) for k, v in payload['lut'].items()}
    print(f'  lut={len(lut):,} load_sec={time.time()-t0:.1f}')

    print('Building prefix stabilizer...')
    actions = make_actions()
    stab = [img for img in actions if {transform_mask(p, img) for p in prefix} == prefix_set]

    print('Expanding selected Wang row orbits...')
    _, orbit_records, orbit_keys = expand_orbit_keys(Path(args.tiers), args.tier, args.top, stab, lut)
    print(f'  tier={args.tier} top={args.top} orbit_keys={len(orbit_keys)}')

    print('Collecting Wang upper constraints...')
    t1 = time.time()
    wang_constraints, source_counts = collect_wang_constraints(lut, prefix_set, cand_set, cand_idx, args.initial_max_residual, orbit_keys)
    print(f'  wang_constraints={len(wang_constraints):,} source_counts={source_counts} sec={time.time()-t1:.1f}')

    lower_rows, immediate_lower_fail = contraction_lower_data(prefix, candidates)
    print(f'Contraction lower rows={len(lower_rows)} immediate_fail={len(immediate_lower_fail)}')

    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x{i}') for i in range(len(candidates))]
    model.Add(sum(x) == target)
    model.Add(sum(x[i] for i in r1_indices) <= 15)
    for ci, residual in wang_constraints.values():
        model.Add(sum(x[i] for i in ci) <= residual)
    for rec in lower_rows:
        model.Add(sum(x[i] for i in rec['indices']) >= int(rec['required_from_candidates']))

    rc = simplify_ruling(all_ruling_triples(), prefix_set)
    ruling_counts = {'unit': 0, 'binary': 0, 'ternary': 0}
    for p in rc['unit']:
        if p in cand_idx:
            model.Add(x[cand_idx[p]] == 0)
            ruling_counts['unit'] += 1
    for a, b in rc['binary']:
        if a in cand_idx and b in cand_idx:
            model.Add(x[cand_idx[a]] + x[cand_idx[b]] <= 1)
            ruling_counts['binary'] += 1
    for a, b, c in rc['ternary']:
        if a in cand_idx and b in cand_idx and c in cand_idx:
            model.Add(x[cand_idx[a]] + x[cand_idx[b]] + x[cand_idx[c]] <= 2)
            ruling_counts['ternary'] += 1

    result = {
        'schema': 'rep2_contraction_lower_pilot_v1',
        'field': 'F2',
        'meaning': 'Normalized adjacent-pair A-support relaxation with Wang upper bounds, rank-1 structural bound, ruling-line clauses, and contraction-rank lower bounds. CP-SAT infeasibility is a proof target only until replayed.',
        'prefix': prefix,
        'target_additional_points': target,
        'total_support_size': 20,
        'rank1_candidate_limit': 15,
        'initial_max_residual': args.initial_max_residual,
        'tier': args.tier,
        'top': args.top,
        'setwise_stabilizer_order': len(stab),
        'expanded_orbit_key_count': len(orbit_keys),
        'orbit_records': orbit_records,
        'wang_constraint_count': len(wang_constraints),
        'wang_source_counts': source_counts,
        'contraction_lower_constraint_count': len(lower_rows),
        'contraction_lower_immediate_fail_count': len(immediate_lower_fail),
        'contraction_lower_immediate_fail_head': immediate_lower_fail[:20],
        'ruling_counts': ruling_counts,
    }
    if immediate_lower_fail:
        result.update({'status': 'INFEASIBLE_BY_CONTRACTION_LOWER_IMMEDIATE', 'total_elapsed_sec': round(time.time() - t0, 2)})
        out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
        print(json.dumps({'out': str(out_path), 'status': result['status']}, sort_keys=True))
        return

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.time_limit
    solver.parameters.num_workers = 8
    solver.parameters.random_seed = 424242
    t2 = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - t2
    status_name = {
        cp_model.OPTIMAL: 'OPTIMAL',
        cp_model.FEASIBLE: 'FEASIBLE',
        cp_model.INFEASIBLE: 'INFEASIBLE',
        cp_model.MODEL_INVALID: 'MODEL_INVALID',
        cp_model.UNKNOWN: 'UNKNOWN',
    }.get(status, str(status))
    result.update({'status': status_name, 'solve_sec': round(solve_sec, 2), 'cp_model_stats': solver.ResponseStats()})
    print(f'Solve status={status_name} sec={solve_sec:.1f}')

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        selected = [candidates[i] for i in range(len(candidates)) if solver.Value(x[i])]
        support = sorted(prefix + selected)
        print('Scanning SAT support against full LUT...')
        scan = full_lut_scan(lut, set(support))
        print('Running saturated-domain fixed-A test...')
        sat = analyze_fixed_A('rep2_contraction_lower_candidate', build_matmul_tensor_f2(), support, None)
        result.update({
            'selected_points': selected,
            'support': support,
            'rank1_total': sum(1 for p in support if p in r1_all),
            'higher_rank_total': sum(1 for p in support if p not in r1_all),
            'full_lut_scan': scan,
            'saturation_brief': {
                'undersaturated_contraction_count': sat['undersaturated_contraction_count'],
                'saturated_contraction_count': sat['saturated_contraction_count'],
                'term_domain_dims_hist': sat['term_domain_dims_hist'],
                'linear_membership': sat['linear_membership'],
            },
        })
        print(f"  full violations={scan['violation_count']} max_excess={scan['max_excess']} rank1_total={result['rank1_total']} linear={sat['linear_membership']['necessary_linear_test_passed']} undersat={sat['undersaturated_contraction_count']}")
    elif status == 'INFEASIBLE':
        result['infeasible_warning'] = 'Convert this formula into CNF/PB and independently replay before using as mathematical evidence.'
    result['total_elapsed_sec'] = round(time.time() - t0, 2)
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(out_path),
        'status': status_name,
        'wang_constraints': len(wang_constraints),
        'lower_constraints': len(lower_rows),
        'violations': result.get('full_lut_scan', {}).get('violation_count'),
        'linear': result.get('saturation_brief', {}).get('linear_membership', {}).get('necessary_linear_test_passed'),
        'solve_sec': round(solve_sec, 2),
    }, sort_keys=True))


if __name__ == '__main__':
    main()
