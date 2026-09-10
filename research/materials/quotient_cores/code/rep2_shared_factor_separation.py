#!/usr/bin/env python3
"""analysis: rep2 support separation using shared B/C-factor compatibility.

This is a support-level experiment that goes beyond Wang occupation alone.  It
starts from the normalized adjacent-pair support relaxation with:
  * Wang upper constraints (base residual tier plus optional row-orbit tier),
  * transported ruling-line clauses,
  * contraction-rank lower bounds |I_q| >= rank T(q).

For each returned support, it performs the saturated-contraction domain test.
When a term has B_s={0} or C_s={0}, it extracts a small subset of saturated
contractions q_i whose column/row spaces intersect in zero.  Since contraction
lower bounds are already imposed, every valid support containing that A-term must
make at least one of those contractions nonsaturated, i.e. |I_{q_i}| >= rank+1.
The learned pure support cut is

    p not selected  OR  (|I_{q_1}|>=rank(q_1)+1) OR ... .

This is not yet a mathematical proof; an UNSAT result must be exported to a
replayable proof system.  The purpose is to test whether shared-factor
compatibility gives compact information that Wang-only separation misses.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

from wang_capacity_lazy import make_actions, subspace_points_from_basis, transform_key, transform_mask, unpack_basis
from ruling_line_transport import all_rank1_set, all_ruling_triples, simplify_ruling
from rep2_orbit_promotion_pilot import load_tier_keys, full_lut_scan, span_constraints_for_key
from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2, analyze_fixed_A
from zero_domain_certificates import saturated_records_by_term, find_zero_subset


def contraction_lower_data(prefix, candidates):
    T = build_matmul_tensor_f2()
    rows = []
    for q in range(1, 512):
        rk = mat_rank_f2(contraction_matrix(T, q))
        prefix_cnt = sum(1 for p in prefix if ((q & p).bit_count() & 1))
        ci = [i for i, p in enumerate(candidates) if ((q & p).bit_count() & 1)]
        req = rk - prefix_cnt
        if req > 0:
            rows.append({'q': q, 'rank': rk, 'prefix_count': prefix_cnt, 'required_from_candidates': req, 'indices': ci})
    return rows


def collect_wang_constraints(lut, prefix_set, cand_set, cand_idx, initial_max_residual, orbit_keys):
    constraints = {}
    source_counts = {'base_residual': 0, 'orbit': 0, 'both': 0, 'learned': 0, 'nonbinding_selected_orbit': 0}
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
            constraints[int(key)] = {'indices': ci, 'residual': residual, 'lb': int(lb), 'source': 'base_or_orbit'}
            if is_base and is_orbit:
                source_counts['both'] += 1
            elif is_base:
                source_counts['base_residual'] += 1
            else:
                source_counts['orbit'] += 1
    return constraints, source_counts


def expand_orbit_keys(tiers_path, tier, top, stab, lut):
    if tier == 'none':
        return [], set()
    _, tier_entries, tier_keys = load_tier_keys(Path(tiers_path), tier, top)
    orbit_keys = set()
    orbit_records = []
    for e, key in zip(tier_entries, tier_keys):
        rows = unpack_basis(key)
        expanded = {transform_key(rows, img) for img in stab}
        if any(k not in lut for k in expanded):
            raise RuntimeError(f'missing expanded LUT key for {hex(key)}')
        orbit_keys.update(expanded)
        orbit_records.append({'canonical_key_hex': hex(key), 'expanded_key_count': len(expanded), 'tier_hit_model_count': e.get('hit_model_count'), 'tier_lb': e.get('lb'), 'tier_dim': e.get('dim'), 'tier_residual_after_prefix': e.get('residual_after_prefix')})
    return orbit_records, orbit_keys


def add_wang_constraint(model, x, constraints, key, lb, prefix_set, cand_set, cand_idx, source):
    if key in constraints:
        return False
    parsed = span_constraints_for_key(int(key), int(lb), prefix_set, cand_set, cand_idx)
    if parsed is None:
        return False
    ci, residual, pts_len, dim, cap, prefix_occ = parsed
    model.Add(sum(x[i] for i in ci) <= int(residual))
    constraints[int(key)] = {'indices': ci, 'residual': int(residual), 'lb': int(lb), 'source': source}
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--tiers', default='data/corrected_strategy/rep2_orbit_promotion_tiers.json')
    ap.add_argument('--tier', choices=['none', 'all5', 'strong4plus', 'hit4plus'], default='all5')
    ap.add_argument('--top', type=int, default=None)
    ap.add_argument('--initial-max-residual', type=int, default=2)
    ap.add_argument('--max-rounds', type=int, default=4)
    ap.add_argument('--solver-time', type=float, default=180.0)
    ap.add_argument('--add-wang-limit', type=int, default=1000)
    ap.add_argument('--out', default='data/rep2_shared_factor/all5_rounds/result.json')
    args = ap.parse_args()
    out_path = Path(args.out); out_path.parent.mkdir(parents=True, exist_ok=True)

    prefix = [1, 2]
    prefix_set = set(prefix)
    candidates = [p for p in range(1, 512) if p not in prefix_set]
    cand_set = set(candidates)
    cand_idx = {p: i for i, p in enumerate(candidates)}
    target = 18
    T = build_matmul_tensor_f2()
    print('Loading LUT...')
    t0 = time.time()
    with open(args.lut, 'rb') as f:
        payload = pickle.load(f)
    lut = {int(k): int(v) for k, v in payload['lut'].items()}
    print(f'  lut={len(lut):,} load_sec={time.time()-t0:.1f}')
    print('Building stabilizer and initial constraints...')
    actions = make_actions()
    stab = [img for img in actions if {transform_mask(p, img) for p in prefix} == prefix_set]
    orbit_records, orbit_keys = expand_orbit_keys(args.tiers, args.tier, args.top, stab, lut)
    constraints, source_counts = collect_wang_constraints(lut, prefix_set, cand_set, cand_idx, args.initial_max_residual, orbit_keys)
    lower_rows = contraction_lower_data(prefix, candidates)

    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x{i}') for i in range(len(candidates))]
    model.Add(sum(x) == target)
    r1_all = all_rank1_set()
    r1_indices = [cand_idx[p] for p in candidates if p in r1_all]
    model.Add(sum(x[i] for i in r1_indices) <= 15)
    for c in constraints.values():
        model.Add(sum(x[i] for i in c['indices']) <= int(c['residual']))
    for rec in lower_rows:
        model.Add(sum(x[i] for i in rec['indices']) >= int(rec['required_from_candidates']))

    rc = simplify_ruling(all_ruling_triples(), prefix_set)
    ruling_counts = {'unit': 0, 'binary': 0, 'ternary': 0}
    for p in rc['unit']:
        if p in cand_idx:
            model.Add(x[cand_idx[p]] == 0); ruling_counts['unit'] += 1
    for a, b in rc['binary']:
        if a in cand_idx and b in cand_idx:
            model.Add(x[cand_idx[a]] + x[cand_idx[b]] <= 1); ruling_counts['binary'] += 1
    for a, b, c in rc['ternary']:
        if a in cand_idx and b in cand_idx and c in cand_idx:
            model.Add(x[cand_idx[a]] + x[cand_idx[b]] + x[cand_idx[c]] <= 2); ruling_counts['ternary'] += 1

    # Reified nonsaturation literals y_q: true iff count(q) >= rank(q)+1.
    nonsat_lits = {}
    def get_nonsat_lit(q, rk):
        q = int(q); rk = int(rk)
        if q in nonsat_lits:
            return nonsat_lits[q]
        prefix_cnt = sum(1 for p in prefix if ((q & p).bit_count() & 1))
        ci = [i for i, p in enumerate(candidates) if ((q & p).bit_count() & 1)]
        req_gt = rk + 1 - prefix_cnt
        y = model.NewBoolVar(f'nonsat_q{q}')
        if req_gt <= 0:
            model.Add(y == 1)
        elif req_gt > len(ci):
            model.Add(y == 0)
        else:
            expr = sum(x[i] for i in ci)
            model.Add(expr >= req_gt).OnlyEnforceIf(y)
            model.Add(expr <= req_gt - 1).OnlyEnforceIf(y.Not())
        nonsat_lits[q] = y
        return y

    rounds = []
    learned_zero_cuts = set()
    status_name = None
    for rnd in range(args.max_rounds):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = args.solver_time
        solver.parameters.num_workers = 8
        solver.parameters.random_seed = 9000 + rnd
        tsolve = time.time()
        status = solver.Solve(model)
        solve_sec = time.time() - tsolve
        status_name = {cp_model.OPTIMAL:'OPTIMAL', cp_model.FEASIBLE:'FEASIBLE', cp_model.INFEASIBLE:'INFEASIBLE', cp_model.MODEL_INVALID:'MODEL_INVALID', cp_model.UNKNOWN:'UNKNOWN'}.get(status, str(status))
        print(f'Round {rnd}: status={status_name} solve_sec={solve_sec:.1f} constraints={len(constraints)} zero_cuts={len(learned_zero_cuts)}')
        rec = {'round': rnd, 'status': status_name, 'solve_sec': round(solve_sec, 2), 'wang_constraint_count': len(constraints), 'zero_domain_cut_count': len(learned_zero_cuts)}
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rec['cp_model_stats'] = solver.ResponseStats()
            rounds.append(rec)
            break
        selected = [candidates[i] for i in range(len(candidates)) if solver.Value(x[i])]
        support = sorted(prefix + selected)
        rec['support'] = support
        rec['rank1_total'] = sum(1 for p in support if p in r1_all)
        print('  scanning full LUT...')
        scan = full_lut_scan(lut, set(support))
        rec['full_lut_violation_count'] = scan['violation_count']
        rec['full_lut_max_excess'] = scan['max_excess']
        rec['full_lut_type_top'] = scan['type_top'][:10]
        print('  saturated-domain analysis...')
        sat = analyze_fixed_A(f'round{rnd}', T, support, None)
        lin = sat['linear_membership']
        zero_terms = [t for t in sat['term_summaries'] if t['B_dim'] == 0 or t['C_dim'] == 0]
        rec['saturation'] = {
            'undersaturated_contraction_count': sat['undersaturated_contraction_count'],
            'saturated_contraction_count': sat['saturated_contraction_count'],
            'domain_hist': sat['term_domain_dims_hist'],
            'linear_passed': lin['necessary_linear_test_passed'],
            'linear_affine_dim': lin['affine_solution_dimension_if_consistent'],
            'zero_domain_terms': [{'term': int(t['term']), 'a': int(t['a']), 'B_dim': int(t['B_dim']), 'C_dim': int(t['C_dim']), 'saturated_contractions': int(t['saturated_contractions'])} for t in zero_terms],
        }
        if scan['violation_count'] == 0 and lin['necessary_linear_test_passed'] and not zero_terms:
            rec['candidate_status'] = 'PASSED_WANG_AND_SATURATION_LINEAR_NEEDS_RANKONE_SOLVE'
            rounds.append(rec)
            break

        added_wang = 0
        # Add most violated Wang rows first, bounded by add-wang-limit.
        examples = sorted(scan['violation_examples'], key=lambda v: (-int(v['excess']), -int(v['lb']), int(v['dim'])))[:args.add_wang_limit]
        for v in examples:
            key = int(v['key_hex'], 16)
            if add_wang_constraint(model, x, constraints, key, int(v['lb']), prefix_set, cand_set, cand_idx, f'round{rnd}_violated'):
                added_wang += 1
                source_counts['learned'] += 1
        rec['learned_wang_added'] = added_wang

        added_zero = 0
        if zero_terms:
            sat_by_term = saturated_records_by_term(T, support)
            for t in zero_terms:
                term_idx = int(t['term']); p = support[term_idx]
                side = 'B' if int(t['B_dim']) == 0 else 'C'
                cert = find_zero_subset(sat_by_term[term_idx], side, 9)
                qrs = tuple((int(r['q']), int(r['rank'])) for r in cert['records'])
                key = (int(p), side, qrs)
                if key in learned_zero_cuts:
                    continue
                lits = [get_nonsat_lit(q, rk) for q, rk in qrs]
                if p not in prefix_set:
                    lits.append(x[cand_idx[p]].Not())
                model.AddBoolOr(lits)
                learned_zero_cuts.add(key)
                added_zero += 1
            rec['learned_zero_domain_cuts_added'] = added_zero
        else:
            rec['learned_zero_domain_cuts_added'] = 0
            # If only the linear domain test fails, exclude the exact support to avoid repeats.
            if not lin['necessary_linear_test_passed']:
                lits = []
                for p in selected:
                    lits.append(x[cand_idx[p]].Not())
                for p in candidates:
                    if p not in selected:
                        lits.append(x[cand_idx[p]])
                model.AddBoolOr(lits)
                rec['learned_exact_support_nogood'] = True
        print(f"  viol={scan['violation_count']} linear={lin['necessary_linear_test_passed']} zero_terms={len(zero_terms)} added_wang={added_wang} added_zero={added_zero}")
        rounds.append(rec)

    result = {
        'schema': 'rep2_shared_factor_separation_v1',
        'field': 'F2',
        'meaning': 'Exploratory support-level separation combining Wang occupation, contraction lower bounds, and learned zero-domain shared-factor cuts. Not a formal lower bound without proof replay.',
        'prefix': prefix,
        'tier': args.tier,
        'top': args.top,
        'initial_max_residual': args.initial_max_residual,
        'initial_wang_constraints': len(constraints) - source_counts['learned'],
        'final_wang_constraints': len(constraints),
        'source_counts': source_counts,
        'contraction_lower_constraints': len(lower_rows),
        'ruling_counts': ruling_counts,
        'setwise_stabilizer_order': len(stab),
        'orbit_records': orbit_records,
        'final_status': status_name,
        'rounds': rounds,
        'learned_zero_domain_cut_count': len(learned_zero_cuts),
        'total_elapsed_sec': round(time.time() - t0, 2),
    }
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'out': str(out_path), 'final_status': status_name, 'rounds': len(rounds), 'final_wang_constraints': len(constraints), 'zero_cuts': len(learned_zero_cuts)}, sort_keys=True))


if __name__ == '__main__':
    main()
