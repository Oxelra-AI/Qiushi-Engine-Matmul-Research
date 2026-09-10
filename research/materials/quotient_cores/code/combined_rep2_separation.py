#!/usr/bin/env python3
r"""analysis: Combined rep2 separation with ALL known constraints.

Integrates:
  1. Wang upper constraints (base residual + orbit tier)
  2. Contraction lower bounds (w(q) >= rank L(q))
  3. Primal ruling-line clauses (A-support ruling exclusions)
  4. Dual ruling-line shared-factor constraints (294 implications)
  5. Iterative learning: Wang violation rows + zero-domain cuts

The dual ruling-line constraints encode: on each dual Segre ruling line
{Q1,Q2,Q3=Q1+Q2} where all three are rank-1 contractions,
w(Qj)=3 AND w(Qk)=3 => w(Ql)>=6 for each permutation.
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

from wang_capacity_lazy import make_actions, transform_key, transform_mask, unpack_basis
from ruling_line_transport import all_rank1_set, all_ruling_triples, simplify_ruling
from rep2_orbit_promotion_pilot import load_tier_keys, full_lut_scan, span_constraints_for_key
from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2, analyze_fixed_A
from zero_domain_certificates import saturated_records_by_term, find_zero_subset
from dual_ruling_shared_factor import rank1_contractions, all_dual_ruling_lines


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--tiers', default='data/corrected_strategy/rep2_orbit_promotion_tiers.json')
    ap.add_argument('--tier', choices=['none', 'all5', 'strong4plus', 'hit4plus'], default='all5')
    ap.add_argument('--top', type=int, default=None)
    ap.add_argument('--initial-max-residual', type=int, default=2)
    ap.add_argument('--max-rounds', type=int, default=10)
    ap.add_argument('--solver-time', type=float, default=180.0)
    ap.add_argument('--add-wang-limit', type=int, default=2000)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

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

    actions = make_actions()
    stab = [img for img in actions if {transform_mask(p, img) for p in prefix} == prefix_set]
    print(f'  stab={len(stab)}')

    # Expand orbit keys
    orbit_keys = set()
    if args.tier != 'none':
        _, tier_entries, tier_keys = load_tier_keys(Path(args.tiers), args.tier, args.top)
        for e, key in zip(tier_entries, tier_keys):
            rows = unpack_basis(key)
            expanded = {transform_key(rows, img) for img in stab}
            orbit_keys.update(expanded)
    print(f'  orbit_keys={len(orbit_keys):,}')

    # Collect Wang upper constraints
    constraints = {}
    source_counts = {'base_residual': 0, 'orbit': 0, 'both': 0, 'learned': 0}
    for key, lb in lut.items():
        is_orbit = key in orbit_keys
        parsed = span_constraints_for_key(int(key), int(lb), prefix_set, cand_set, cand_idx)
        if parsed is None:
            continue
        ci, residual, pts_len, dim, cap, prefix_occ = parsed
        is_base = residual <= args.initial_max_residual
        if is_base or is_orbit:
            constraints[int(key)] = {'indices': ci, 'residual': int(residual), 'lb': int(lb), 'source': 'base_or_orbit'}
            if is_base and is_orbit:
                source_counts['both'] += 1
            elif is_base:
                source_counts['base_residual'] += 1
            else:
                source_counts['orbit'] += 1

    # Contraction lower bounds
    lower_rows = []
    for q in range(1, 512):
        rk = mat_rank_f2(contraction_matrix(T, q))
        prefix_cnt = sum(1 for p in prefix if bin(q & p).count('1') % 2 == 1)
        ci = [i for i, p in enumerate(candidates) if bin(q & p).count('1') % 2 == 1]
        req = rk - prefix_cnt
        if req > 0:
            lower_rows.append((q, rk, ci, req))

    print(f'  wang_upper={len(constraints):,}  contraction_lower={len(lower_rows)}')

    # Build model
    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x{i}') for i in range(len(candidates))]
    model.Add(sum(x) == target)

    # Rank-1 structural bound
    r1_all = all_rank1_set()
    r1_indices = [cand_idx[p] for p in candidates if p in r1_all]
    model.Add(sum(x[i] for i in r1_indices) <= 15)

    # Wang upper
    for key, c in constraints.items():
        model.Add(sum(x[i] for i in c['indices']) <= int(c['residual']))

    # Contraction lower
    for q, rk, ci, req in lower_rows:
        model.Add(sum(x[i] for i in ci) >= req)

    # Primal ruling-line clauses
    rc = simplify_ruling(all_ruling_triples(), prefix_set)
    primal_counts = {'unit': 0, 'binary': 0, 'ternary': 0}
    for p in rc['unit']:
        if p in cand_idx:
            model.Add(x[cand_idx[p]] == 0)
            primal_counts['unit'] += 1
    for a, b in rc['binary']:
        if a in cand_idx and b in cand_idx:
            model.Add(x[cand_idx[a]] + x[cand_idx[b]] <= 1)
            primal_counts['binary'] += 1
    for a, b, c in rc['ternary']:
        if a in cand_idx and b in cand_idx and c in cand_idx:
            model.Add(x[cand_idx[a]] + x[cand_idx[b]] + x[cand_idx[c]] <= 2)
            primal_counts['ternary'] += 1

    # ---------- DUAL RULING-LINE SHARED-FACTOR CONSTRAINTS ----------
    r1_list = rank1_contractions()
    dual_lines = all_dual_ruling_lines(r1_list)
    print(f'  dual_ruling_lines={len(dual_lines)}')

    # Precompute evaluation data for rank-1 contractions
    r1_eval = {}
    for d in r1_list:
        q = d['q']
        pc = sum(1 for p in prefix if bin(q & p).count('1') % 2 == 1)
        ci = [i for i, cp in enumerate(candidates) if bin(q & cp).count('1') % 2 == 1]
        r1_eval[q] = {'prefix_count': pc, 'cand_indices': ci}

    sat_vars = {}
    def get_sat_var(q):
        if q in sat_vars:
            return sat_vars[q]
        info = r1_eval[q]
        pc = info['prefix_count']
        ci = info['cand_indices']
        threshold = 3 - pc
        if threshold < 0:
            y = model.NewConstant(0)
        elif threshold >= len(ci):
            y = model.NewConstant(1)
        else:
            y = model.NewBoolVar(f'sat_q{q}')
            expr = sum(x[i] for i in ci)
            model.Add(expr <= threshold).OnlyEnforceIf(y)
            model.Add(expr >= threshold + 1).OnlyEnforceIf(y.Not())
        sat_vars[q] = y
        return y

    dual_count = 0
    for tri in dual_lines:
        q1, q2, q3 = tri
        qs = [q1, q2, q3]
        for j in range(3):
            k = (j + 1) % 3
            l = (j + 2) % 3
            qj, qk, ql = qs[j], qs[k], qs[l]
            info_l = r1_eval[ql]
            pc_l = info_l['prefix_count']
            ci_l = info_l['cand_indices']
            req_from_cand = 6 - pc_l
            if req_from_cand > len(ci_l):
                model.AddBoolOr([get_sat_var(qj).Not(), get_sat_var(qk).Not()])
                dual_count += 1
            elif req_from_cand <= 0:
                pass
            else:
                model.Add(sum(x[i] for i in ci_l) >= req_from_cand).OnlyEnforceIf(
                    [get_sat_var(qj), get_sat_var(qk)])
                dual_count += 1
    print(f'  dual_ruling_constraints={dual_count}  sat_vars={len(sat_vars)}')

    # ---------- REIFIED NONSATURATION for zero-domain cuts ----------
    nonsat_lits = {}
    def get_nonsat_lit(q, rk):
        q = int(q); rk = int(rk)
        if q in nonsat_lits:
            return nonsat_lits[q]
        prefix_cnt = sum(1 for p in prefix if bin(q & p).count('1') % 2 == 1)
        ci = [i for i, p in enumerate(candidates) if bin(q & p).count('1') % 2 == 1]
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

    # ---------- ITERATIVE SEPARATION ----------
    learned_zero_cuts = set()
    rounds = []
    final_status = None

    for rnd in range(args.max_rounds):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = args.solver_time
        solver.parameters.num_workers = 8
        solver.parameters.random_seed = 4300 + rnd * 7
        tsolve = time.time()
        status = solver.Solve(model)
        solve_sec = time.time() - tsolve
        status_name = {
            cp_model.OPTIMAL: 'OPTIMAL', cp_model.FEASIBLE: 'FEASIBLE',
            cp_model.INFEASIBLE: 'INFEASIBLE', cp_model.MODEL_INVALID: 'MODEL_INVALID',
            cp_model.UNKNOWN: 'UNKNOWN'
        }.get(status, str(status))
        print(f'\nRound {rnd}: status={status_name} solve_sec={solve_sec:.1f} constraints={len(constraints)} zero_cuts={len(learned_zero_cuts)}')

        rec = {'round': rnd, 'status': status_name, 'solve_sec': round(solve_sec, 2),
               'wang_constraint_count': len(constraints), 'zero_domain_cut_count': len(learned_zero_cuts)}

        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rec['note'] = 'no solution found'
            rounds.append(rec)
            final_status = status_name
            break

        selected = [candidates[i] for i in range(len(candidates)) if solver.Value(x[i])]
        support = sorted(prefix + selected)
        rec['support'] = support
        rec['rank1_total'] = sum(1 for p in support if p in r1_all)

        # Full LUT scan
        scan = full_lut_scan(lut, set(support))
        rec['full_lut_violation_count'] = scan['violation_count']
        rec['full_lut_max_excess'] = scan['max_excess']

        # Saturated-domain analysis
        sat_result = analyze_fixed_A(f'rnd{rnd}', T, support, None)
        lin = sat_result['linear_membership']
        zero_terms = [t for t in sat_result['term_summaries'] if t['B_dim'] == 0 or t['C_dim'] == 0]
        rec['saturation'] = {
            'saturated_contraction_count': sat_result['saturated_contraction_count'],
            'undersaturated_contraction_count': sat_result['undersaturated_contraction_count'],
            'linear_passed': lin['necessary_linear_test_passed'],
            'linear_affine_dim': lin['affine_solution_dimension_if_consistent'],
            'domain_hist': sat_result['term_domain_dims_hist'],
            'zero_domain_terms': [{'term': int(t['term']), 'a': int(t['a']),
                                    'B_dim': int(t['B_dim']), 'C_dim': int(t['C_dim'])} for t in zero_terms],
        }

        if scan['violation_count'] == 0 and lin['necessary_linear_test_passed'] and not zero_terms:
            rec['candidate_status'] = 'FULL_WANG_AND_SATURATION_PASS_NEEDS_RANKONE_SOLVE'
            rounds.append(rec)
            final_status = 'CANDIDATE_FOUND'
            print(f'  *** CANDIDATE FOUND: Wang-admissible + linear-pass support ***')
            break

        # Learn Wang violation rows
        added_wang = 0
        violation_examples = sorted(scan.get('violation_examples', []),
                                     key=lambda v: (-int(v['excess']), -int(v['lb'])))[:args.add_wang_limit]
        for v in violation_examples:
            key = int(v['key_hex'], 16)
            if key in constraints:
                continue
            parsed = span_constraints_for_key(key, int(v['lb']), prefix_set, cand_set, cand_idx)
            if parsed is None:
                continue
            ci, residual, pts_len, dim, cap, prefix_occ = parsed
            model.Add(sum(x[i] for i in ci) <= int(residual))
            constraints[key] = {'indices': ci, 'residual': int(residual), 'lb': int(v['lb']), 'source': f'rnd{rnd}'}
            added_wang += 1
            source_counts['learned'] += 1
        rec['learned_wang_added'] = added_wang

        # Learn zero-domain cuts
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

        if not lin['necessary_linear_test_passed'] and not zero_terms:
            # Exclude exact support
            lits = [x[cand_idx[p]].Not() for p in selected] + [x[cand_idx[p]] for p in candidates if p not in set(selected) and p not in prefix_set]
            model.AddBoolOr(lits)
            rec['learned_exact_support_nogood'] = True

        print(f'  viol={scan["violation_count"]} linear={lin["necessary_linear_test_passed"]} zero_terms={len(zero_terms)} added_wang={added_wang} added_zero={added_zero}')
        rounds.append(rec)
        final_status = status_name

    result = {
        'schema': 'combined_rep2_separation_v1',
        'prefix': prefix,
        'tier': args.tier,
        'top': args.top,
        'initial_max_residual': args.initial_max_residual,
        'initial_wang_constraints': len(constraints) - source_counts['learned'],
        'final_wang_constraints': len(constraints),
        'primal_ruling_counts': primal_counts,
        'dual_ruling_constraints': dual_count,
        'source_counts': source_counts,
        'contraction_lower_constraints': len(lower_rows),
        'final_status': final_status,
        'total_rounds': len(rounds),
        'learned_zero_domain_cut_count': len(learned_zero_cuts),
        'rounds': rounds,
        'total_elapsed_sec': round(time.time() - t0, 2),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'\nSaved to {args.out}')
    print(json.dumps({'final_status': final_status, 'rounds': len(rounds), 'wang': len(constraints), 'zero_cuts': len(learned_zero_cuts)}, sort_keys=True))


if __name__ == '__main__':
    main()
