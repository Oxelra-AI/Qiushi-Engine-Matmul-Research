#!/usr/bin/env python3
r"""analysis: rep2 combined separation with saturated-transversal cuts.

This extends `combined_rep2_separation.py` by adding Rado independent-
transversal cuts when a solved support passes zero-domain and linear membership
but still cannot supply independent B or C factors for a saturated contraction.

A cut has the guarded form

    (some witness A-point is absent) OR (some source contraction is nonsaturated).

For the current implementation the source contractions for each term-domain are
all saturated contractions containing that term; this is sound but may be weaker
than a minimized certificate because it allows the solver to break any one of
many saturations.  The output records the full witness and source q list for
later minimization.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from wang_capacity_lazy import make_actions, transform_key, transform_mask, unpack_basis  # noqa: E402
from ruling_line_transport import all_rank1_set, all_ruling_triples, simplify_ruling  # noqa: E402
from rep2_orbit_promotion_pilot import load_tier_keys, full_lut_scan, span_constraints_for_key  # noqa: E402
from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2  # noqa: E402
from dual_ruling_shared_factor import rank1_contractions, all_dual_ruling_lines  # noqa: E402
from complete_core_and_transversal import saturation_domains, transversal_failures  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--tiers', default='data/corrected_strategy/rep2_orbit_promotion_tiers.json')
    ap.add_argument('--tier', choices=['none', 'all5', 'strong4plus', 'hit4plus'], default='all5')
    ap.add_argument('--top', type=int, default=None)
    ap.add_argument('--initial-max-residual', type=int, default=2)
    ap.add_argument('--max-rounds', type=int, default=4)
    ap.add_argument('--solver-time', type=float, default=240.0)
    ap.add_argument('--add-wang-limit', type=int, default=2000)
    ap.add_argument('--max-transversal-cuts', type=int, default=12)
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
    orbit_keys = set()
    if args.tier != 'none':
        _, tier_entries, tier_keys = load_tier_keys(Path(args.tiers), args.tier, args.top)
        for key in tier_keys:
            rows = unpack_basis(key)
            orbit_keys.update(transform_key(rows, img) for img in stab)
    print(f'  tier={args.tier} top={args.top} orbit_keys={len(orbit_keys):,}')

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

    lower_rows = []
    for q in range(1, 512):
        rk = mat_rank_f2(contraction_matrix(T, q))
        prefix_cnt = sum(1 for p in prefix if ((q & p).bit_count() & 1))
        ci = [i for i, p in enumerate(candidates) if ((q & p).bit_count() & 1)]
        req = rk - prefix_cnt
        if req > 0:
            lower_rows.append((q, rk, ci, req))
    print(f'  wang_upper={len(constraints):,} contraction_lower={len(lower_rows)}')

    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x{i}') for i in range(len(candidates))]
    model.Add(sum(x) == target)

    r1_all = all_rank1_set()
    r1_indices = [cand_idx[p] for p in candidates if p in r1_all]
    model.Add(sum(x[i] for i in r1_indices) <= 15)

    for c in constraints.values():
        model.Add(sum(x[i] for i in c['indices']) <= int(c['residual']))
    for q, rk, ci, req in lower_rows:
        model.Add(sum(x[i] for i in ci) >= int(req))

    rc = simplify_ruling(all_ruling_triples(), prefix_set)
    primal_counts = {'unit': 0, 'binary': 0, 'ternary': 0}
    for p in rc['unit']:
        if p in cand_idx:
            model.Add(x[cand_idx[p]] == 0); primal_counts['unit'] += 1
    for a, b in rc['binary']:
        if a in cand_idx and b in cand_idx:
            model.Add(x[cand_idx[a]] + x[cand_idx[b]] <= 1); primal_counts['binary'] += 1
    for a, b, c in rc['ternary']:
        if a in cand_idx and b in cand_idx and c in cand_idx:
            model.Add(x[cand_idx[a]] + x[cand_idx[b]] + x[cand_idx[c]] <= 2); primal_counts['ternary'] += 1

    # Reified saturation/nonsaturation literals for contraction weights.
    weight_cache = {}
    def eval_info(q):
        q = int(q)
        if q not in weight_cache:
            pc = sum(1 for p in prefix if ((q & p).bit_count() & 1))
            ci = [i for i, p in enumerate(candidates) if ((q & p).bit_count() & 1)]
            weight_cache[q] = (pc, ci)
        return weight_cache[q]

    sat_vars = {}
    def get_sat_var(q, rk):
        q = int(q); rk = int(rk)
        key = (q, rk)
        if key in sat_vars:
            return sat_vars[key]
        pc, ci = eval_info(q)
        threshold = rk - pc
        if threshold < 0 or threshold > len(ci):
            y = model.NewConstant(0)
        else:
            y = model.NewBoolVar(f'sat_q{q}_r{rk}')
            expr = sum(x[i] for i in ci)
            model.Add(expr <= threshold).OnlyEnforceIf(y)
            model.Add(expr >= threshold + 1).OnlyEnforceIf(y.Not())
        sat_vars[key] = y
        return y

    nonsat_vars = {}
    def get_nonsat_lit(q, rk):
        q = int(q); rk = int(rk)
        key = (q, rk)
        if key in nonsat_vars:
            return nonsat_vars[key]
        pc, ci = eval_info(q)
        req_gt = rk + 1 - pc
        if req_gt <= 0:
            y = model.NewConstant(1)
        elif req_gt > len(ci):
            y = model.NewConstant(0)
        else:
            y = model.NewBoolVar(f'nonsat_q{q}_r{rk}')
            expr = sum(x[i] for i in ci)
            model.Add(expr >= req_gt).OnlyEnforceIf(y)
            model.Add(expr <= req_gt - 1).OnlyEnforceIf(y.Not())
        nonsat_vars[key] = y
        return y

    # Dual ruling constraints for rank-one contractions: saturation rank is 3.
    r1_list = rank1_contractions()
    r1_qs = {d['q'] for d in r1_list}
    r1_eval = {q: eval_info(q) for q in r1_qs}
    dual_count = 0
    for tri in all_dual_ruling_lines(r1_list):
        qs = list(tri)
        for j in range(3):
            qj, qk, ql = qs[j], qs[(j + 1) % 3], qs[(j + 2) % 3]
            pc_l, ci_l = eval_info(ql)
            req = 6 - pc_l
            if req > len(ci_l):
                model.AddBoolOr([get_sat_var(qj, 3).Not(), get_sat_var(qk, 3).Not()]); dual_count += 1
            elif req > 0:
                model.Add(sum(x[i] for i in ci_l) >= req).OnlyEnforceIf([get_sat_var(qj, 3), get_sat_var(qk, 3)]); dual_count += 1
    print(f'  dual_ruling_constraints={dual_count}')

    learned_transversal_cuts = []
    learned_exact_nogoods = 0
    rounds = []
    final_status = None

    for rnd in range(args.max_rounds):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(args.solver_time)
        solver.parameters.num_search_workers = 8
        solver.parameters.random_seed = 4440 + 19 * rnd
        tsolve = time.time()
        status = solver.Solve(model)
        solve_sec = time.time() - tsolve
        status_name = {cp_model.OPTIMAL: 'OPTIMAL', cp_model.FEASIBLE: 'FEASIBLE', cp_model.INFEASIBLE: 'INFEASIBLE', cp_model.MODEL_INVALID: 'MODEL_INVALID', cp_model.UNKNOWN: 'UNKNOWN'}.get(status, str(status))
        print(f'\nRound {rnd}: status={status_name} solve_sec={solve_sec:.1f} wang={len(constraints)} trans_cuts={len(learned_transversal_cuts)}')
        rec = {'round': rnd, 'status': status_name, 'solve_sec': round(solve_sec, 2), 'wang_constraint_count': len(constraints), 'transversal_cut_count': len(learned_transversal_cuts)}
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rec['note'] = 'no solution found'
            rounds.append(rec); final_status = status_name; break

        selected = [candidates[i] for i in range(len(candidates)) if solver.Value(x[i])]
        support = sorted(prefix + selected)
        rec['support'] = support
        rec['rank1_total'] = sum(1 for p in support if p in r1_all)

        scan = full_lut_scan(lut, set(support))
        rec['full_lut_violation_count'] = scan['violation_count']
        rec['full_lut_max_excess'] = scan['max_excess']

        sat = saturation_domains(T, support)
        lin = sat['summary']['linear_membership']
        trans = transversal_failures(sat['sat_records'], sat['B_domains'], sat['C_domains'], 9, 9, max_report=60)
        zero_terms = sat['summary']['zero_domain_terms']
        rec['saturation'] = {
            'saturated_contraction_count': sat['summary']['saturated_contraction_count'],
            'undersaturated_contraction_count': sat['summary']['undersaturated_contraction_count'],
            'zero_domain_term_count': len(zero_terms),
            'linear_passed': lin['necessary_linear_test_passed'],
            'linear_affine_dim': lin['affine_solution_dimension_if_consistent'],
            'domain_hist': sat['summary']['term_domain_dims_hist'],
            'transversal_failure_count_reported': trans['failure_count_reported'],
            'transversal_witnesses_head': trans['failures_head'][:12],
        }

        if scan['violation_count'] == 0 and lin['necessary_linear_test_passed'] and len(zero_terms) == 0 and trans['failure_count_reported'] == 0:
            rec['candidate_status'] = 'FULL_WANG_AND_SATURATION_TRANSVERSAL_PASS_NEEDS_RANKONE_SOLVE'
            rounds.append(rec); final_status = 'CANDIDATE_FOUND'
            print('  *** CANDIDATE support passes complete current fixed-A tests ***')
            break

        added_wang = 0
        for v in sorted(scan.get('violation_examples', []), key=lambda z: (-int(z['excess']), -int(z['lb'])))[:args.add_wang_limit]:
            key = int(v['key_hex'], 16)
            if key in constraints:
                continue
            parsed = span_constraints_for_key(key, int(v['lb']), prefix_set, cand_set, cand_idx)
            if parsed is None:
                continue
            ci, residual, pts_len, dim, cap, prefix_occ = parsed
            model.Add(sum(x[i] for i in ci) <= int(residual))
            constraints[key] = {'indices': ci, 'residual': int(residual), 'lb': int(v['lb']), 'source': f'rnd{rnd}'}
            added_wang += 1; source_counts['learned'] += 1
        rec['learned_wang_added'] = added_wang

        added_trans = 0
        # Add guarded transversality cuts for the first few witnesses.  We use all
        # currently saturated contractions containing each subset term as sources.
        # This is sound but intentionally not minimal.
        for f in trans['failures_head'][:args.max_transversal_cuts]:
            subset_terms = [int(s) for s in f['subset_terms']]
            subset_points = [int(support[s]) for s in subset_terms]
            source_qr = set()
            for s in subset_terms:
                for rec_sat in sat['sat_records']:
                    if s in rec_sat['terms']:
                        source_qr.add((int(rec_sat['q']), int(rec_sat['rank'])))
            cut_key = (tuple(sorted(subset_points)), f['side'], tuple(sorted(source_qr)))
            if cut_key in {tuple(c['key_tuple']) for c in learned_transversal_cuts}:
                continue
            lits = []
            for p in set(subset_points):
                if p in prefix_set:
                    # fixed prefix term is always present, no absence literal.
                    continue
                lits.append(x[cand_idx[p]].Not())
            for q, rk in sorted(source_qr):
                lits.append(get_nonsat_lit(q, rk))
            if lits:
                model.AddBoolOr(lits)
                learned_transversal_cuts.append({
                    'key_tuple': [list(sorted(subset_points)), f['side'], [[q, rk] for q, rk in sorted(source_qr)]],
                    'round': rnd,
                    'q_star': int(f['q']),
                    'rank_star': int(f['rank']),
                    'side': f['side'],
                    'subset_terms': subset_terms,
                    'subset_points': subset_points,
                    'subset_size': int(f['subset_size']),
                    'sum_domain_dim': int(f['sum_domain_dim']),
                    'source_qr_count': len(source_qr),
                })
                added_trans += 1
        rec['learned_transversal_cuts_added'] = added_trans

        # Linear failure without compact support cut: exclude this exact selected set.
        if (not lin['necessary_linear_test_passed']) and len(zero_terms) == 0 and trans['failure_count_reported'] == 0:
            lits = [x[cand_idx[p]].Not() for p in selected] + [x[cand_idx[p]] for p in candidates if p not in set(selected) and p not in prefix_set]
            model.AddBoolOr(lits)
            learned_exact_nogoods += 1
            rec['learned_exact_support_nogood'] = True

        print(f'  viol={scan["violation_count"]} zero={len(zero_terms)} linear={lin["necessary_linear_test_passed"]} trans={trans["failure_count_reported"]} added_wang={added_wang} added_trans={added_trans}')
        rounds.append(rec); final_status = status_name

    result = {
        'schema': 'rep2_combined_transversal_sep_v1',
        'field': 'F2',
        'prefix': prefix,
        'prefix_semantics': 'The model fixes prefix points 1 and 2 and selects 18 additional candidate points; support records are the complete 20-term A-list.',
        'tier': args.tier,
        'top': args.top,
        'initial_max_residual': args.initial_max_residual,
        'final_status': final_status,
        'total_rounds': len(rounds),
        'initial_wang_constraints': len(constraints) - source_counts['learned'],
        'final_wang_constraints': len(constraints),
        'source_counts': source_counts,
        'contraction_lower_constraints': len(lower_rows),
        'primal_ruling_counts': primal_counts,
        'dual_ruling_constraints': dual_count,
        'learned_transversal_cut_count': len(learned_transversal_cuts),
        'learned_transversal_cuts_head': learned_transversal_cuts[:40],
        'learned_exact_nogoods': learned_exact_nogoods,
        'rounds': rounds,
        'total_elapsed_sec': round(time.time() - t0, 2),
        'scope': 'Exploratory exact-support separation. SAT/UNKNOWN are not proof; guarded transversality cuts are candidate-derived necessary conditions whose source contractions should be minimized before proof conversion.',
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'\nSaved to {args.out}')
    print(json.dumps({'final_status': final_status, 'rounds': len(rounds), 'wang': len(constraints), 'trans_cuts': len(learned_transversal_cuts)}, sort_keys=True))


if __name__ == '__main__':
    main()
