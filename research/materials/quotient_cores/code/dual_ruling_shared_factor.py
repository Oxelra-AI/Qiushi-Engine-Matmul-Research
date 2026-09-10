#!/usr/bin/env python3
r"""analysis: dual ruling-line shared-factor constraints for T<3,3,3> over F2.

Mathematical basis
------------------
For the matrix multiplication tensor T = sum_{i,j,k} e_ij tensor e_jk tensor e_ki,
a contraction by Q in the A-dual space gives L(Q), a B-by-C matrix.  When Q = uv^T
(rank 1 as a 3x3 matrix), L(Q) = Q^T tensor I_3, and:

    col(L(Q))  = <v> tensor F2^3      (dimension 3)
    row(L(Q))  = <u> tensor F2^3      (dimension 3)

Two distinct rank-1 contractions Q1 = u1 v1^T, Q2 = u2 v2^T:
  - u1 != u2 => row spaces disjoint => C-factors of shared terms forced to 0
  - v1 != v2 => col spaces disjoint => B-factors of shared terms forced to 0

Since Q1 != Q2 as projective points implies u1 != u2 or v1 != v2 (or both),
any two distinct saturated rank-1 contractions have disjoint participating term sets.

DUAL RULING LINE: three rank-1 contractions {Q1, Q2, Q3=Q1+Q2} sharing one
Segre factor (same u or same v).  Q1+Q2 is rank-1 only in this case.
The shared-factor constraint on such a triple is:

    w(Q_j) = 3 AND w(Q_k) = 3  =>  w(Q_l) = 6   for each permutation

where w(Q) = #{s : Q(a_s) = 1} is the contraction weight.  Since the
contraction lower bound gives w(Q) >= rank L(Q) = 3 for rank-1 Q, this
forces the third member above its lower bound.

For non-ruling-line pairs, Q1+Q2 has rank 2, lower bound 6, so the
forced weight 6 is already implied.  Ruling lines are the unique source
of new information from this mechanism.

There are exactly 98 dual ruling lines (7 row-rulings x 7 lines/ruling +
7 column-rulings x 7 lines/ruling = 98).

This script:
 1. Enumerates all 49 rank-1 contractions and 98 dual ruling lines.
 2. Validates constraints on cn122 mod 2 (must be satisfied).
 3. Quantifies how many ruling-line constraints are active (restrictive)
    for various support sets.
 4. Builds a CP-SAT model for rep2 with these constraints added.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from itertools import combinations

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))


# ---------- GF(2) helpers ----------

def mat_rank1_uv(q: int) -> tuple[int, int] | None:
    """For a 9-bit mask encoding a 3x3 matrix in row-major order,
    return (u,v) as 3-bit masks if the matrix has rank 1, else None."""
    rows_3 = [(q >> (3 * i)) & 7 for i in range(3)]
    nonzero = [(i, r) for i, r in enumerate(rows_3) if r]
    if not nonzero:
        return None
    # All nonzero rows must be equal (over F2, rank 1 means all rows
    # are the same nonzero vector or zero).
    v = nonzero[0][1]
    for _, r in nonzero[1:]:
        if r != v:
            return None
    u = 0
    for i, r in nonzero:
        u |= 1 << i
    return (u, v)


def rank1_contractions() -> list[dict]:
    """Return all 49 rank-1 projective points in F2^{3x3}."""
    seen = set()
    result = []
    for q in range(1, 512):
        uv = mat_rank1_uv(q)
        if uv is None:
            continue
        u, v = uv
        # Canonical representative: smallest q in the projective class
        # (over F2, rank-1 uv^T is unique for given u,v)
        if q not in seen:
            seen.add(q)
            result.append({'q': q, 'u': u, 'v': v})
    return result


def all_dual_ruling_lines(r1_list: list[dict]) -> list[tuple[int, int, int]]:
    """Enumerate all 98 dual ruling lines.
    A ruling line has three rank-1 points sharing u or v."""
    q_set = {d['q'] for d in r1_list}
    q_to_uv = {d['q']: (d['u'], d['v']) for d in r1_list}
    lines = set()
    for qa, qb in combinations(sorted(q_set), 2):
        qc = qa ^ qb
        if qc in q_set and qc != 0:
            tri = tuple(sorted([qa, qb, qc]))
            lines.add(tri)
    return sorted(lines)


def contraction_weight(q: int, support: list[int]) -> int:
    return sum(1 for a in support if bin(q & a).count('1') % 2 == 1)


def contraction_term_set(q: int, support: list[int]) -> list[int]:
    return [i for i, a in enumerate(support) if bin(q & a).count('1') % 2 == 1]


# ---------- Validation on cn122 ----------

def load_cn122_support_f2() -> list[int]:
    qmm_path = Path('data/cn122_3x3_r23_repro/scheme.qmm')
    A_cols = []
    current_u = None
    for line in qmm_path.read_text().splitlines():
        parts = line.split()
        if parts and parts[0] == 'u':
            vals = [int(x) % 2 for x in parts[1:]]
            mask = 0
            for i, b in enumerate(vals):
                mask |= b << i
            A_cols.append(mask)
    return A_cols


def validate_cn122(r1_list, lines):
    """Check that cn122 mod 2 satisfies all dual ruling-line constraints."""
    A_cols = load_cn122_support_f2()
    support = A_cols
    n = len(support)
    print(f"cn122 support: {n} terms")

    # Compute all weights
    weights = {}
    for d in r1_list:
        q = d['q']
        weights[q] = contraction_weight(q, support)

    # Check contraction lower bounds
    violated_lower = 0
    for d in r1_list:
        q = d['q']
        if weights[q] < 3:
            violated_lower += 1
    print(f"  rank-1 contraction lower bound violations: {violated_lower}")

    # Check ruling-line constraints
    violated_ruling = 0
    active_lines = 0
    for tri in lines:
        ws = [weights[q] for q in tri]
        # For each pair: if both are exactly 3, third must be exactly 6
        ok = True
        active = False
        for j in range(3):
            k = (j + 1) % 3
            l = (j + 2) % 3
            if ws[j] == 3 and ws[k] == 3:
                if ws[l] != 6:
                    ok = False
                active = True
        if not ok:
            violated_ruling += 1
        if active:
            active_lines += 1
    print(f"  ruling-line constraint violations: {violated_ruling}")
    print(f"  active ruling lines (at least two w=3): {active_lines}")

    # Weight distribution on rank-1 contractions
    from collections import Counter
    wdist = Counter(weights.values())
    print(f"  rank-1 weight distribution: {dict(sorted(wdist.items()))}")

    # Pairwise overlap analysis for saturated rank-1
    sat_qs = [d['q'] for d in r1_list if weights[d['q']] == 3]
    print(f"  saturated rank-1 contractions (w=3): {len(sat_qs)}")
    if sat_qs:
        max_overlap = 0
        for qa, qb in combinations(sat_qs, 2):
            ov = sum(1 for a in support if (bin(qa & a).count('1') % 2 == 1)
                     and (bin(qb & a).count('1') % 2 == 1))
            if ov > max_overlap:
                max_overlap = ov
        print(f"  max pairwise term overlap among saturated: {max_overlap}")

    return violated_ruling == 0


# ---------- Support-level constraint analysis ----------

def analyze_support(label, support, r1_list, lines, verbose=True):
    """Analyze dual ruling-line constraints for a given support."""
    weights = {d['q']: contraction_weight(d['q'], support) for d in r1_list}

    from collections import Counter
    wdist = Counter(weights.values())

    # Count active and violated ruling constraints
    violated = 0
    active = 0
    forced_weight_increases = 0
    for tri in lines:
        ws = [weights[q] for q in tri]
        line_active = False
        for j in range(3):
            k = (j + 1) % 3
            l = (j + 2) % 3
            if ws[j] == 3 and ws[k] == 3:
                line_active = True
                if ws[l] < 6:
                    violated += 1
                    forced_weight_increases += 1
        if line_active:
            active += 1

    # Count which rank-1 pairs with overlap are both saturated
    sat_qs = [d['q'] for d in r1_list if weights[d['q']] == 3]
    pair_overlaps = 0
    for qa, qb in combinations(sat_qs, 2):
        ov = sum(1 for a in support if (bin(qa & a).count('1') % 2 == 1)
                 and (bin(qb & a).count('1') % 2 == 1))
        if ov > 0:
            pair_overlaps += 1

    rec = {
        'label': label,
        'support_size': len(support),
        'rank1_weight_dist': dict(sorted(wdist.items())),
        'saturated_count': len(sat_qs),
        'active_ruling_lines': active,
        'violated_ruling_lines': violated,
        'forced_weight_increases': forced_weight_increases,
        'sat_pair_with_overlap': pair_overlaps,
    }

    if verbose:
        print(f"\n=== {label} ===")
        print(f"  support size: {len(support)}")
        print(f"  rank-1 weight dist: {rec['rank1_weight_dist']}")
        print(f"  saturated: {len(sat_qs)}")
        print(f"  active ruling lines: {active}")
        print(f"  VIOLATED ruling lines: {violated}")
        print(f"  sat pairs with overlap: {pair_overlaps}")

    return rec


# ---------- CP-SAT model with dual ruling-line constraints ----------

def build_rep2_model_with_dual_ruling(
    lut_path, tiers_path, tier, top, initial_max_residual,
    r1_list, lines, solver_time, out_path
):
    """Build rep2 CP-SAT model with Wang + contraction lower + dual ruling."""
    import pickle
    from wang_capacity_lazy import make_actions, transform_key, transform_mask, unpack_basis
    from ruling_line_transport import all_rank1_set, all_ruling_triples, simplify_ruling
    from rep2_orbit_promotion_pilot import load_tier_keys, full_lut_scan, span_constraints_for_key
    from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2

    prefix = [1, 2]
    prefix_set = set(prefix)
    candidates = [p for p in range(1, 512) if p not in prefix_set]
    cand_set = set(candidates)
    cand_idx = {p: i for i, p in enumerate(candidates)}
    target = 18

    T = build_matmul_tensor_f2()

    print('Loading LUT...')
    t0 = time.time()
    with open(lut_path, 'rb') as f:
        payload = pickle.load(f)
    lut = {int(k): int(v) for k, v in payload['lut'].items()}
    print(f'  lut={len(lut):,} load_sec={time.time()-t0:.1f}')

    # Build stabilizer and Wang constraints
    actions = make_actions()
    stab = [img for img in actions if {transform_mask(p, img) for p in prefix} == prefix_set]
    print(f'  setwise_stab={len(stab)}')

    # Expand orbit keys
    orbit_keys = set()
    if tier != 'none':
        _, tier_entries, tier_keys = load_tier_keys(Path(tiers_path), tier, top)
        for e, key in zip(tier_entries, tier_keys):
            rows = unpack_basis(key)
            expanded = {transform_key(rows, img) for img in stab}
            orbit_keys.update(expanded)
    print(f'  orbit_keys={len(orbit_keys):,}')

    # Build Wang upper constraints
    wang_constraints = {}
    for key, lb in lut.items():
        is_orbit = key in orbit_keys
        parsed = span_constraints_for_key(int(key), int(lb), prefix_set, cand_set, cand_idx)
        if parsed is None:
            continue
        ci, residual, pts_len, dim, cap, prefix_occ = parsed
        is_base = residual <= initial_max_residual
        if is_base or is_orbit:
            wang_constraints[int(key)] = (ci, int(residual))

    # Contraction lower bounds
    lower_rows = []
    for q in range(1, 512):
        rk = mat_rank_f2(contraction_matrix(T, q))
        prefix_cnt = sum(1 for p in prefix if bin(q & p).count('1') % 2 == 1)
        ci = [i for i, p in enumerate(candidates) if bin(q & p).count('1') % 2 == 1]
        req = rk - prefix_cnt
        if req > 0:
            lower_rows.append((q, rk, ci, req))

    print(f'  wang_upper={len(wang_constraints):,}  contraction_lower={len(lower_rows)}')

    # Build CP-SAT model
    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x{i}') for i in range(len(candidates))]
    model.Add(sum(x) == target)

    # Rank-1 structural bound
    r1_all = all_rank1_set()
    r1_indices = [cand_idx[p] for p in candidates if p in r1_all]
    model.Add(sum(x[i] for i in r1_indices) <= 15)

    # Wang upper
    for key, (ci, res) in wang_constraints.items():
        model.Add(sum(x[i] for i in ci) <= res)

    # Contraction lower
    for q, rk, ci, req in lower_rows:
        model.Add(sum(x[i] for i in ci) >= req)

    # Primal ruling-line clauses
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

    # ---------- DUAL RULING-LINE SHARED-FACTOR CONSTRAINTS ----------
    # For each dual ruling line {Q1, Q2, Q3=Q1+Q2}:
    #   w(Qj) = prefix_cnt_j + sum(x[i] for i in eval_j)
    #   Constraint: w(Qj)=3 AND w(Qk)=3 => w(Ql)>=6 (for each permutation)
    #
    # We reify sat_q: True iff w(q) <= 3 (equivalently w(q) = 3 given lower bound)

    # Precompute evaluation indices and prefix counts for rank-1 contractions
    r1_eval = {}
    for d in r1_list:
        q = d['q']
        pc = sum(1 for p in prefix if bin(q & p).count('1') % 2 == 1)
        ci = [i for i, p in enumerate(candidates) if bin(q & p).count('1') % 2 == 1]
        r1_eval[q] = {'prefix_count': pc, 'cand_indices': ci}

    # Reified saturation indicators
    sat_vars = {}
    def get_sat_var(q):
        if q in sat_vars:
            return sat_vars[q]
        info = r1_eval[q]
        pc = info['prefix_count']
        ci = info['cand_indices']
        # w(q) = pc + sum(x[i] for i in ci)
        # sat_q = 1 iff w(q) <= 3, i.e. sum(x[i] for i in ci) <= 3 - pc
        threshold = 3 - pc
        if threshold < 0:
            # Already oversaturated from prefix alone
            y = model.NewConstant(0)
            sat_vars[q] = y
            return y
        if threshold >= len(ci):
            # Always saturated (impossible to exceed if all selected)
            # Actually: sat = (sum <= threshold), if threshold >= |ci|, always true
            y = model.NewConstant(1)
            sat_vars[q] = y
            return y
        y = model.NewBoolVar(f'sat_q{q}')
        expr = sum(x[i] for i in ci)
        # y = 1 iff expr <= threshold
        model.Add(expr <= threshold).OnlyEnforceIf(y)
        model.Add(expr >= threshold + 1).OnlyEnforceIf(y.Not())
        sat_vars[q] = y
        return y

    dual_ruling_constraints = 0
    for tri in lines:
        q1, q2, q3 = tri
        qs = [q1, q2, q3]
        for j in range(3):
            k = (j + 1) % 3
            l = (j + 2) % 3
            qj, qk, ql = qs[j], qs[k], qs[l]
            # Constraint: sat(qj) AND sat(qk) => w(ql) >= 6
            info_l = r1_eval[ql]
            pc_l = info_l['prefix_count']
            ci_l = info_l['cand_indices']
            req_from_cand = 6 - pc_l
            if req_from_cand > len(ci_l):
                # w(ql) can never reach 6 => sat(qj) AND sat(qk) impossible
                model.AddBoolOr([get_sat_var(qj).Not(), get_sat_var(qk).Not()])
                dual_ruling_constraints += 1
            elif req_from_cand <= 0:
                # w(ql) >= 6 always from prefix alone: constraint is trivially satisfied
                pass
            else:
                yj = get_sat_var(qj)
                yk = get_sat_var(qk)
                # sat(qj) AND sat(qk) => sum(x[ci_l]) >= req_from_cand
                # Rewrite as: NOT sat(qj) OR NOT sat(qk) OR sum(ci_l) >= req_from_cand
                # Use indicator: model.Add(sum >= req).OnlyEnforceIf([yj, yk])
                model.Add(sum(x[i] for i in ci_l) >= req_from_cand).OnlyEnforceIf([yj, yk])
                dual_ruling_constraints += 1

    print(f'  dual_ruling_constraints={dual_ruling_constraints}')
    print(f'  sat_vars={len(sat_vars)}')

    # Solve
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = solver_time
    solver.parameters.num_workers = 8
    solver.parameters.random_seed = 4300
    tsolve = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - tsolve
    status_name = {
        cp_model.OPTIMAL: 'OPTIMAL', cp_model.FEASIBLE: 'FEASIBLE',
        cp_model.INFEASIBLE: 'INFEASIBLE', cp_model.MODEL_INVALID: 'MODEL_INVALID',
        cp_model.UNKNOWN: 'UNKNOWN'
    }.get(status, str(status))
    print(f'\nSolver: status={status_name} solve_sec={solve_sec:.1f}')

    result = {
        'schema': 'dual_ruling_shared_factor_v1',
        'field': 'F2',
        'prefix': prefix,
        'tier': tier,
        'top': top,
        'initial_max_residual': initial_max_residual,
        'wang_upper_constraints': len(wang_constraints),
        'contraction_lower_constraints': len(lower_rows),
        'primal_ruling_counts': ruling_counts,
        'dual_ruling_constraints': dual_ruling_constraints,
        'sat_indicator_vars': len(sat_vars),
        'status': status_name,
        'solve_sec': round(solve_sec, 2),
    }

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        selected = [candidates[i] for i in range(len(candidates)) if solver.Value(x[i])]
        support = sorted(prefix + selected)
        result['support'] = support
        result['rank1_total'] = sum(1 for p in support if p in r1_all)

        # Scan full LUT
        scan = full_lut_scan(lut, set(support))
        result['full_lut_violations'] = scan['violation_count']
        result['full_lut_max_excess'] = scan['max_excess']

        # Check dual ruling lines for this support
        analysis = analyze_support('returned_support', support, r1_list, lines, verbose=True)
        result['dual_ruling_analysis'] = analysis

    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'\nSaved to {out_path}')
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', choices=['validate', 'analyze-analysis', 'rep2-cpsat'], default='validate')
    ap.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--tiers', default='data/corrected_strategy/rep2_orbit_promotion_tiers.json')
    ap.add_argument('--tier', choices=['none', 'all5', 'strong4plus', 'hit4plus'], default='all5')
    ap.add_argument('--top', type=int, default=None)
    ap.add_argument('--initial-max-residual', type=int, default=2)
    ap.add_argument('--solver-time', type=float, default=300.0)
    ap.add_argument('--outdir', type=Path, default=Path('data/dual_ruling'))
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)

    # analysis: enumerate dual Segre structure
    r1_list = rank1_contractions()
    print(f'Rank-1 contractions: {len(r1_list)}')
    assert len(r1_list) == 49, f'expected 49, got {len(r1_list)}'

    lines = all_dual_ruling_lines(r1_list)
    print(f'Dual ruling lines: {len(lines)}')
    assert len(lines) == 98, f'expected 98, got {len(lines)}'

    # Verify ruling-line structure: each should share u or v
    q_to_uv = {d['q']: (d['u'], d['v']) for d in r1_list}
    row_rulings = 0
    col_rulings = 0
    for tri in lines:
        uvs = [q_to_uv[q] for q in tri]
        us = {uv[0] for uv in uvs}
        vs = {uv[1] for uv in uvs}
        if len(us) == 1:
            col_rulings += 1
        elif len(vs) == 1:
            row_rulings += 1
        else:
            raise RuntimeError(f'ruling line {tri} shares neither u nor v!')
    print(f'  row rulings (shared v): {row_rulings}')
    print(f'  col rulings (shared u): {col_rulings}')

    # Save dual Segre structure
    segre = {
        'rank1_contractions': r1_list,
        'dual_ruling_lines': [list(t) for t in lines],
        'row_rulings': row_rulings,
        'col_rulings': col_rulings,
    }
    (args.outdir / 'dual_segre_structure.json').write_text(
        json.dumps(segre, indent=2, sort_keys=True) + '\n')

    if args.mode == 'validate':
        print('\n--- cn122 validation ---')
        ok = validate_cn122(r1_list, lines)
        print(f'cn122 validation: {"PASS" if ok else "FAIL"}')

        # Also validate all 5 analysis rep2 supports
        path = Path('data/rep2_rankaware/result.json')
        if path.exists():
            analysis = json.loads(path.read_text())
            print('\n--- analysis rep2 support analysis ---')
            records = []
            for rnd in analysis.get('round_log', []):
                if rnd.get('selected_points'):
                    support = sorted(analysis['prefix'] + rnd['selected_points'])
                    rec = analyze_support(
                        f'round{rnd["round"]}', support, r1_list, lines)
                    records.append(rec)
            if records:
                (args.outdir / 'rep2_dual_ruling_analysis.json').write_text(
                    json.dumps(records, indent=2, sort_keys=True) + '\n')

        # Validate analysis contraction-lower supports
        for name in ['none', 'all5']:
            p = Path(f'data/rep2_contraction_lower/{name}/result.json')
            if p.exists():
                d = json.loads(p.read_text())
                if 'support' in d:
                    rec = analyze_support(
                        f'contraction_lower_{name}', d['support'], r1_list, lines)

        summary = {'schema': 'dual_ruling_validation_v1', 'cn122_valid': ok,
                    'rank1_count': len(r1_list), 'ruling_line_count': len(lines)}
        (args.outdir / 'validation_summary.json').write_text(
            json.dumps(summary, indent=2, sort_keys=True) + '\n')

    elif args.mode == 'rep2-cpsat':
        out_path = args.outdir / f'rep2_cpsat_{args.tier}.json'
        build_rep2_model_with_dual_ruling(
            args.lut, args.tiers, args.tier, args.top,
            args.initial_max_residual, r1_list, lines,
            args.solver_time, out_path)


if __name__ == '__main__':
    main()
