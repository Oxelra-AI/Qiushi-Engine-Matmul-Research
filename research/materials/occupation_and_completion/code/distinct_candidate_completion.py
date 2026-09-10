#!/usr/bin/env python3
"""analysis: inspect best distinct E11-core A-supports and attempt fixed-A completion.

After the repeated projected-A branch is excluded, the E11 rank-19 core route is
concentrated on distinct A-supports.  This script rescans selected low-Wang-
violation supports from analysis, applies the fixed-A saturated-domain tests,
and formulates the linear/rank-one completion problem for B/C factors.  It is
primarily an exact candidate analysis tool; a solution would be a rank-19 core
algorithm over F2, while infeasibility for sampled supports is not a family proof.
"""
from __future__ import annotations
import argparse, json, sys, time
from collections import Counter
from pathlib import Path

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import (
    ROOT, build_core_constraints, complete_core_wang_scan, saturation_domains, transversal_failures
)
from candidate_source_qcut_scan import eval_candidate_sources
from fixed_A_rankone_solver import solve_fixed_A_completion
from quotient_rank_cuts import build_contractions, point_mask_for_q

OUTDIR = ROOT / 'workspace/data/repeat_branch_certificate'


def load_candidates():
    cands = []
    # analysis pilot and 50r separator rounds.
    for path in [
        ROOT / 'workspace/data/unconditional_qcuts/fresh_uncond_sep_10r.json',
        ROOT / 'workspace/data/unconditional_qcuts/fresh_uncond_sep_50r.json',
        ROOT / 'workspace/data/core_complete_transversal/core_e11_saturation_v3_complete_long.json',
    ]:
        if not path.exists():
            continue
        d = json.loads(path.read_text())
        for r in d.get('rounds', []):
            A = r.get('support') or r.get('A_cols') or None
            if not A:
                continue
            name = f"{path.stem}_round{r.get('round', r.get('iteration','?'))}"
            cands.append({'name': name, 'source': str(path), 'round': r.get('round', r.get('iteration')), 'A_cols': [int(x) for x in A]})
    # De-duplicate by sorted multiset, keep the best-named first.
    seen = set(); out = []
    for c in cands:
        key = tuple(c['A_cols'])
        if key in seen:
            continue
        seen.add(key); out.append(c)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--max-completion', type=int, default=4, help='attempt rank-one completion for this many best Wang-distinct candidates')
    ap.add_argument('--completion-time', type=float, default=120.0)
    ap.add_argument('--out', type=Path, default=OUTDIR / 'distinct_candidate_completion.json')
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    lut, _ = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    core = CoreQuotient(1)
    records, meta = build_core_constraints(core, lut)
    T = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    contractions = build_contractions(T)
    candidates = load_candidates()
    print(f'loaded {len(candidates)} candidate supports')

    analyses = []
    for c in candidates:
        A = c['A_cols']
        distinct = len(set(A))
        max_mult = max(Counter(A).values()) if A else 0
        if len(A) != 19:
            continue
        scan = complete_core_wang_scan(c['name'], A, 19, records, max_head=60)
        sat = saturation_domains(T, A)
        sat_sum = sat['summary']
        trans = transversal_failures(sat['sat_records'], sat['B_domains'], sat['C_domains'], 9, 9, max_report=5)
        masks = {q: point_mask_for_q(q) for q in contractions}
        qscan = eval_candidate_sources(c['name'], A, contractions, masks, max_source_size=2, max_store=20)
        rec = {
            **c,
            'distinct_A': distinct,
            'max_mult': max_mult,
            'complete_wang_violations': scan['complete_violation_count'],
            'max_excess': scan['max_excess'],
            'violations_by_dim8': scan['violations_by_dim8'],
            'violations_by_L': scan['violations_by_full_lut_L'],
            'violations_head': scan['violations_head'][:15],
            'saturation': {
                'saturated_contractions': sat_sum['saturated_contraction_count'],
                'zero_domain_terms': len(sat_sum['zero_domain_terms']),
                'linear_pass': sat_sum['linear_membership']['necessary_linear_test_passed'],
                'affine_dim': sat_sum['linear_membership']['affine_solution_dimension_if_consistent'],
            },
            'transversal_failures': trans['failure_count_reported'],
            'quotient_rank_violations_size2': qscan['violated_guarded_instances'],
        }
        analyses.append(rec)
        print(f"{c['name']}: distinct={distinct} mult={max_mult} Wang={rec['complete_wang_violations']} zero={rec['saturation']['zero_domain_terms']} lin={rec['saturation']['linear_pass']} trans={rec['transversal_failures']} qviol={rec['quotient_rank_violations_size2']}")

    analyses.sort(key=lambda r: (r['complete_wang_violations'], r['max_mult'], r['quotient_rank_violations_size2'], r['transversal_failures']))
    completion_results = []
    attempted = 0
    for rec in analyses:
        if attempted >= args.max_completion:
            break
        if rec['max_mult'] != 1:
            continue
        # Completion only meaningful as construction attempt; Wang violations mean not a support satisfying the current lower-bound table, but B/C may still reveal structure.
        attempted += 1
        print(f"completion attempt {attempted}: {rec['name']} Wang={rec['complete_wang_violations']}")
        try:
            comp = solve_fixed_A_completion(T, rec['A_cols'], timeout_sec=args.completion_time)
        except TypeError:
            comp = solve_fixed_A_completion(T, rec['A_cols'])
        except Exception as e:
            comp = {'error': repr(e)}
        completion_results.append({'name': rec['name'], 'A_cols': rec['A_cols'], 'complete_wang_violations': rec['complete_wang_violations'], 'completion': comp})
        print('  completion result keys/status:', comp.get('status') if isinstance(comp, dict) else type(comp))

    out = {
        'schema': 'distinct_candidate_completion_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': 19,
        'candidate_count': len(candidates),
        'analysis_count': len(analyses),
        'complete_core_table_meta': meta,
        'best_analyses': analyses[:30],
        'completion_attempts': completion_results,
        'interpretation': 'These are exact checks of low-violation distinct A-supports. A support with Wang violations is not an admissible rank-19 core support; completion failures are candidate-specific, not family lower bounds.',
        'elapsed_sec': round(time.time()-t0, 3),
    }
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f'Saved {args.out}')

if __name__ == '__main__':
    main()
