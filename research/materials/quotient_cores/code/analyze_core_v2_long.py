#!/usr/bin/env python3
"""Analyze the delivered analysis long E11-core partial search with complete tests.

The source `core_e11_saturation_v2_long.json` used the old partial Wang scan.
This script rescans each returned support against all 417,199 E11-core Wang
subspaces and applies saturated-domain linear membership plus Rado transversal
checks.  The search remains a distinct-A support search; this is not a lower
bound proof.
"""
from __future__ import annotations

import json
import pickle
import sys
import time
from pathlib import Path

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402
from complete_core_and_transversal import (  # noqa: E402
    ROOT,
    build_core_constraints,
    complete_core_wang_scan,
    saturation_domains,
    transversal_failures,
)

OUT = ROOT / 'workspace/data/core_complete_transversal/core_e11_v2_long_complete_analysis.json'
SRC = ROOT / 'workspace/data/dual_ruling/core_e11_saturation_v2_long.json'
LUT = ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl'


def load_lut():
    with LUT.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}


def main():
    t0 = time.time()
    OUT.parent.mkdir(parents=True, exist_ok=True)
    source = json.loads(SRC.read_text())
    lut = load_lut()
    core = CoreQuotient(1)
    records, meta = build_core_constraints(core, lut)
    T_core = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2

    analyzed = []
    best = []
    for r in source['rounds']:
        if r.get('status') not in ('OPTIMAL', 'FEASIBLE') or 'support' not in r:
            analyzed.append({'round': r.get('round'), 'status': r.get('status'), 'note': 'no support'})
            continue
        support = [int(x) for x in r['support']]
        scan = complete_core_wang_scan(f"v2_long_round{r['round']}", support, 19, records, max_head=60)
        sat = saturation_domains(T_core, support)
        lin = sat['summary']['linear_membership']
        trans = transversal_failures(sat['sat_records'], sat['B_domains'], sat['C_domains'], 9, 9, max_report=60)
        rec = {
            'round': int(r['round']),
            'source_status': r['status'],
            'source_partial_wang_violations': r.get('wang_violations'),
            'source_zero_domains': r.get('saturation', {}).get('zero_domains'),
            'source_saturated': r.get('saturation', {}).get('saturated'),
            'support': support,
            'complete_wang_scan': {k: v for k, v in scan.items() if k != 'violations_head'},
            'complete_wang_violations_head': scan['violations_head'][:20],
            'saturation': {
                'saturated_contraction_count': sat['summary']['saturated_contraction_count'],
                'undersaturated_contraction_count': sat['summary']['undersaturated_contraction_count'],
                'zero_domain_term_count': len(sat['summary']['zero_domain_terms']),
                'term_domain_dims_hist': sat['summary']['term_domain_dims_hist'],
                'linear_passed': lin['necessary_linear_test_passed'],
                'linear_affine_dim': lin['affine_solution_dimension_if_consistent'],
                'linear_rank': lin['coefficient_rank'],
                'linear_variables': lin['variables'],
                'transversal_failure_count_reported': trans['failure_count_reported'],
                'transversal_contractions_with_failure_reported': trans['saturated_contractions_with_failure_reported'],
                'transversal_witnesses_head': trans['failures_head'][:12],
            },
        }
        analyzed.append(rec)
        best.append({
            'round': rec['round'],
            'partial': rec['source_partial_wang_violations'],
            'complete': scan['complete_violation_count'],
            'max_excess': scan['max_excess'],
            'zero': rec['saturation']['zero_domain_term_count'],
            'linear': rec['saturation']['linear_passed'],
            'affine_dim': rec['saturation']['linear_affine_dim'],
            'trans': rec['saturation']['transversal_failure_count_reported'],
            'support': support,
        })
        print(json.dumps(best[-1], sort_keys=True))

    best_sorted = sorted([b for b in best if b['complete'] is not None], key=lambda x: (x['complete'], x['zero'], x['trans'], x['partial'] or 9999))
    result = {
        'schema': 'core_e11_v2_long_complete_analysis_v1',
        'field': 'F2',
        'source': str(SRC),
        'scope': 'Complete evaluation of supports produced by the old partial distinct-A E11-core separator. This does not cover multiplicity-bearing decompositions.',
        'core_table_meta': meta,
        'source_final_status': source.get('final_status'),
        'source_total_rounds': source.get('total_rounds'),
        'best_by_complete_violation': best_sorted[:10],
        'analyzed_rounds': analyzed,
        'total_elapsed_sec': round(time.time() - t0, 3),
    }
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'Saved {OUT}')


if __name__ == '__main__':
    main()
