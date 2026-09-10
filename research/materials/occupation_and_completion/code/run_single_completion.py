#!/usr/bin/env python3
"""analysis: run exact fixed-A B/C completion on one E11-core support."""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from complete_core_and_transversal import ROOT, build_core_constraints, complete_core_wang_scan, saturation_domains, transversal_failures
from quotient_rank_cuts import build_contractions, point_mask_for_q
from candidate_source_qcut_scan import eval_candidate_sources
from core_capacity_from_wang_lut import CoreQuotient, load_lut
from fixed_A_rankone_solver import solve_fixed_A_completion


def load_support(path: Path, index: int):
    d = json.loads(path.read_text())
    if 'A_cols' in d:
        return [int(x) for x in d['A_cols']], path.stem
    if d.get('solutions'):
        sol = d['solutions'][index]
        return [int(x) for x in sol['A_cols']], sol.get('label', f'{path.stem}_solution{index}')
    if d.get('rounds'):
        r = d['rounds'][index]
        return [int(x) for x in (r.get('support') or r.get('A_cols'))], f"{path.stem}_round{r.get('round', index)}"
    raise ValueError(f'cannot load support from {path}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--support-json', type=Path, required=True)
    ap.add_argument('--support-index', type=int, default=0)
    ap.add_argument('--time-limit', type=float, default=300.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--seed', type=int, default=4949)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    A, label = load_support(args.support_json, args.support_index)
    lut, _ = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records, meta = build_core_constraints(CoreQuotient(1), lut)
    T = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    contractions = build_contractions(T)
    masks = {q: point_mask_for_q(q) for q in contractions}
    scan = complete_core_wang_scan(label, A, 19, records, max_head=30)
    sat = saturation_domains(T, A)
    trans = transversal_failures(sat['sat_records'], sat['B_domains'], sat['C_domains'], 9, 9, max_report=20)
    qscan = eval_candidate_sources(label, A, contractions, masks, max_source_size=2, max_store=20)
    comp = solve_fixed_A_completion(T, A, timeout_sec=args.time_limit, workers=args.workers, seed=args.seed, label=label)
    out = {
        'schema': 'single_completion_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': 19,
        'source': str(args.support_json),
        'source_index': args.support_index,
        'label': label,
        'A_cols': A,
        'distinct_A': len(set(A)),
        'complete_core_table_meta': meta,
        'wang_scan': scan,
        'saturation_summary': sat['summary'],
        'transversal': trans,
        'quotient_rank_scan_size2': qscan,
        'completion': comp,
        'interpretation': 'A support with Wang violations is not admissible; completion is run to test fixed-A solver behavior and local B/C compatibility, not to override Wang occupation.',
        'elapsed_sec': round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(args.out),
        'label': label,
        'wang_violations': scan['complete_violation_count'],
        'zero_domain_terms': len(sat['summary']['zero_domain_terms']),
        'linear_pass': sat['summary']['linear_membership']['necessary_linear_test_passed'],
        'transversal_failures': trans['failure_count_reported'],
        'qviol_size2': qscan['violated_guarded_instances'],
        'completion_status': comp.get('status'),
        'verified_decomposition': comp.get('verified_decomposition'),
        'elapsed_sec': out['elapsed_sec'],
    }, sort_keys=True))


if __name__ == '__main__':
    main()
