#!/usr/bin/env python3
"""Summarize analysis anchored matching stratum results."""
from __future__ import annotations

import json
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path('data/matching_strata')


def load(path: Path):
    return json.loads(path.read_text())


def main() -> None:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, default=ROOT / 'matching_strata_summary.json')
    args = ap.parse_args()
    classification = load(ROOT / 'anchored_matching_strata.json')
    profile = load(ROOT / 'matching_stratum_residual_profile.json')
    audit = load(ROOT / 'cover_connection_audit.json')
    lazy_files = sorted(ROOT.glob('lazy_k*_stratum_*.json'))
    lazy_records = []
    for p in lazy_files:
        d = load(p)
        lazy_records.append({
            'path': str(p),
            'matching': d['fixed_rank1_matching'],
            'k': d['total_rank1_k'],
            'target_higher_rank_count': d['target_higher_rank_count'],
            'final_status': d['final_status'],
            'iteration_count': d['iteration_count'],
            'cut_count_total': d['cut_count_total'],
            'cuts_by_mode': d.get('cuts_by_mode'),
            'cuts_by_reason': d.get('cuts_by_reason'),
            'elapsed_sec': d.get('elapsed_sec'),
            'candidate_violation_counts': [it.get('full_lut_scan', {}).get('violation_count') for it in d.get('history', []) if 'full_lut_scan' in it],
            'candidate_max_excess': [it.get('full_lut_scan', {}).get('max_excess') for it in d.get('history', []) if 'full_lut_scan' in it],
        })
    rank1_impossible = [r for r in profile['records'] if r['rank1_only_status'] == 'IMPOSSIBLE']
    k7_reps = classification['representatives_by_k']['7']
    k7_impossible = [r for r in rank1_impossible if r['k'] == 7]
    k7_lazy = [r for r in lazy_records if r['k'] == 7]
    covered_k7_matchings = sorted([tuple(r['canonical']) for r in k7_impossible] + [tuple(r['matching']) for r in k7_lazy])
    all_k7_matchings = sorted(tuple(int(p) for p in r['canonical']) for r in k7_reps)
    missing_k7 = [list(x) for x in all_k7_matchings if x not in set(covered_k7_matchings)]
    by_status = Counter(r['final_status'] for r in lazy_records)
    by_k_status = Counter((r['k'], r['final_status']) for r in lazy_records)
    payload = {
        'problem': 'analysis matching-stratum execution summary',
        'field': 'F2',
        'cover_connection_audit_path': str(ROOT / 'cover_connection_audit.json'),
        'cover_connection_checks_passed': audit.get('all_connection_checks_passed'),
        'classification_path': str(ROOT / 'anchored_matching_strata.json'),
        'anchored_matching_count': classification['anchored_matching_count'],
        'strata_count_total': classification['strata_count_total'],
        'strata_count_by_k': classification['strata_count_by_total_rank1_k'],
        'profile_path': str(ROOT / 'matching_stratum_residual_profile.json'),
        'rank1_only_status_by_k': profile['rank1_only_status_by_k'],
        'rank1_only_impossible_strata': [
            {
                'k': r['k'], 'canonical': r['canonical'],
                'rank1_only_violation_count': r['rank1_only_violation_count'],
                'rank1_only_max_excess': r['rank1_only_max_excess'],
                'rank1_only_bad_by_dim': r['rank1_only_bad_by_dim'],
                'rank1_only_bad_head': r['rank1_only_bad_head'][:5],
            }
            for r in rank1_impossible
        ],
        'lazy_record_count': len(lazy_records),
        'lazy_status_hist': dict(sorted(by_status.items())),
        'lazy_status_by_k': {f'k{k}_{s}': c for (k, s), c in sorted(by_k_status.items())},
        'lazy_records': lazy_records,
        'k7_matching_strata_total': len(all_k7_matchings),
        'k7_rank1_only_impossible_count': len(k7_impossible),
        'k7_lazy_infeasible_count': sum(1 for r in k7_lazy if r['final_status'] == 'INFEASIBLE'),
        'k7_missing_from_coverage': missing_k7,
        'k7_computationally_closed': (len(missing_k7) == 0 and len(k7_impossible) + sum(1 for r in k7_lazy if r['final_status'] == 'INFEASIBLE') == len(all_k7_matchings)),
        'scientific_meaning': 'The matching half of the global cover has only 38 whole-matching strata. At k=7, two strata are impossible by fixed rank-1 occupancy alone and four surviving strata became CP-SAT INFEASIBLE after lazy full-LUT cut learning. This is computational evidence and a proof-target decomposition, not a checked lower-bound theorem.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'cover_connection_checks_passed': payload['cover_connection_checks_passed'],
        'strata_count_total': payload['strata_count_total'],
        'rank1_only_status_by_k': payload['rank1_only_status_by_k'],
        'lazy_status_hist': payload['lazy_status_hist'],
        'k7_computationally_closed': payload['k7_computationally_closed'],
        'k7_missing': payload['k7_missing_from_coverage'],
        'out': str(args.out),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
