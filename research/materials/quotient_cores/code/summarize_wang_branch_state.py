#!/usr/bin/env python3
"""Summarize proof and probe status for the F2 Wang fixed-E11 branch.

The output is a research-state snapshot, not a theorem checker.  It distinguishes
DRAT-verified leaves from CP-SAT probes and records which finite branch pieces
remain to be converted into proof objects.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


def load_json(path: Path):
    return json.loads(path.read_text())


def verified_status(path: Path) -> bool:
    try:
        data = load_json(path)
    except Exception:
        return False
    return bool(data.get('drat_trim_log_parse', {}).get('verified')) or bool(data.get('cadical_log_parse', {}).get('verified'))


def status_brief(path: Path) -> dict:
    data = load_json(path)
    return {
        'path': str(path),
        'cadical_exit': data.get('cadical_exit'),
        'cadical_elapsed_sec': data.get('cadical_elapsed_sec'),
        'drat_trim_exit': data.get('drat_trim_exit'),
        'drat_trim_elapsed_sec': data.get('drat_trim_elapsed_sec'),
        'verified': bool(data.get('drat_trim_log_parse', {}).get('verified')),
        'unsat': bool(data.get('cadical_log_parse', {}).get('unsat')),
        'sat': bool(data.get('cadical_log_parse', {}).get('sat')),
        'hashes': data.get('hashes', {}),
    }


def collect_statuses(root: Path) -> list[dict]:
    out = []
    if root.exists():
        for p in sorted(root.rglob('*.status.json')):
            try:
                out.append(status_brief(p))
            except Exception as e:
                out.append({'path': str(p), 'error': repr(e)})
    return out


def collect_pair_cp_summaries(paths: list[Path]) -> dict:
    records = []
    for sp in paths:
        if not sp.exists():
            continue
        data = load_json(sp)
        for r in data.get('records', []):
            rr = dict(r)
            rr['summary_path'] = str(sp)
            records.append(rr)
    records.sort(key=lambda r: int(r.get('pair_orbit_global_index', -1)))
    return {
        'summary_paths': [str(p) for p in paths if p.exists()],
        'record_count': len(records),
        'index_set': [int(r.get('pair_orbit_global_index')) for r in records],
        'status_hist': dict(sorted(Counter(r.get('solver_status') for r in records).items())),
        'sat_or_feasible_records': [r for r in records if r.get('solver_status') in ('OPTIMAL', 'FEASIBLE')],
        'records': records,
    }


def classify_exact18_pair_proofs(statuses: list[dict]) -> list[dict]:
    proofs = []
    for st in statuses:
        p = Path(st['path'])
        name = p.parent.name
        if not name.startswith('pair_'):
            continue
        # Expected pattern pair_002_17_26_exact18_max9
        parts = name.split('_')
        if len(parts) < 6:
            continue
        try:
            idx = int(parts[1]); a = int(parts[2]); b = int(parts[3]); maxpart = parts[-1]
        except Exception:
            continue
        proofs.append({
            'pair_orbit_global_index': idx,
            'pair': [a, b],
            'directory': str(p.parent),
            'status_path': st['path'],
            'max_intersection_filter': maxpart,
            'verified': st.get('verified', False),
            'unsat': st.get('unsat', False),
            'sat': st.get('sat', False),
            'hashes': st.get('hashes', {}),
        })
    proofs.sort(key=lambda r: (r['pair_orbit_global_index'], r['max_intersection_filter']))
    return proofs


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()

    part_path = Path('data/wang_branch_partition/fixed_e11_partition_certificate.json')
    partition = load_json(part_path) if part_path.exists() else None
    fixed_statuses = collect_statuses(Path('data/wang_capacity_e11_fixed'))
    exact18_statuses = (
        collect_statuses(Path('data/rank1_fixed_high_filtered_cnf'))
        + collect_statuses(Path('data/rank1_pair_filtered_proof_batch'))
    )
    pair_cp = collect_pair_cp_summaries([
        Path('data/rank1_highpair_batch/pilot5_summary.json'),
        Path('data/rank1_highpair_batch/all69_remaining_from5_summary.json'),
    ])
    pair_proofs = classify_exact18_pair_proofs(exact18_statuses)
    verified_pair_indices = sorted({p['pair_orbit_global_index'] for p in pair_proofs if p['verified'] and p['unsat']})
    all_pair_indices = list(range(69))
    missing_pair_proof_indices = [i for i in all_pair_indices if i not in set(verified_pair_indices)]

    range_root = Path('data/wang_fixed_e11_range_cpsat')
    range_records = []
    if range_root.exists():
        for p in sorted(range_root.rglob('*.json')):
            if p.name.endswith('full_capacity_check.json'):
                continue
            try:
                d = load_json(p)
            except Exception:
                continue
            if d.get('problem') == 'fixed-E11 Wang support CP-SAT with rank-1-count range':
                range_records.append({
                    'path': str(p),
                    'fixed_points': d.get('fixed_points'),
                    'min_rank1_count': d.get('min_rank1_count'),
                    'max_rank1_count': d.get('max_rank1_count'),
                    'exact_rank1_count': d.get('exact_rank1_count'),
                    'solver_status': d.get('solver_status'),
                    'support_rank1_count': d.get('support_rank1_count'),
                    'support_rank_hist': d.get('support_rank_hist'),
                    'support_size': d.get('support_size'),
                    'wang_rows_added': d.get('wang_rows_added'),
                    'rank1_projection_rows_added': d.get('rank1_projection_rows_added'),
                    'build_elapsed_sec': d.get('build_elapsed_sec'),
                    'solve_elapsed_sec': d.get('solve_elapsed_sec'),
                })
    payload = {
        'problem': 'status summary for F2 Wang fixed-E11 rank-20 support branch',
        'partition_certificate_path': str(part_path),
        'partition_overall_boolean': None if partition is None else partition.get('overall_boolean'),
        'second_point_orbit_reps': None if partition is None else partition.get('single_orbits_after_fixing_E11', {}).get('reps'),
        'fixed_E11_second_orbit_statuses': fixed_statuses,
        'exact18_filtered_status_count': len(exact18_statuses),
        'exact18_single_high_verified_dirs': [s['path'] for s in exact18_statuses if '/high' in s['path'] and s.get('verified')],
        'exact18_pair_cp_sat': {
            'record_count': pair_cp['record_count'],
            'status_hist': pair_cp['status_hist'],
            'sat_or_feasible_records': pair_cp['sat_or_feasible_records'],
        },
        'exact18_pair_cp_sat_all69_infeasible': pair_cp['record_count'] == 69 and pair_cp['status_hist'] == {'INFEASIBLE': 69},
        'exact18_pair_proofs': pair_proofs,
        'exact18_pair_verified_indices': verified_pair_indices,
        'exact18_pair_verified_count': len(verified_pair_indices),
        'exact18_pair_missing_proof_indices': missing_pair_proof_indices,
        'rank1_count_range_probes': range_records,
        'meaning': 'Verified DRAT leaves are theorem-ready proof objects, while CP-SAT infeasible and UNKNOWN entries are execution evidence or route information only.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(args.out),
        'partition_ok': payload['partition_overall_boolean'],
        'exact18_pair_cp_sat_all69_infeasible': payload['exact18_pair_cp_sat_all69_infeasible'],
        'exact18_pair_verified_count': payload['exact18_pair_verified_count'],
        'exact18_pair_missing_proof_count': len(missing_pair_proof_indices),
        'range_probe_status_hist': dict(sorted(Counter(r['solver_status'] for r in range_records).items())),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
