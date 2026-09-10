#!/usr/bin/env python3
"""Collect analysis rep2 marked-orbit branch evidence.

Each marked branch has prefix [1,2,rep], where rep runs over the 17 orbits of
Stab([1,2]) on the remaining projective A-points.  A branch is counted closed
only if there is a DRAT-verified UNSAT formula with exact local regeneration.
"""
from __future__ import annotations
import json
import pathlib
from typing import Optional

WS = pathlib.Path('workspace')

TESTED_REPS = [3, 4, 8, 10, 12, 24, 32, 80, 225]


def read_json(p: pathlib.Path) -> Optional[dict]:
    if not p.exists():
        return None
    return json.loads(p.read_text())


def compact(path: pathlib.Path) -> dict:
    d = read_json(path)
    out = {'path': str(path), 'exists': path.exists()}
    if not d:
        return out
    out['status'] = d.get('status')
    out['summary_status'] = d.get('summary_status')
    out['fixed_prefix'] = d.get('fixed_prefix')
    out['target'] = d.get('target')
    out['survivor_count'] = d.get('survivor_count')
    if 'rounds' in d:
        out['rounds'] = d.get('rounds')
    if 'learned_clause_count' in d:
        out['learned_clause_count'] = d.get('learned_clause_count')
    if 'learned_clause_provenance_sha256' in d:
        out['learned_clause_provenance_sha256'] = d.get('learned_clause_provenance_sha256')
    if 'final_clauses' in d:
        out['final_clauses'] = d.get('final_clauses')
        out['final_variables'] = d.get('final_variables')
    if 'cnf_check' in d:
        out['cnf_clauses'] = d['cnf_check'].get('cnf_clauses')
        out['cnf_variables'] = d['cnf_check'].get('cnf_variables')
        out['exact_sequence_match'] = d['cnf_check'].get('exact_sequence_match')
    if 'structure_check' in d:
        out['structure_ok'] = d['structure_check'].get('structure_ok')
    if 'learned_check' in d:
        out['learned_checked'] = d['learned_check'].get('learned_checked')
        out['learned_bad_count'] = d['learned_check'].get('learned_bad_count')
    if 'initial_solve' in d:
        out['initial_cadical_exit'] = d['initial_solve'].get('cadical_exit')
        out['initial_cadical_sec'] = d['initial_solve'].get('cadical_sec')
    if 'full_lut_violations' in d:
        out['full_lut_violation_count'] = d['full_lut_violations'].get('count')
        out['max_excess'] = d['full_lut_violations'].get('max_excess')
    if 'promotion_count' in d:
        out['promotion_count'] = d.get('promotion_count')
        out['promotion_clause_count'] = d.get('promotion_clause_count')
    if 'promotion_check' in d:
        out['promotion_count'] = d['promotion_check'].get('promotion_count')
        out['promotion_clause_count'] = d['promotion_check'].get('promotion_clause_count_regenerated')
        out['promotion_aux_intervals'] = d['promotion_check'].get('promotion_aux_interval_count')
        out['promotion_problem_count'] = d['promotion_check'].get('promotion_problem_count')
    if 'drat_trim' in d:
        out['drat_verified'] = d['drat_trim'].get('verified')
        out['drat_sha256'] = d.get('drat_sha256')
    if 'drat_replay' in d:
        out['drat_verified'] = None if d['drat_replay'] is None else d['drat_replay'].get('verified')
    return out


def rep_dirname(rep: int) -> str:
    return f'rep{rep:03d}'


def main() -> None:
    profile = read_json(WS / 'data/rep2_marked_profile/summary.json') or {'records': []}
    records = {int(r['rep']): r for r in profile.get('records', [])}
    out_records = []
    closed = []
    for rep, prof in sorted(records.items(), key=lambda kv: kv[0]):
        name = rep_dirname(rep)
        rec = {
            'rep': rep,
            'rank': prof.get('rep_matrix_rank'),
            'orbit_size': prof.get('orbit_size'),
            'profile_survivor_count': prof.get('survivor_count'),
            'profile_target': prof.get('target'),
            'base_graph_status': prof.get('status'),
            'base_graph_violations': (prof.get('full_lut_violations') or {}).get('count'),
            'tested_in': rep in TESTED_REPS,
        }
        if rep == 3:
            seed_root = WS / 'data/rep2_marked_witness/rep003'
            fair = WS / 'data/fair_seed/rep2_rep003_witness20/summary.json'
            prom_root = WS / 'data/rep2_rep003_promotion/lowres_12w8'
        else:
            seed_root = WS / f'data/rep2_marked_witness/{name}'
            fair = WS / f'data/fair_seed/rep2_{name}_witness20/summary.json'
            prom_root = WS / f'data/rep2_marked_promotion/{name}_lowres_12w8'
        rec['witness_seed_summary'] = compact(seed_root / 'summary.json')
        rec['witness_seed_verification'] = compact(seed_root / 'strict_verification.json')
        rec['fair_seed_summary'] = compact(fair)
        rec['promotion_summary'] = compact(prom_root / 'summary.json')
        rec['promotion_verification'] = compact(prom_root / 'strict_verification.json')
        pv = rec['promotion_verification']
        ps = rec['promotion_summary']
        is_closed = (ps.get('status') == 'UNSAT' and pv.get('status') == 'verified' and pv.get('drat_verified') is True)
        rec['closed'] = bool(is_closed)
        if is_closed:
            closed.append(rep)
        out_records.append(rec)

    output = {
        'schema': 'rep2_marked_status_v1',
        'scope': 'Fixed-prefix A-support branch evidence for rep2 adjacent-pair over F2 Wang occupation rows. A closed rep excludes supports whose third selected point is in that stabilizer orbit; all 17 reps are required to close rep2.',
        'total_marked_orbits': len(out_records),
        'tested_reps': TESTED_REPS,
        'closed_reps': closed,
        'open_reps': [r['rep'] for r in out_records if not r['closed']],
        'closed_orbit_size_sum': sum(int(records[r]['orbit_size']) for r in closed),
        'total_orbit_size_sum': sum(int(r['orbit_size']) for r in records.values()),
        'rep2_closed': len(closed) == len(out_records) and len(out_records) > 0,
        'records': out_records,
    }
    path = WS / 'data/rep2_marked_status/summary.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(output, indent=2, sort_keys=True) + '\n')
    print(f"closed reps {closed}; {len(closed)}/{len(out_records)} marked orbits closed; orbit-size coverage {output['closed_orbit_size_sum']}/{output['total_orbit_size_sum']}")
    for r in out_records:
        if r['tested_in']:
            print(json.dumps({
                'rep': r['rep'],
                'rank': r['rank'],
                'orbit_size': r['orbit_size'],
                'seed_status': r['witness_seed_summary'].get('status'),
                'fair_status': r['fair_seed_summary'].get('status'),
                'fair_violations': r['fair_seed_summary'].get('full_lut_violation_count'),
                'promotion_status': r['promotion_summary'].get('status'),
                'promotion_verified': r['promotion_verification'].get('status'),
                'drat_verified': r['promotion_verification'].get('drat_verified'),
                'closed': r['closed'],
            }, sort_keys=True))
    print(f'saved {path}')


if __name__ == '__main__':
    main()
