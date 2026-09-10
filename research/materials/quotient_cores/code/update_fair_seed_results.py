#!/usr/bin/env python3
"""Collect analysis fair-seed solve outcomes into a compact evidence table."""
from __future__ import annotations
import json
import pathlib

ROOTS = {
    'k1_idx00': pathlib.Path('workspace/data/fair_seed/k1_idx00_copy/summary.json'),
    'k4_idx05': pathlib.Path('workspace/data/fair_seed/k4_idx05_copy/summary.json'),
    'k5_idx15': pathlib.Path('workspace/data/fair_seed/k5_idx15_copy/summary.json'),
    'k5_idx16': pathlib.Path('workspace/data/fair_seed/k5_idx16_regen/summary.json'),
    'k4_idx06': pathlib.Path('workspace/data/fair_seed/k4_idx06_regen/summary.json'),
}


def main() -> None:
    rows = []
    for label, path in ROOTS.items():
        rec = {'label': label, 'summary_path': str(path), 'exists': path.exists()}
        if path.exists():
            d = json.loads(path.read_text())
            rec.update({
                'status': d.get('status'),
                'branch': d.get('branch'),
                'idx': d.get('idx'),
                'k': d.get('k'),
                'target': d.get('target'),
                'survivor_count': d.get('survivor_count'),
                'cnf_source': d.get('cnf_source'),
                'cnf_clauses': d.get('cnf_check', {}).get('cnf_clauses'),
                'cnf_variables': d.get('cnf_check', {}).get('cnf_variables'),
                'exact_sequence_match': d.get('cnf_check', {}).get('exact_sequence_match'),
                'provenance_ok': d.get('provenance_ok'),
                'initial_cadical_exit': d.get('initial_solve', {}).get('cadical_exit'),
                'initial_cadical_sec': d.get('initial_solve', {}).get('cadical_sec'),
                'drat_verified': d.get('drat_trim', {}).get('verified'),
                'full_lut_violation_count': d.get('full_lut_violations', {}).get('count'),
                'max_excess': d.get('full_lut_violations', {}).get('max_excess'),
            })
        rows.append(rec)
    out = {
        'schema': 'fair_seed_results_v1',
        'interpretation': 'A SAT result shows the seed CNF is only a relaxation and the returned support still violates complete Wang LUT rows; UNSAT needs exact regeneration and DRAT replay before it closes the fixed branch.',
        'results': rows,
    }
    out_path = pathlib.Path('workspace/data/fair_seed/summary.json')
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    for r in rows:
        print(json.dumps({k: r.get(k) for k in ['label','exists','status','idx','k','cnf_clauses','initial_cadical_sec','full_lut_violation_count','drat_verified']}, sort_keys=True))
    print(f'Saved {out_path}')


if __name__ == '__main__':
    main()
