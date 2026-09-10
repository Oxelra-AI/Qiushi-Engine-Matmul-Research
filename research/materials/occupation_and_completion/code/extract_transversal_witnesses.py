#!/usr/bin/env python3
"""Extract focused saturated-transversal witnesses from analysis targets.

The output keeps enough linear-algebra data to reconstruct each fixed-support
obstruction: the saturated contraction q, the failing subset of terms, their
A-points, their globally intersected B/C domains, and the basis of the sum of
those domains whose dimension is too small.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Sequence

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import build_matmul_tensor_f2, gf2_rank_rows, rref_basis  # noqa: E402
from complete_core_and_transversal import ROOT, saturation_domains, transversal_failures  # noqa: E402

OUTDIR = ROOT / 'workspace/data/core_complete_transversal'


def sum_basis(domains: Sequence[Sequence[int]], n: int):
    rows = []
    for d in domains:
        rows.extend(int(x) for x in d)
    return list(rref_basis(rows, n))


def focused_witness(label: str, T: np.ndarray, A_cols: Sequence[int], max_witnesses: int = 12) -> dict:
    sat = saturation_domains(T, A_cols)
    trans = transversal_failures(sat['sat_records'], sat['B_domains'], sat['C_domains'], T.shape[1], T.shape[2], max_report=max_witnesses)
    sat_by_q = {int(r['q']): r for r in sat['sat_records']}
    sat_qs_by_term = {s: [] for s in range(len(A_cols))}
    for r in sat['sat_records']:
        for s in r['terms']:
            sat_qs_by_term[int(s)].append(int(r['q']))
    records = []
    for f in trans['failures_head'][:max_witnesses]:
        side = f['side']
        n = T.shape[1] if side == 'B' else T.shape[2]
        domains = sat['B_domains'] if side == 'B' else sat['C_domains']
        J = [int(x) for x in f['subset_terms']]
        sb = sum_basis([domains[s] for s in J], n)
        records.append({
            'q': int(f['q']),
            'q_hex': f['q_hex'],
            'rank': int(f['rank']),
            'side': side,
            'participating_terms': [int(x) for x in f['participating_terms']],
            'participating_A_points': [int(A_cols[int(x)]) for x in f['participating_terms']],
            'subset_terms': J,
            'subset_A_points': [int(A_cols[s]) for s in J],
            'subset_size': int(f['subset_size']),
            'sum_domain_dim': int(f['sum_domain_dim']),
            'sum_domain_basis': sb,
            'term_domains': [
                {
                    'term': s,
                    'A_point': int(A_cols[s]),
                    'basis': [int(x) for x in domains[s]],
                    'dim': len(domains[s]),
                    'saturated_contractions_containing_term': sat_qs_by_term[s],
                }
                for s in J
            ],
            'raw_contraction_space_basis': sat_by_q[int(f['q'])]['B_space_basis' if side == 'B' else 'C_space_basis'],
            'interpretation': 'No independent representatives can be chosen from the listed term domains for this saturated contraction, since the sum dimension is smaller than the number of required independent B/C factors.',
        })
    return {
        'label': label,
        'term_count': len(A_cols),
        'distinct_A_points': len(set(int(a) for a in A_cols)),
        'saturation_summary': sat['summary'],
        'transversal_summary': {k: v for k, v in trans.items() if k != 'failures_head' and k != 'per_q_first_head'},
        'focused_witnesses': records,
    }


def main():
    core_json = json.loads((ROOT / 'workspace/data/dual_ruling/core_e11_saturation_v2.json').read_text())
    T_core = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    full_T = build_matmul_tensor_f2()
    combined = json.loads((ROOT / 'workspace/data/dual_ruling/combined_sep_all5.json').read_text())

    targets = []
    r5 = next(r for r in core_json['rounds'] if r.get('round') == 5)
    targets.append(('core_round5_partialscan', T_core, [int(x) for x in r5['support']]))
    r1 = next(r for r in core_json['rounds'] if r.get('round') == 1)
    targets.append(('core_round1_partialscan', T_core, [int(x) for x in r1['support']]))
    targets.append(('combined_rep2_all5_round0', full_T, [int(x) for x in combined['rounds'][0]['support']]))

    out = {'schema': 'transversal_witnesses_v1', 'field': 'F2', 'targets': []}
    for label, T, A in targets:
        rec = focused_witness(label, T, A)
        out['targets'].append(rec)
        print(json.dumps({
            'label': label,
            'zero_terms': len(rec['saturation_summary']['zero_domain_terms']),
            'linear': rec['saturation_summary']['linear_membership']['necessary_linear_test_passed'],
            'saturated': rec['saturation_summary']['saturated_contraction_count'],
            'witnesses': len(rec['focused_witnesses']),
            'first': None if not rec['focused_witnesses'] else {k: rec['focused_witnesses'][0][k] for k in ['q','side','subset_terms','subset_A_points','subset_size','sum_domain_dim']},
        }, sort_keys=True))

    path = OUTDIR / 'transversal_witnesses.json'
    path.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f'Saved {path}')


if __name__ == '__main__':
    main()
