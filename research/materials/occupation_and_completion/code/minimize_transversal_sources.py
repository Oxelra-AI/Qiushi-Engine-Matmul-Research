#!/usr/bin/env python3
"""Minimize saturated-source sets for analysis transversality witnesses.

A transversality obstruction uses a saturated contraction q_star and a subset J
of participating terms.  For each s in J, the domain D_s may be witnessed by a
small set Q_s of saturated contractions containing s.  If q_star and all Q_s
remain saturated and all J terms are present, then dim(sum_s D_s) < |J| rules
out the fixed-A completion.

This script greedily removes source contractions from Q_s while preserving the
rank defect, producing smaller guarded support cuts for later exact encodings.
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

from fixed_A_saturation import build_matmul_tensor_f2, gf2_rank_rows, intersection_basis  # noqa: E402
from complete_core_and_transversal import ROOT, saturation_domains  # noqa: E402

OUT = ROOT / 'workspace/data/core_complete_transversal/transversal_minimized_sources.json'
WIT = ROOT / 'workspace/data/core_complete_transversal/transversal_witnesses.json'


def sum_dim(domains: Sequence[Sequence[int]], n: int) -> int:
    return gf2_rank_rows([int(v) for D in domains for v in D], n)


def get_target(label: str):
    if label.startswith('core_round'):
        rnum = int(label.split('round')[1].split('_')[0])
        src = json.loads((ROOT / 'workspace/data/dual_ruling/core_e11_saturation_v2_long.json').read_text())
        rec = next(r for r in src['rounds'] if r.get('round') == rnum)
        T = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
        return T, [int(x) for x in rec['support']]
    if label == 'combined_rep2_all5_round0':
        combined = json.loads((ROOT / 'workspace/data/dual_ruling/combined_sep_all5.json').read_text())
        T = build_matmul_tensor_f2()
        return T, [int(x) for x in combined['rounds'][0]['support']]
    raise KeyError(label)


def minimize_for_witness(label: str, witness: dict) -> dict:
    T, A = get_target(label)
    sat = saturation_domains(T, A)
    side = witness['side']
    side_key = 'B_space_basis' if side == 'B' else 'C_space_basis'
    domains_all = sat['B_domains'] if side == 'B' else sat['C_domains']
    n = T.shape[1] if side == 'B' else T.shape[2]
    J = [int(s) for s in witness['subset_terms']]
    q_star = int(witness['q'])

    # Source records per term: all saturated contractions containing s.
    sat_by_term = {s: [] for s in range(len(A))}
    for rec in sat['sat_records']:
        for s in rec['terms']:
            sat_by_term[int(s)].append(rec)
    sources = {s: [rec for rec in sat_by_term[s]] for s in J}

    def domains_from_sources(srcs):
        Ds = []
        for s in J:
            spaces = [tuple(int(x) for x in rec[side_key]) for rec in srcs[s]]
            Ds.append(intersection_basis(spaces, n))
        return Ds

    def still_fails(srcs):
        Ds = domains_from_sources(srcs)
        return sum_dim(Ds, n) < len(J), Ds

    ok, Ds = still_fails(sources)
    if not ok:
        raise RuntimeError('initial all-source witness no longer fails')

    changed = True
    while changed:
        changed = False
        for s in list(J):
            # Try removals that reduce total union first by q frequency, but keep simple/deterministic.
            for rec in list(sources[s]):
                trial = {t: list(v) for t, v in sources.items()}
                trial[s] = [r for r in trial[s] if int(r['q']) != int(rec['q'])]
                fail, _ = still_fails(trial)
                if fail:
                    sources = trial
                    changed = True
                    break
            if changed:
                break

    fail, Ds = still_fails(sources)
    assert fail
    source_qr_union = sorted({(int(rec['q']), int(rec['rank'])) for s in J for rec in sources[s]} | {(q_star, int(witness['rank']))})
    return {
        'label': label,
        'q_star': q_star,
        'q_star_hex': hex(q_star),
        'q_star_rank': int(witness['rank']),
        'side': side,
        'subset_terms': J,
        'subset_A_points': [int(A[s]) for s in J],
        'subset_size': len(J),
        'source_qr_union': [[q, rk] for q, rk in source_qr_union],
        'source_qr_union_count': len(source_qr_union),
        'sources_by_term': {
            str(s): {
                'A_point': int(A[s]),
                'source_qr': [[int(rec['q']), int(rec['rank'])] for rec in sources[s]],
                'domain_basis_from_sources': [int(x) for x in Ds[J.index(s)]],
                'domain_dim_from_sources': len(Ds[J.index(s)]),
                'full_domain_dim': len(domains_all[s]),
            }
            for s in J
        },
        'sum_domain_dim_from_sources': sum_dim(Ds, n),
        'defect_confirmed': sum_dim(Ds, n) < len(J),
        'guarded_cut_meaning': 'If all subset A-points are present and q_star plus all source_qr_union contractions stay saturated, no independent representatives can be chosen on this side. A reusable support cut must be guarded by absence of a point or nonsaturation of one source contraction.',
    }


def main():
    data = json.loads(WIT.read_text())
    out = {'schema': 'transversal_minimized_sources_v1', 'field': 'F2', 'witnesses': []}
    wanted = {
        'core_round5_partialscan': 3,
        'combined_rep2_all5_round0': 4,
    }
    for target in data['targets']:
        label = target['label']
        if label not in wanted:
            continue
        for w in target['focused_witnesses'][:wanted[label]]:
            rec = minimize_for_witness(label, w)
            out['witnesses'].append(rec)
            print(json.dumps({
                'label': label,
                'q_star': rec['q_star'],
                'side': rec['side'],
                'subset_size': rec['subset_size'],
                'sum_dim': rec['sum_domain_dim_from_sources'],
                'source_union': rec['source_qr_union_count'],
                'subset_A': rec['subset_A_points'],
            }, sort_keys=True))
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f'Saved {OUT}')


if __name__ == '__main__':
    main()
