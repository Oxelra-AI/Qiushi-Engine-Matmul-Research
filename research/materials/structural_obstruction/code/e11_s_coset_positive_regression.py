#!/usr/bin/env python3
"""Positive-regression check for S-level E11 coset-rank SAT.

This script rebuilds the analysis known rank-21 quotient/regression instance,
extracts S=span{B_j tensor C_j} from the quotient terms, and runs the S-only
fixed-A coset SAT on the known inside A-vectors.  It confirms that the S-level
encoder can return SAT and that its equations agree with the general lift
convention.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

SCRIPTS = Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import e11_quotient_lift_general_sat as glift  # noqa: E402
import e11_s_coset_rank_sat as scoset  # noqa: E402


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--meta', type=Path, default=Path('data/general_lift_positive_regression/known_rank21_inside4_meta.json'))
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--workdir', type=Path, required=True)
    ap.add_argument('--solver', default='cryptominisat5')
    ap.add_argument('--timeout', type=int, default=60)
    ap.add_argument('--threads', type=int, default=4)
    args = ap.parse_args()

    t0 = time.time()
    meta = json.loads(args.meta.read_text())
    prefix = [int(x) for x in meta['prefix_basis']]
    pool = np.load(meta['qpool_path'])
    scheme = pool[0]
    S_basis = scoset.scheme_s_basis(scheme)
    _, _, _, Rcoords = scoset.quotient_base_residual(prefix)
    # Known residual A vectors are the inside source U masks converted to V-coordinates.
    phis = glift.find_phi_vectors(prefix, 8)
    inside_indices = [int(x) for x in meta['inside_term_indices']]
    source_u = [int(x) for x in meta['source_u_masks']]
    known_a = []
    for idx in inside_indices:
        u = source_u[idx]
        a4 = 0
        for k, phi in enumerate(phis):
            if (phi & u).bit_count() & 1:
                a4 |= 1 << k
        known_a.append(a4)

    args.workdir.mkdir(parents=True, exist_ok=True)
    enc = scoset.FixedASSubspaceSAT(Rcoords, S_basis, known_a)
    cnf_path = args.workdir / 'positive_s_coset.xor.cnf'
    enc.F.write_native(cnf_path, [
        'positive S-level coset regression from known E11 rank-21 source',
        f'prefix={prefix}',
        f'known_a={known_a}',
        f'S_dim={len(S_basis)}',
    ])
    sol = scoset.solve_native(cnf_path, args.solver, args.timeout, args.threads)

    # Also test all cover assignments implied by the m-profile, if small.
    m_by_phi = scoset.m_profile_for_S(Rcoords, S_basis)
    covers = scoset.enumerate_covers(tuple(m_by_phi[p] for p in range(1, 16)), len(known_a))
    result = {
        'purpose': 'positive regression for S-only coset rank SAT',
        'meta_path': str(args.meta),
        'field': 'F2',
        'prefix': prefix,
        'S_dim': len(S_basis),
        'S_hash': scoset.basis_hash(S_basis),
        'known_a_assignment_from_source': known_a,
        'm_by_phi': {str(k): int(v) for k, v in m_by_phi.items()},
        'valid_cover_count_at_known_residual_rank': len(covers),
        'known_assignment_is_valid_cover': known_a in covers,
        'encoding': {'vars': enc.F.next - 1, 'cnf_clauses': len(enc.F.cnf), 'xor_clauses': len(enc.F.xors)},
        'solve': sol,
        'elapsed_sec': time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True, default=int) + '\n')
    print(json.dumps({
        'S_dim': result['S_dim'],
        'known_a': known_a,
        'valid_cover_count': len(covers),
        'known_assignment_is_valid_cover': result['known_assignment_is_valid_cover'],
        'solve_status': sol['status'],
        'vars': enc.F.next - 1,
        'xors': len(enc.F.xors),
        'elapsed_sec': result['elapsed_sec'],
    }, indent=2, sort_keys=True))
    print('wrote', args.out)


if __name__ == '__main__':
    main()
