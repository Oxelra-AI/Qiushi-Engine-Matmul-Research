#!/usr/bin/env python3
"""Check quotient/occupation semantics for proof-used Wang subspaces.

Wang certificate records a subspace U of the A factor as RREF rows.  The
verifier's ApplyConstraintsToTensor folds pivot slices into free coordinates,
which is the tensor image under the quotient q_U : A -> A/U represented in the
free-coordinate section.  The occupation inequality used in the rank>=21 proof
is:

  if rank(q_U(T)) >= L and T has an s-term decomposition, then at most s-L
  A-factors may lie in U, because exactly those terms are killed by q_U.

This finite check reconstructs the quotient map for every U actually used in
the research anchored proof assets and verifies q_U(a)=0 iff a is in the rowspace
U for all 512 A-vectors.  It also verifies the image dimension 9-d.
"""
from __future__ import annotations

import json
import pickle
import sys
import time
from pathlib import Path
from collections import Counter

S04 = Path('assets/quotients/scripts')
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
import wang_capacity_lazy as wc  # type: ignore

S08 = Path('assets/structural/scripts')
if str(S08) not in sys.path:
    sys.path.insert(0, str(S08))
import transport_witness_layer as stw  # type: ignore

LUT_PATH = Path('assets/quotients/data/wang_f2_lb20/wang_subspace_lut.pkl')
CACHE_PATH = Path('assets/quotients/data/wang_f2_lb20/wang_orbit_closed_cache.pkl')
OUT = Path('assets/structural/data/quotient_semantics/quotient_occupation_semantics.json')


def reduce_mod_U(v: int, basis) -> int:
    x = int(v)
    for row in basis:
        row = int(row)
        if row and ((x >> (row.bit_length() - 1)) & 1):
            x ^= row
    return x


def quotient_image_basis(basis):
    imgs = [reduce_mod_U(1 << i, basis) for i in range(9)]
    return wc.rref_basis(imgs, n=9)


def main():
    t0 = time.time()
    lut_obj = pickle.load(open(LUT_PATH, 'rb'))
    lut = {int(k): int(v) for k, v in (lut_obj['lut'] if isinstance(lut_obj, dict) and 'lut' in lut_obj else lut_obj).items()}
    cache = pickle.load(open(CACHE_PATH, 'rb'))
    dim2_rows, _ = stw.collect_dim2_core_rows(lut, cache)
    line_rows = stw.collect_line_keys(cache)
    plane_rows, _ = stw.collect_affine_plane_keys(lut, cache)
    used = {}
    for r in dim2_rows:
        used[int(r['U_key'])] = tuple(int(x) for x in r['U_basis'])
    for r in line_rows:
        used[int(r['key'])] = tuple(wc.unpack_basis(int(r['key'])))
    for r in plane_rows:
        used[int(r['U_key'])] = tuple(int(x) for x in r['U_basis'])
    failures = []
    image_dim_hist = Counter()
    dim_hist = Counter()
    for key, basis in used.items():
        d = len(basis)
        dim_hist[d] += 1
        images = {reduce_mod_U(v, basis) for v in range(512)}
        img_basis = quotient_image_basis(basis)
        image_dim_hist[len(img_basis)] += 1
        if len(images) != (1 << (9 - d)) or len(img_basis) != 9 - d:
            failures.append({'key': key, 'basis': list(basis), 'reason': 'bad_image_size_or_rank', 'image_size': len(images), 'image_rank': len(img_basis), 'expected_rank': 9-d})
            if len(failures) >= 20: break
        for v in range(512):
            inU = wc.in_rowspace(v, basis, n=9)
            killed = reduce_mod_U(v, basis) == 0
            if inU != killed:
                failures.append({'key': key, 'basis': list(basis), 'v': v, 'in_rowspace': inU, 'quotient_killed': killed, 'reduced': reduce_mod_U(v,basis)})
                break
        if len(failures) >= 20: break
    out = {
        'schema': 's0908_quotient_occupation_semantics_v1',
        'meaning': 'For every proof-used A-subspace U, the quotient map represented by the Wang RREF substitution kills exactly the A-vectors in U. Hence a lower bound L for q_U(T) gives the occupation inequality #terms with A_t in U <= s-L for any s-term decomposition.',
        'used_unique_subspace_count': len(used),
        'input_instance_counts': {'dim2_core_rows': len(dim2_rows), 'line_rows': len(line_rows), 'affine_plane_rows': len(plane_rows)},
        'subspace_dimension_hist': {str(k): int(v) for k,v in sorted(dim_hist.items())},
        'quotient_image_dimension_hist': {str(k): int(v) for k,v in sorted(image_dim_hist.items())},
        'failure_count': len(failures),
        'failures_head': failures[:20],
        'all_ok': len(failures) == 0,
        'mathematical_statement_checked': 'q_U is reduction modulo the RREF rowspace U; for all a in F2^9, q_U(a)=0 iff a in U. Applying q_U to each A factor of a rank-one term kills exactly the terms counted by the occupation row.',
        'elapsed_sec': time.time() - t0,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'status': 'ok', 'out': str(OUT), 'all_ok': out['all_ok'], 'used_unique_subspace_count': len(used), 'failure_count': len(failures), 'elapsed_sec': out['elapsed_sec']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
