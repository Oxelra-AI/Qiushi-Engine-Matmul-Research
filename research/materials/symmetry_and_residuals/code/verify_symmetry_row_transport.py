#!/usr/bin/env python3
"""analysis: verify row transport for the fixed-repeat E11-core certificate.

The fixed p=1 DRAT proof uses selected Wang rows.  To cover any repeated
capacity-two direction p, the E11-stabilizer must transport a hypothetical
complete-Wang solution with p repeated to one with p=1 repeated, and the selected
rows used in the p=1 proof must remain valid complete-core rows under this
transport.  This script checks that explicitly for the selected 262 Wang rows.
"""
from __future__ import annotations
import json, pickle, sys, time
from collections import Counter
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient
from complete_core_and_transversal import ROOT, build_core_constraints
from core_repeat_symmetry_and_cnf import build_action_images_with_flag, induced_core_permutation, label8, sha256
from wang_capacity_lazy import pack_basis, rref_basis, transform_mask, unpack_basis

OUTDIR = ROOT / 'workspace/data/repeat_branch_certificate'


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}, payload.get('meta', {})


def image_key8(key8: int, perm):
    rows = unpack_basis(key8)
    im_rows = [perm[r - 1] for r in rows]
    return pack_basis(rref_basis(im_rows, n=8))


def inverse_perm(perm):
    inv = [0] * 255
    for i, q in enumerate(perm, start=1):
        inv[q - 1] = i
    return tuple(inv)


def main():
    t0 = time.time()
    core = CoreQuotient(1)
    lut, _ = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records, meta = build_core_constraints(core, lut)
    by_key = {int(r['key8']): r for r in records}

    shrink_path = OUTDIR / 'iis_shrink_p1/shrink_summary.json'
    shrink = json.loads(shrink_path.read_text())
    selected = [r for r in shrink['selected_constraint_records'] if r['kind'] == 'wang']
    selected_keys = [int(r['key8']) for r in selected]
    if len(selected_keys) != shrink['selected_constraint_count']:
        raise AssertionError('non-Wang selected constraint in shrunken proof')

    # Recompute all induced E11-stabilizer permutations.
    actions = build_action_images_with_flag()
    perms = []
    seen = set()
    for img, tr in actions:
        if transform_mask(core.pivot, img) != core.pivot:
            continue
        p = induced_core_permutation(core, img)
        if p not in seen:
            seen.add(p)
            perms.append(p)
    cap2 = [1, 2, 3, 4, 32, 36]

    # Witness maps taking each repeated direction to p=1.
    witnesses = {}
    for p in cap2:
        for idx, perm in enumerate(perms):
            if perm[p - 1] == 1:
                witnesses[p] = idx
                break
        else:
            raise AssertionError(f'no map sends {p} to 1')

    # Check every selected row transported by every stabilizer element stays in the core table with same L.
    violations = []
    transported_dim_counter = Counter()
    for key in selected_keys:
        L0 = int(by_key[key]['L'])
        for perm in perms:
            im = image_key8(key, perm)
            rec = by_key.get(im)
            if rec is None or int(rec['L']) != L0:
                violations.append({'key8': key, 'image_key8': im, 'L0': L0, 'L_image': None if rec is None else int(rec['L'])})
                break
            transported_dim_counter[int(rec['dim8'])] += 1

    # Check the exact witness maps needed for coverage, both image and preimage of selected rows.
    witness_checks = {}
    for p, idx in witnesses.items():
        perm = perms[idx]
        inv = inverse_perm(perm)
        bad = []
        for key in selected_keys:
            L0 = int(by_key[key]['L'])
            for tag, pp in [('image', perm), ('preimage', inv)]:
                kk = image_key8(key, pp)
                rec = by_key.get(kk)
                if rec is None or int(rec['L']) != L0:
                    bad.append({'tag': tag, 'key8': key, 'transported': kk, 'L0': L0, 'L1': None if rec is None else int(rec['L'])})
                    break
            if bad:
                break
        witness_checks[str(p)] = {
            'label': label8(core, p),
            'perm_index': idx,
            'maps_p_to': perm[p - 1],
            'maps_p_to_label': label8(core, perm[p - 1]),
            'selected_rows_image_and_preimage_preserve_L': not bad,
            'bad_head': bad[:3],
        }

    out = {
        'schema': 'symmetry_row_transport_check_v1',
        'field': 'F2',
        'core': 'E11',
        'selected_proof_rows_source': str(shrink_path),
        'selected_proof_rows_source_sha256': sha256(shrink_path),
        'selected_wang_rows': len(selected_keys),
        'selected_rows_by_dim': {str(k): int(v) for k, v in sorted(Counter(int(r['dim8']) for r in selected).items())},
        'selected_rows_by_L': {str(k): int(v) for k, v in sorted(Counter(int(r['L']) for r in selected).items())},
        'unique_induced_stabilizer_perms': len(perms),
        'capacity_two_points': cap2,
        'capacity_two_labels': {str(p): label8(core, p) for p in cap2},
        'witness_maps_to_p1': witness_checks,
        'all_selected_rows_preserve_L_under_all_stabilizer_perms': len(violations) == 0,
        'transport_violations_head': violations[:5],
        'transported_dim_counter_total': sum(transported_dim_counter.values()),
        'complete_core_table_meta': meta,
        'interpretation': 'The selected p=1 Wang rows remain valid complete-core Wang rows under the induced E11 stabilizer. Thus a complete-Wang solution with any capacity-two repeated direction can be transported to the fixed p=1 contradiction.',
        'elapsed_sec': round(time.time() - t0, 3),
    }
    path = OUTDIR / 'symmetry_row_transport_check.json'
    path.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(path),
        'selected_rows': len(selected_keys),
        'perms': len(perms),
        'all_preserve': out['all_selected_rows_preserve_L_under_all_stabilizer_perms'],
        'witnesses_ok': all(w['selected_rows_image_and_preimage_preserve_L'] for w in witness_checks.values()),
        'elapsed': out['elapsed_sec'],
    }, sort_keys=True))

if __name__ == '__main__':
    main()
