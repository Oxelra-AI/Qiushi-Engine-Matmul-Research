#!/usr/bin/env python3
"""Hash and consistency manifest for analysis E11 proof-surface artifacts."""
from __future__ import annotations

import hashlib
import json
import pickle
import sys
import time
from collections import deque
from pathlib import Path

import numpy as np

SCRIPTS_A02 = Path('scripts')
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))

from e11_subspace_orbit_reduce import gen_perms  # noqa: E402


def sha256_file(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def array_hash(arr: np.ndarray) -> str:
    a = np.ascontiguousarray(arr)
    return hashlib.sha256(a.tobytes()).hexdigest()


def cache_arrays_hash(cache: dict) -> str:
    h = hashlib.sha256()
    for key, dtype in [('keys8', object), ('masks', object), ('caps', np.int16), ('Ls', np.int16), ('dims', np.int16)]:
        vals = cache[key]
        h.update(key.encode() + b'\0')
        if key in ('keys8', 'masks'):
            # Packed bases/masks may exceed uint64. Store each as decimal plus delimiter in cache order.
            for x in vals:
                h.update(str(int(x)).encode() + b'\n')
        else:
            h.update(np.ascontiguousarray(vals, dtype=dtype).tobytes())
    return h.hexdigest()


def recompute_membership_hash(masks: list[int], shape: tuple[int, int]) -> tuple[str, bool]:
    M = np.zeros(shape, dtype=np.uint8)
    for i, m0 in enumerate(masks):
        m = int(m0)
        while m:
            lb = m & -m
            p = lb.bit_length()
            M[p, i] = 1
            m ^= lb
    return array_hash(M), True


def compose_perm(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    # q after p: x -> q[p[x]]
    return tuple(q[p[i]] for i in range(len(p)))


def verify_perm_group(perms_arr: np.ndarray) -> dict:
    perms = [tuple(int(x) for x in row.tolist()) for row in perms_arr]
    perm_set = set(perms)
    identity = tuple(range(256))
    gens = [tuple(int(x) for x in g) for g in gen_perms()]
    q = deque([identity])
    closure = {identity}
    while q:
        cur = q.popleft()
        for g in gens:
            nxt = compose_perm(cur, g)
            if nxt not in closure:
                closure.add(nxt)
                q.append(nxt)
    inverse_ok = True
    # Check each listed perm has inverse in generated closure by mapping inverse row.
    for p in perms:
        inv = [0] * len(p)
        for i, y in enumerate(p):
            inv[y] = i
        if tuple(inv) not in closure:
            inverse_ok = False
            break
    return {
        'perms_shape': list(perms_arr.shape),
        'distinct_rows': len(perm_set),
        'identity_in_rows': identity in perm_set,
        'generator_count': len(gens),
        'generators_in_rows': all(g in perm_set for g in gens),
        'closure_from_generators_size': len(closure),
        'closure_equals_rows': len(closure) == len(perm_set) and closure == perm_set,
        'inverses_in_generated_closure': inverse_ok,
    }


def main():
    t0 = time.time()
    root = Path('research/research_record')
    paths = {
        'core_e11': Path('data/restricted_cores/mask_001_E11_core.npy'),
        'wang_lut': Path('data/wang_f2_lb20/wang_subspace_lut.pkl'),
        'capacity_cache': root / 'workspace/data/e11_capacity_sat/e11_capacity_cache.pkl',
        'membership': root / 'workspace/data/e11_occupation_sat/e11_membership.npy',
        'quotient_perms': root / 'workspace/data/e11_quotient_action/e11_quotient_action_verification.perms.npz',
        'subspace_orbits': root / 'workspace/data/e11_subspace_orbits/e11_subspace_orbits.npz',
        'subspace_orbit_check': root / 'workspace/data/e11_subspace_orbits/e11_subspace_orbit_certificate_check.json',
        'depth4_summary': root / 'workspace/data/e11_canonical_tree/depth4_complete_summary.json',
        'depth4_replay': root / 'workspace/data/e11_canonical_tree/depth4_complete_summary_replay_check.json',
        'depth4_terminal_completeness': root / 'workspace/data/e11_canonical_tree/depth4_complete_summary_terminal_completeness.json',
        'depth4_eliminated': root / 'workspace/data/e11_canonical_tree/depth4_complete_eliminated_prefixes.jsonl',
        'depth4_leaves': root / 'workspace/data/e11_canonical_tree/depth4_complete_occupation_feasible_leaves.jsonl',
        'xor_empty_regression': root / 'workspace/data/e11_fixed_u_xor_tests/empty_xor_regression_summary.json',
        'xor_rank21_control': root / 'workspace/data/e11_fixed_u_xor/rank21_poolrow0_xor_control_rerun_correct_us.json',
        'xor_vector_neg': root / 'workspace/data/e11_fixed_u_xor/vector_local_9viol_xor_rerun.json',
        'xor_local_neg': root / 'workspace/data/e11_fixed_u_xor/local_search_9viol_xor_rerun.json',
        'drat_meta': root / 'workspace/data/e11_fixed_u_drat/local_search_9viol_kissat_drat_meta.json',
        'drat_translation': root / 'workspace/data/e11_fixed_u_drat/local_search_9viol_plain_cnf_translation_verify.json',
        'domain_cpsat_all_tight': root / 'workspace/data/e11_occupation_sat/domain_cpsat_all_tight.json',
    }
    file_hashes = {name: {'path': str(path), 'sha256': sha256_file(path), 'size_bytes': path.stat().st_size if path.exists() else None} for name, path in paths.items()}

    core = np.load(paths['core_e11']).astype(np.uint8) & 1
    with paths['capacity_cache'].open('rb') as f:
        cache = pickle.load(f)
    M = np.load(paths['membership'], mmap_mode=None).astype(np.uint8, copy=False)
    mh_rebuilt, _ = recompute_membership_hash([int(x) for x in cache['masks']], M.shape)
    mh_loaded = array_hash(M)
    perms_arr = np.load(paths['quotient_perms'])['perms'].astype(np.uint16, copy=False)

    result = {
        'purpose': 'analysis E11 artifact hash/consistency manifest',
        'field': 'F2',
        'rank_s': 19,
        'file_hashes': file_hashes,
        'core': {
            'shape': list(core.shape),
            'nnz': int(core.sum()),
            'sha256_raw_uint8': array_hash(core),
        },
        'capacity_cache': {
            'subspace_count': len(cache['masks']),
            'rank_s': cache.get('rank_s'),
            'core_name': cache.get('core_name'),
            'arrays_sha256_ordered': cache_arrays_hash(cache),
            'stats': cache.get('stats'),
            'lut_meta_brief': cache.get('lut_meta_brief'),
        },
        'membership': {
            'shape': list(M.shape),
            'loaded_sha256_raw_uint8': mh_loaded,
            'rebuilt_from_cache_masks_sha256_raw_uint8': mh_rebuilt,
            'matches_cache_masks': mh_loaded == mh_rebuilt,
        },
        'quotient_permutation_group': verify_perm_group(perms_arr),
        'meaning': 'This binds the analysis tree/SAT/proof records to concrete file hashes and checks that the membership matrix and quotient action are reconstructed from their defining cache/generators. It is evidence infrastructure, not a rank result.',
        'elapsed_sec': time.time() - t0,
    }
    out = root / 'workspace/data/e11_manifest/e11_artifact_manifest.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True, default=str) + '\n')
    print(json.dumps({
        'core_hash': result['core']['sha256_raw_uint8'],
        'cache_arrays_hash': result['capacity_cache']['arrays_sha256_ordered'],
        'membership_matches_cache_masks': result['membership']['matches_cache_masks'],
        'perm_group': result['quotient_permutation_group'],
        'out': str(out),
        'elapsed_sec': result['elapsed_sec'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
