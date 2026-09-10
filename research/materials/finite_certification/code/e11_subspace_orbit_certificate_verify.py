#!/usr/bin/env python3
"""Replay-check the E11 subspace-orbit occupation proof surface.

This verifier does not solve the E11 rank-19 problem.  It checks that the analysis
compressed orbit object faithfully represents all 417,199 Wang-derived subspace
occupation constraints under the corrected E11 quotient action.
"""
from __future__ import annotations

import argparse, hashlib, json, pickle, sys, time
from collections import Counter, deque
from pathlib import Path

import numpy as np

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))
from e11_capacity_incremental_sat import build_or_load_constraint_cache, mask_to_points  # noqa: E402
from e11_subspace_orbit_reduce import gen_perms, transform_mask  # noqa: E402


def stable_hash_ints(vals):
    h = hashlib.sha256()
    for v in vals:
        n = int(v)
        blen = max(1, (n.bit_length() + 7) // 8)
        h.update(blen.to_bytes(2, 'little', signed=False))
        h.update(n.to_bytes(blen, 'little', signed=False))
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cache', type=Path, default=Path('data/e11_capacity_sat/e11_capacity_cache.pkl'))
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--orbits', type=Path, default=Path('data/e11_subspace_orbits/e11_subspace_orbits.npz'))
    ap.add_argument('--out', type=Path, default=Path('data/e11_subspace_orbits/e11_subspace_orbit_certificate_check.json'))
    ap.add_argument('--rank', type=int, default=19)
    args = ap.parse_args()
    t0 = time.time()
    cache = build_or_load_constraint_cache(args.lut, args.cache, args.rank)
    masks = [int(x) for x in cache['masks']]
    mask_to_idx = {m:i for i,m in enumerate(masks)}
    data = np.load(args.orbits)
    orbit_id = data['orbit_id'].astype(np.int64)
    offsets = data['offsets'].astype(np.int64)
    flat = data['flat_members'].astype(np.int64)
    rep_indices = data['rep_indices'].astype(np.int64)
    N = len(masks)
    errors = []
    coverage_ok = (len(orbit_id) == N and len(flat) == N and sorted(int(x) for x in flat.tolist()) == list(range(N)))
    if not coverage_ok:
        errors.append({'failure':'flat member coverage mismatch','N':N,'orbit_id_len':len(orbit_id),'flat_len':len(flat)})
    if len(offsets) != len(rep_indices) + 1:
        errors.append({'failure':'offset/rep length mismatch','offsets':len(offsets),'reps':len(rep_indices)})
    perms = gen_perms()
    replay_orbit_sizes = []
    cap_dim_L_constant = True
    member_match_ok = True
    image_missing = []
    for oid, rep in enumerate(rep_indices.tolist()):
        stored = set(int(x) for x in flat[offsets[oid]:offsets[oid+1]].tolist())
        q = deque([int(rep)]); seen = {int(rep)}
        while q:
            i = q.popleft()
            for perm in perms:
                im = transform_mask(masks[i], perm)
                j = mask_to_idx.get(im)
                if j is None:
                    image_missing.append({'orbit':oid,'index':int(i),'image_mask':int(im)})
                    continue
                if j not in seen:
                    seen.add(j); q.append(j)
        if seen != stored:
            member_match_ok = False
            errors.append({'failure':'replayed orbit differs from stored orbit','orbit':oid,'rep_index':int(rep),'stored_size':len(stored),'replayed_size':len(seen),'missing_head':sorted(stored-seen)[:20],'extra_head':sorted(seen-stored)[:20]})
            if len(errors) > 20:
                break
        caps = Counter(int(cache['caps'][i]) for i in seen)
        dims = Counter(int(cache['dims'][i]) for i in seen)
        Ls = Counter(int(cache['Ls'][i]) for i in seen)
        if len(caps) != 1 or len(dims) != 1 or len(Ls) != 1:
            cap_dim_L_constant = False
            errors.append({'failure':'nonconstant invariant on replayed orbit','orbit':oid,'caps':dict(caps),'dims':dict(dims),'Ls':dict(Ls)})
        replay_orbit_sizes.append(len(seen))
    # Verify orbit_id agrees with flat/offets for every stored member.
    orbit_id_ok = True
    if len(errors) <= 20:
        for oid in range(len(rep_indices)):
            for idx in flat[offsets[oid]:offsets[oid+1]]:
                if int(orbit_id[int(idx)]) != oid:
                    orbit_id_ok = False
                    errors.append({'failure':'orbit_id mismatch','orbit':oid,'index':int(idx),'orbit_id_value':int(orbit_id[int(idx)])})
                    break
            if not orbit_id_ok:
                break
    # Stable digests for independent comparison.
    constraint_digest_vals = []
    for i in range(N):
        constraint_digest_vals.extend([int(cache['keys8'][i]), int(cache['dims'][i]), int(cache['Ls'][i]), int(cache['caps'][i]), int(cache['masks'][i])])
    rep_digest_vals = []
    for rep in rep_indices.tolist():
        rep_digest_vals.extend([int(cache['keys8'][rep]), int(cache['dims'][rep]), int(cache['Ls'][rep]), int(cache['caps'][rep]), int(cache['masks'][rep])])
    result = {
        'purpose':'Replay verification of compressed E11 Wang occupation subspace-orbit object',
        'field':'F2','rank_s':args.rank,'cache':str(args.cache),'orbits_npz':str(args.orbits),
        'subspace_count':N,'orbit_count':int(len(rep_indices)),'generator_permutations':len(perms),
        'flat_covers_each_subspace_once':coverage_ok,
        'stored_orbits_equal_generator_closure_from_reps':member_match_ok,
        'orbit_id_matches_offsets':orbit_id_ok,
        'all_replayed_images_found':not image_missing,
        'constant_dim_L_cap_on_replayed_orbits':cap_dim_L_constant,
        'orbit_size_distribution':dict(sorted(Counter(replay_orbit_sizes).items())),
        'constraint_table_sha256':stable_hash_ints(constraint_digest_vals),
        'orbit_representative_table_sha256':stable_hash_ints(rep_digest_vals),
        'npz_file_sha256':hashlib.sha256(args.orbits.read_bytes()).hexdigest(),
        'errors_head':errors[:20],
        'elapsed_sec':time.time()-t0,
        'meaning':'If all checks are true, the 1,496 representatives plus the verified quotient generator permutations replay the complete 417,199 E11 Wang occupation constraints with constant L/cap on each orbit.'
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k:result[k] for k in ['subspace_count','orbit_count','flat_covers_each_subspace_once','stored_orbits_equal_generator_closure_from_reps','orbit_id_matches_offsets','all_replayed_images_found','constant_dim_L_cap_on_replayed_orbits','npz_file_sha256','constraint_table_sha256','orbit_representative_table_sha256','elapsed_sec']}, indent=2, sort_keys=True))
    print(f'wrote {args.out}')
    if errors or not (coverage_ok and member_match_ok and orbit_id_ok and not image_missing and cap_dim_L_constant):
        raise SystemExit('certificate check failed')

if __name__ == '__main__': main()
