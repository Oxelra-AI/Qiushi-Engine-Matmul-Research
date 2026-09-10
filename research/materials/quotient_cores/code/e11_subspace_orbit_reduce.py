#!/usr/bin/env python3
"""Reduce complete E11 Wang occupation subspaces into corrected quotient-action orbits.

The point action was verified in analysis.  This script lifts it to subspaces of
F2^8 by acting on nonzero point masks, computes orbit representatives using the
8 subgroup-generator permutations, and checks that every orbit has constant Wang
L and capacity.  The output is a replayable compact description of the complete
occupation constraint family: representative mask/key/cap plus the full orbit of
cache indices.
"""
from __future__ import annotations

import argparse, json, pickle, sys, time, hashlib
from collections import Counter, deque, defaultdict
from pathlib import Path

import numpy as np

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))
from e11_capacity_incremental_sat import build_or_load_constraint_cache, mask_to_points  # noqa: E402
from e11_quotient_action_verify import I3, P_row_stabilizer_generators, Q_col_stabilizer_generators, perm_for_pair  # noqa: E402


def transform_mask(mask: int, perm: tuple[int, ...]) -> int:
    out = 0
    x = int(mask)
    while x:
        lb = x & -x
        p = lb.bit_length()
        out |= 1 << (int(perm[p]) - 1)
        x ^= lb
    return out


def gen_perms():
    I = I3()
    return [perm_for_pair(P, I) for P in P_row_stabilizer_generators()] + [perm_for_pair(I, Q) for Q in Q_col_stabilizer_generators()]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cache', type=Path, default=Path('data/e11_capacity_sat/e11_capacity_cache.pkl'))
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=19)
    ap.add_argument('--outdir', type=Path, default=Path('data/e11_subspace_orbits'))
    ap.add_argument('--rebuild-cache', action='store_true')
    args = ap.parse_args()
    t0 = time.time()
    cache = build_or_load_constraint_cache(args.lut, args.cache, args.rank, args.rebuild_cache)
    masks = [int(x) for x in cache['masks']]
    mask_to_idx = {m:i for i,m in enumerate(masks)}
    if len(mask_to_idx) != len(masks):
        raise SystemExit('subspace masks are not unique')
    perms = gen_perms()
    if len(perms) != 8:
        raise SystemExit(f'expected 8 generator perms, got {len(perms)}')
    n = len(masks)
    visited = np.zeros(n, dtype=np.uint8)
    orbit_id = np.full(n, -1, dtype=np.int32)
    orbits = []
    failures = []
    for start in range(n):
        if visited[start]:
            continue
        oid = len(orbits)
        q = deque([start]); visited[start] = 1; members = []
        while q:
            i = q.popleft(); members.append(i); orbit_id[i] = oid
            m = masks[i]
            for perm in perms:
                im = transform_mask(m, perm)
                j = mask_to_idx.get(im)
                if j is None:
                    failures.append({'orbit':oid,'index':i,'mask':m,'image_mask':im,'failure':'image mask missing'})
                    continue
                if not visited[j]:
                    visited[j] = 1; q.append(j)
        caps = Counter(int(cache['caps'][i]) for i in members)
        Ls = Counter(int(cache['Ls'][i]) for i in members)
        dims = Counter(int(cache['dims'][i]) for i in members)
        if len(caps) != 1 or len(Ls) != 1 or len(dims) != 1:
            failures.append({'orbit':oid,'failure':'nonconstant invariant','caps':dict(caps),'Ls':dict(Ls),'dims':dict(dims),'members_head':members[:20]})
        rep = min(members, key=lambda i: (int(cache['dims'][i]), int(cache['caps'][i]), masks[i]))
        orbits.append({'orbit':oid,'size':len(members),'rep_index':int(rep),'rep_key8':int(cache['keys8'][rep]),'rep_mask':int(masks[rep]),'dim8':int(cache['dims'][rep]),'L':int(cache['Ls'][rep]),'cap':int(cache['caps'][rep]),'point_count':int(masks[rep]).bit_count(),'rep_points_head':mask_to_points(masks[rep])[:80],'members':members})
        if oid % 1000 == 0:
            print(f'orbit {oid:,}, visited {int(visited.sum()):,}/{n:,}')
    # save large arrays compactly
    args.outdir.mkdir(parents=True, exist_ok=True)
    npz_path = args.outdir / 'e11_subspace_orbits.npz'
    # Flatten members for replay without huge JSON.
    offsets = [0]
    flat = []
    for o in orbits:
        flat.extend(o['members'])
        offsets.append(len(flat))
    np.savez_compressed(npz_path,
                        orbit_id=orbit_id,
                        offsets=np.array(offsets,dtype=np.int64),
                        flat_members=np.array(flat,dtype=np.int32),
                        rep_indices=np.array([o['rep_index'] for o in orbits],dtype=np.int32))
    digest = hashlib.sha256(npz_path.read_bytes()).hexdigest()
    # JSON summary without all members.
    summary_orbits = []
    for o in orbits:
        oo = {k:v for k,v in o.items() if k != 'members'}
        summary_orbits.append(oo)
    dist = Counter((o['dim8'], o['cap']) for o in summary_orbits)
    size_dist = Counter(o['size'] for o in summary_orbits)
    result = {'purpose':'Corrected quotient-action orbit decomposition of all E11 Wang occupation subspace constraints',
              'field':'F2','rank_s':args.rank,'cache':str(args.cache),'subspace_count':n,
              'generator_permutations':len(perms),'orbit_count':len(orbits),
              'orbit_size_distribution':dict(sorted(size_dist.items())),
              'orbit_dim_cap_distribution':{str(k):v for k,v in sorted(dist.items())},
              'constant_L_cap_dim_on_orbits':len(failures)==0,'failures_head':failures[:20],
              'npz_path':str(npz_path),'npz_sha256':digest,
              'orbits_head':summary_orbits[:100],
              'elapsed_sec':time.time()-t0,
              'meaning':'The complete 417,199 E11 occupation constraints can be regenerated from these orbit representatives and the verified 8 quotient-action generator permutations; this is a compact replay surface, not by itself a rank lower bound.'}
    json_path = args.outdir / 'e11_subspace_orbit_summary.json'
    json_path.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k:result[k] for k in ['subspace_count','orbit_count','orbit_size_distribution','constant_L_cap_dim_on_orbits','elapsed_sec','npz_sha256']}, indent=2, sort_keys=True))
    print(f'wrote {json_path}')
    if failures:
        raise SystemExit('subspace orbit invariance failures')

if __name__ == '__main__':
    main()
