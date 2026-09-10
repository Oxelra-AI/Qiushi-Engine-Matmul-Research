#!/usr/bin/env python3
"""analysis: orbit structure of the annihilator subspaces behind near-miss violations."""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Iterable, Sequence

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints  # noqa: E402
from core_repeat_symmetry_and_cnf import build_action_images_with_flag, induced_core_permutation  # noqa: E402
from wang_capacity_lazy import pack_basis, rref_basis, subspace_points_from_basis, unpack_basis  # noqa: E402

OUTDIR = ROOT / 'workspace/data/hybrid_annihilator'
S=19


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}, payload.get('meta', {})


def dot(q:int,p:int)->int:
    return (int(q)&int(p)).bit_count() & 1


def annihilator_points(basis: Sequence[int], n:int=8):
    return [q for q in range(1,1<<n) if all(dot(q,b)==0 for b in basis)]


def D_key(D: Sequence[int]) -> int:
    return pack_basis(rref_basis(D,n=8))


def primal_perm_to_dual_perm(g: Sequence[int]) -> tuple[int,...]:
    # columns are images of the eight basis vectors under the primal map.
    cols=[int(g[(1<<i)-1]) for i in range(8)]
    sig_to_mask={}
    for m in range(256):
        sig=0
        for i,c in enumerate(cols):
            if dot(m,c): sig |= 1<<i
        sig_to_mask[sig]=m
    if len(sig_to_mask)!=256:
        raise AssertionError('dual signature map not bijective')
    return tuple(sig_to_mask[q] for q in range(1,256))


def transform_D_key(key:int, dual_perm: Sequence[int]) -> int:
    pts=subspace_points_from_basis(unpack_basis(key))
    im=[int(dual_perm[q-1]) for q in pts]
    return D_key(im)


def orbit(seed:int, perms: Sequence[Sequence[int]]) -> list[int]:
    seen={int(seed)}; dq=deque([int(seed)])
    while dq:
        k=dq.popleft()
        for dp in perms:
            im=transform_D_key(k, dp)
            if im not in seen:
                seen.add(im); dq.append(im)
    return sorted(seen)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--analysis', type=Path, default=ROOT/'workspace/data/hybrid_annihilator/analysis_L15_support.json')
    ap.add_argument('--out', type=Path, default=OUTDIR/'dual_violation_orbits.json')
    args=ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0=time.time()

    core=CoreQuotient(1)
    actions=build_action_images_with_flag()
    stab=[(img,tr) for img,tr in actions if __import__('wang_capacity_lazy').transform_mask(core.pivot,img)==core.pivot]
    primal=[]; seen=set()
    for img,tr in stab:
        g=induced_core_permutation(core,img)
        if g not in seen:
            seen.add(g); primal.append(g)
    dual=[primal_perm_to_dual_perm(g) for g in primal]
    if len(set(dual))!=len(dual):
        dual=list(dict.fromkeys(dual))

    d=json.loads(args.analysis.read_text())
    rows=d['annihilator_identity_analysis']['violations']
    row_infos=[]
    for i,r in enumerate(rows):
        key=int(r['D_key'])
        row_infos.append({
            'i':i,
            'dim8':int(r['dim8']),
            'dual_k':int(r['codim_dual_k']),
            'L':int(r['L']),
            'D_key':key,
            'D_basis':r['D_basis'],
            'D_nonzero':r['D_nonzero'],
            'annihilator_deficit':int(r['annihilator_deficit']),
            'weight_pattern': dict(Counter(int(qw['w']) for qw in r['q_weights'])),
            'rank_pattern': dict(Counter(int(qw['rank_Lq']) for qw in r['q_weights'])),
        })

    remaining={ri['D_key'] for ri in row_infos}
    row_orbits=[]
    while remaining:
        seed=min(remaining)
        orb=orbit(seed,dual)
        hit=sorted(remaining.intersection(orb))
        row_orbits.append({
            'seed_D_key':seed,
            'seed_D_basis':list(unpack_basis(seed)),
            'orbit_size_all_dual_stabilizer':len(orb),
            'violating_D_keys_in_this_orbit':hit,
            'hit_count_among_12':len(hit),
            'hit_rows':[ri for ri in row_infos if ri['D_key'] in hit],
        })
        remaining-=set(hit)

    # For each violating dual 3-plane, record all contained violating dual lines and all dual lines.
    key_to_set={ri['D_key']:set(subspace_points_from_basis(unpack_basis(ri['D_key']))) for ri in row_infos}
    contain=[]
    lines=[ri for ri in row_infos if ri['dual_k']==2]
    planes=[ri for ri in row_infos if ri['dual_k']==3]
    for pl in planes:
        ps=key_to_set[pl['D_key']]
        all_lines=[]
        for a in sorted(ps):
            for b in sorted(ps):
                if a<b:
                    lk=D_key([a,b])
                    if (lk & 0xF)==2 and lk not in all_lines:
                        all_lines.append(lk)
        contain.append({
            'plane_D_key':pl['D_key'],
            'plane_D_basis':pl['D_basis'],
            'all_2D_subspace_keys_in_plane':sorted(all_lines),
            'violating_line_keys_inside':sorted([ln['D_key'] for ln in lines if key_to_set[ln['D_key']].issubset(ps)]),
        })

    out={
        'schema':'dual_violation_orbits_v1',
        'field':'F2','core':'E11','rank_s':19,
        'analysis_source':str(args.analysis),
        'unique_primal_stabilizer_permutations':len(primal),
        'unique_dual_stabilizer_permutations':len(dual),
        'row_count':len(row_infos),
        'row_summary_by_dual_k':{str(k):int(v) for k,v in sorted(Counter(ri['dual_k'] for ri in row_infos).items())},
        'row_infos':row_infos,
        'orbits_meeting_12_violating_Ds':row_orbits,
        'plane_line_containment':contain,
        'interpretation':'The twelve near-miss Wang violations are represented by their annihilator dual subspaces D. Orbits use the contragredient action induced by the standard E11 stabilizer on the quotient core.',
        'elapsed_sec':round(time.time()-t0,3),
    }
    args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(args.out),'orbits':len(row_orbits),'dual_perms':len(dual),'elapsed_sec':out['elapsed_sec']},sort_keys=True))

if __name__=='__main__':
    main()
