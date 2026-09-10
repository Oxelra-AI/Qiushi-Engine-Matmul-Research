#!/usr/bin/env python3
"""Stabilizer/orbit analysis for the 16 surviving high-rank coset H configurations."""
from __future__ import annotations
import json, sys, time
from pathlib import Path
from itertools import combinations
from collections import defaultdict, deque
SCRIPT=Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path: sys.path.insert(0,str(SCRIPT))
from quotient_line_caps_and_controls import gl3, transform_term  # type: ignore
from surviving_coset_ansatz import canonical_coset_points, h_to_firstrows  # type: ignore


def transform_A(a:int,P,Q):
    return transform_term((a,1,1),P,Q)[0]

def span_set(gens):
    out={0}
    for g in gens:
        out |= {x^g for x in list(out)}
    return set(out)

def main():
    out_path=Path('data/coset_analysis/coset_h_symmetry.json')
    t0=time.time(); G=gl3(); p,coset,rank2,rank3=canonical_coset_points()
    S=span_set([p,1,2,4]); coset_set=set(coset)
    Hs=[frozenset(list(c2)+list(c3)) for c2 in combinations(rank2,1) for c3 in combinations(rank3,3)]
    Hs=sorted(Hs,key=lambda H:h_to_firstrows(sorted(H),p)); H_index={H:i for i,H in enumerate(Hs)}
    stab_S=[]; stab_coset=[]; perms=[]; image_pairs=[]
    for i,P in enumerate(G):
        for j,Q in enumerate(G):
            imgS={transform_A(x,P,Q) for x in S}
            if imgS==S:
                stab_S.append((i,j))
                imgcos={transform_A(x,P,Q) for x in coset_set}
                if imgcos==coset_set:
                    stab_coset.append((i,j))
                    perm=[]
                    ok=True
                    for H in Hs:
                        im=frozenset(transform_A(x,P,Q) for x in H)
                        if im in H_index: perm.append(H_index[im])
                        else: ok=False; break
                    if ok:
                        perms.append(tuple(perm)); image_pairs.append((i,j))
    # orbit closure on H indices using perms
    seen=set(); orbits=[]
    for a in range(len(Hs)):
        if a in seen: continue
        q=deque([a]); seen.add(a); orb=[]
        while q:
            x=q.popleft(); orb.append(x)
            for perm in perms:
                y=perm[x]
                if y not in seen:
                    seen.add(y); q.append(y)
        orbits.append(sorted(orb))
    rec={
        'schema':'coset_h_symmetry_v1',
        'GL3_size':len(G),
        'total_pairs':len(G)*len(G),
        'S_basis':[p,1,2,4],
        'S_stabilizer_size':len(stab_S),
        'coset_stabilizer_size':len(stab_coset),
        'permutation_count_on_16_H':len(perms),
        'H_count':len(Hs),
        'H_records':[{'index':i,'H':sorted(H),'firstrows':h_to_firstrows(sorted(H),p)} for i,H in enumerate(Hs)],
        'H_orbits_under_stabilizer':orbits,
        'representative_transform_pairs_head':image_pairs[:20],
        'elapsed_sec':time.time()-t0,
    }
    out_path.parent.mkdir(parents=True,exist_ok=True); out_path.write_text(json.dumps(rec,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(out_path),'S_stabilizer_size':len(stab_S),'coset_stabilizer_size':len(stab_coset),'permutation_count':len(perms),'H_orbits':orbits,'elapsed_sec':rec['elapsed_sec']},indent=2,sort_keys=True))
if __name__=='__main__': main()
