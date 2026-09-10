#!/usr/bin/env python3
"""Orbit reduction for possible repeated E11 quotient A-directions.

Uses the saved 576 quotient permutations to classify the repeated-direction
subsets D that survive Wang line/small-subspace caps.  A multiset case with
one extra copy on every p in D can be transformed to the representative D; then
it suffices to enumerate all distinct supports containing that representative
D under residual caps, without further symmetry assumptions.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

PERM_PATH=Path("data/e11_orbits/e11_quotient_orbits_with_perms.perms.npz")
FULLCHECK=Path("data/wang_validation/e11_repeat_subset_fullcheck.json")
OUT=Path("data/wang_validation/e11_repeat_subset_orbits.json")

def image(sub, perm):
    return tuple(sorted(int(perm[x]) for x in sub))

def main():
    perms=np.load(PERM_PATH)['perms']
    data=json.loads(FULLCHECK.read_text())
    possible=[tuple(r['D']) for r in data['possible_sets'] if r['D']]
    possible_set=set(possible)
    unseen=set(possible)
    orbits=[]
    while unseen:
        seed=min(unseen, key=lambda x:(len(x),x))
        orb=set()
        stack=[seed]
        while stack:
            s=stack.pop()
            if s in orb: continue
            orb.add(s)
            for p in perms:
                y=image(s,p)
                # The group image of a possible set should also be possible.
                if y not in orb: stack.append(y)
        rep=min(orb, key=lambda x:(len(x),x))
        orbits.append({'rep':list(rep),'size':len(orb),'members':[list(x) for x in sorted(orb, key=lambda x:(len(x),x))],'all_members_possible':all(x in possible_set for x in orb)})
        unseen-=orb
    out={'status':'ok','possible_nonempty_subsets':[list(x) for x in sorted(possible,key=lambda x:(len(x),x))],'orbit_count':len(orbits),'orbits':orbits}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
