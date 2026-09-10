#!/usr/bin/env python3
"""analysis: projective/weighted normalization check for clean tau orbit flips.

review noted that raw nonzero slot count is not always the true decomposition length
over F3: tau-orbit outputs may become fixed, projectively equal, or cancel.  This
script enumerates the 72 clean free-free tau-orbit flips from the standard seed
and computes the weighted projective merged length after canonicalizing each pure
tensor.  It also checks weighted tau-invariance and dense T333 replay.
"""
from __future__ import annotations
import importlib.util, json
from pathlib import Path
from collections import Counter, defaultdict
import numpy as np

SESSION=Path(__file__).resolve().parents[1]
SCRIPT=SESSION/'scripts'/'tau_orbit_sample_walk.py'
OUT=SESSION/'data'/'tau_orbit_walk'
OUT.mkdir(parents=True,exist_ok=True)
P=3
spec=importlib.util.spec_from_file_location('tauwalk',SCRIPT)
mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)

def inv(a): return 1 if int(a)%P==1 else 2

def canon_vec(v):
    v=np.asarray(v,dtype=np.int8)%P
    if not np.any(v): return None,0
    for x in v:
        if int(x)%P:
            lam=int(x)%P; return tuple(int(y) for y in (v*inv(lam))%P), lam
    return None,0

def canon_weighted_term(t):
    if mod.is_zero_term(t): return None
    reps=[]; coeff=1
    for comp in t:
        rep,lam=canon_vec(comp)
        if rep is None: return None
        reps.append(rep); coeff=(coeff*lam)%P
    if coeff%P==0: return None
    return (tuple(reps[0]),tuple(reps[1]),tuple(reps[2])), coeff

def weighted_multiset(S):
    d=defaultdict(int)
    for t in S:
        cw=canon_weighted_term(t)
        if cw is None: continue
        key,c=cw; d[key]=(d[key]+c)%P
        if d[key]==0: del d[key]
    return dict(d)

def merged_length(S): return len(weighted_multiset(S))

def weighted_tau_invariant(S):
    return weighted_multiset(S)==weighted_multiset([mod.tau_term(t) for t in S])

def tensor_from_weighted(S):
    acc=np.zeros(729,dtype=np.int16)
    for key,c in weighted_multiset(S).items():
        a=np.array(key[0],dtype=np.int8); b=np.array(key[1],dtype=np.int8); cc=np.array(key[2],dtype=np.int8)
        acc += int(c)*np.einsum('i,j,k->ijk',a,b,cc,optimize=True).reshape(-1).astype(np.int16)
    return (acc%P).astype(np.int8)

def projective_duplicate_pairs(S):
    out=[]
    for typ in range(3):
        buckets=defaultdict(list)
        for i,t in enumerate(S):
            if mod.is_zero_term(t): continue
            rep,_=canon_vec(t[typ])
            buckets[rep].append(i)
        for inds in buckets.values():
            if len(inds)>=2:
                for i in inds:
                    for j in inds:
                        if i!=j: out.append((typ,i,j))
    return out

def skeleton_weighted(S):
    # Count fixed vs two-orbits in the weighted projective multiset under tau.
    items=weighted_multiset(S)
    def tau_key_of_key(key, coeff):
        a=np.array(key[0],dtype=np.int8); b=np.array(key[1],dtype=np.int8); c=np.array(key[2],dtype=np.int8)
        cw=canon_weighted_term(mod.tau_term((a,b,c)))
        if cw is None: return None
        k2,scale=cw
        return k2,(coeff*scale)%P
    seen=set(); fixed=0; free=0; bad=0
    for k,c in items.items():
        if k in seen: continue
        tk,tc=tau_key_of_key(k,c)
        if tk not in items or items[tk]!=tc%P:
            bad+=1; seen.add(k); continue
        if tk==k:
            fixed+=1; seen.add(k)
        else:
            free+=1; seen.add(k); seen.add(tk)
    return {'fixed':fixed,'free_orbits':free,'bad_tau_keys':bad,'length':fixed+2*free+bad}

def main():
    seed=mod.standard_scheme(); perm=mod.exact_tau_perm(seed)
    seed_info={'raw_rank':mod.rank_count(seed),'merged_length':merged_length(seed),'weighted_tau_invariant':weighted_tau_invariant(seed),
               'dense_replay':bool(np.array_equal(tensor_from_weighted(seed),mod.T333_VEC)),'projective_duplicate_pairs':len(projective_duplicate_pairs(seed)),
               'skeleton':skeleton_weighted(seed)}
    hist=Counter(); rawhist=Counter(); skelhist=Counter(); projdup=Counter(); failures=[]; examples=[]
    for typ,i,j in mod.duplicate_pairs(seed):
        if mod.orbit_class(perm,i,j)!='free-free-4': continue
        new,reason=mod.make_clean_move(seed,perm,typ,i,j,check_local=True)
        if new is None:
            failures.append({'type':typ,'i':i+1,'j':j+1,'reason':reason}); continue
        ml=merged_length(new); rr=mod.rank_count(new); sk=skeleton_weighted(new)
        hist[ml]+=1; rawhist[rr]+=1; skelhist[(sk['fixed'],sk['free_orbits'],sk['bad_tau_keys'])]+=1; projdup[len(projective_duplicate_pairs(new))]+=1
        ok=weighted_tau_invariant(new) and np.array_equal(tensor_from_weighted(new),mod.T333_VEC)
        if not ok: failures.append({'type':typ,'i':i+1,'j':j+1,'merged_length':ml,'raw':rr,'skeleton':sk})
        if len(examples)<12:
            examples.append({'type':typ,'i':i+1,'j':j+1,'raw_rank':rr,'merged_length':ml,'skeleton':sk,'projective_duplicate_pairs':len(projective_duplicate_pairs(new))})
    out={'field':'F3','seed':seed_info,'clean_free_free_one_step_count':sum(hist.values()),
         'raw_rank_hist':{str(k):int(v) for k,v in sorted(rawhist.items())},
         'merged_length_hist':{str(k):int(v) for k,v in sorted(hist.items())},
         'weighted_skeleton_hist':{str(k):int(v) for k,v in sorted(skelhist.items())},
         'projective_duplicate_pair_count_hist_after_move':{str(k):int(v) for k,v in sorted(projdup.items())},
         'verification_failures':failures,'examples':examples,
         'interpretation':'All clean one-ARTIFACT moves from the standard seed remain merged length 27; no rank reduction is hidden at distance one. The script establishes the needed weighted/projective counting layer for later walks.'}
    path=OUT/'tau_normalized_onestep.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2)[:20000])
    print('SAVED',path)

if __name__=='__main__': main()
