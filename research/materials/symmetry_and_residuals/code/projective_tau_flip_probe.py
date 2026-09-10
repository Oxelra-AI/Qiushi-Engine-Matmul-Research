#!/usr/bin/env python3
"""analysis: projective-gauge tau-flip probe around Laderman over F3.

The raw Laderman transcription has no exactly repeated factors over F3, hence
flip-cpd's literal flip cannot fire.  CP decompositions are projective: a term
(u,v,w) may be replaced by (alpha u, beta v, gamma w) with alpha beta gamma=1.
This script searches one-ARTIFACT tau-orbit flips where a pair shares a component
projectively; before flipping it gauges the two terms to make the chosen
component exactly equal.  It then applies the flip and its Phi-conjugate and
accepts only if the resulting scheme still exactly sums to T333 and remains
Phi-invariant projectively.
"""
from __future__ import annotations
import json, runpy, random, time
from pathlib import Path
import numpy as np

SCRIPT_DIR=Path(__file__).resolve().parent
WS=SCRIPT_DIR.parent
OUT=WS/"data"/"laderman_tau_flip"
OUT.mkdir(parents=True, exist_ok=True)
P=3
NEXT={0:1,1:2,2:0}; PREV={0:2,1:0,2:1}; SIGMA={0:0,1:2,2:1}

src_path=SCRIPT_DIR/"laderman_tau_decomp.py"
src=src_path.read_text(); prefix=src.split('print(f"Loaded {len(terms)} Laderman terms")')[0]
ns={"__file__":str(src_path),"__name__":"defs"}; exec(compile(prefix,str(src_path),"exec"),ns)
terms_Z=ns["terms"]; eps1=np.array(ns["eps1"],dtype=np.int64)%P; eps2=np.array(ns["eps2"],dtype=np.int64)%P; pi12=np.array(ns["pi12"],dtype=np.int64)%P
terms0=[(np.array(a,dtype=np.int64).reshape(9)%P,np.array(b,dtype=np.int64).reshape(9)%P,np.array(c,dtype=np.int64).reshape(9)%P) for a,b,c in terms_Z]

def inv(x): return 1 if x%P==1 else 2

def is_zero_vec(v): return bool(np.all(np.asarray(v)%P==0))
def is_zero_term(t): return is_zero_vec(t[0]) or is_zero_vec(t[1]) or is_zero_vec(t[2])
def rank_count(S): return sum(0 if is_zero_term(t) else 1 for t in S)
def copy_scheme(S): return [(a.copy(),b.copy(),c.copy()) for a,b,c in S]

def Phi_term(t):
    a,b,c=[x.reshape(3,3) for x in t]
    a4=eps1@c@pi12; b4=pi12@a@pi12@eps1; c4=eps1@pi12@b@eps1
    a5=b4.T@eps2; b5=eps2@a4.T; c5=c4.T
    return (a5.reshape(9)%P,b5.reshape(9)%P,c5.reshape(9)%P)

def term_tensor(t):
    return np.einsum('i,j,k->ijk',t[0],t[1],t[2],optimize=True).reshape(-1)%P
T333=np.zeros((9,9,9),dtype=np.int64)
for i in range(3):
  for j in range(3):
    for k in range(3): T333[3*i+j,3*j+k,3*k+i]=1
T333_vec=T333.reshape(-1)%P

def scheme_tensor(S):
    x=np.zeros(729,dtype=np.int64)
    for t in S:
        if not is_zero_term(t): x=(x+term_tensor(t))%P
    return x

def first_nonzero(v):
    for x in v:
        if x%P: return int(x%P)
    return 0

def canon_vec(v):
    v=np.asarray(v,dtype=np.int64)%P
    s=first_nonzero(v)
    if s==0: return None,0
    return tuple((inv(s)*v)%P), s

def projective_factor_equal(x,y):
    cx,sx=canon_vec(x); cy,sy=canon_vec(y)
    if cx is None or cy is None: return False, None
    if cx != cy: return False, None
    # x = lambda * y, lambda = sx/sy
    lam=(sx*inv(sy))%P
    return True, lam

def canon_term_projective(t):
    if is_zero_term(t): return ("ZERO",)
    reps=[]; scales=[]
    for c in t:
        rep,sc=canon_vec(c)
        if rep is None: return ("ZERO",)
        reps.append(rep); scales.append(sc)
    return (reps[0],reps[1],reps[2],int(scales[0]*scales[1]*scales[2]%P))

def multiset_projective(S):
    d={}
    for t in S:
        key=canon_term_projective(t)
        if key == ("ZERO",): continue
        d[key]=d.get(key,0)+1
    return d

def phi_invariant_projective(S): return multiset_projective(S)==multiset_projective([Phi_term(t) for t in S])

def projective_equal_tensor(t1,t2):
    x=term_tensor(t1); y=term_tensor(t2)
    if not np.any(x) and not np.any(y): return True
    if not np.any(x) or not np.any(y): return False
    nz=np.nonzero(y)[0]; lam=None
    for idx in nz:
        if y[idx]%P: lam=x[idx]*inv(y[idx])%P; break
    return bool(np.array_equal(x,(lam*y)%P))

def compute_phi_perm(S):
    used=set(); perm=[None]*len(S)
    for i,t in enumerate(S):
        if is_zero_term(t): continue
        pt=Phi_term(t); found=None
        for j,u in enumerate(S):
            if j in used or is_zero_term(u): continue
            if projective_equal_tensor(pt,u): found=j; break
        if found is None: return None
        perm[i]=found; used.add(found)
    return perm

def scale_term(t, scalars):
    return tuple((scalars[i]*t[i])%P for i in range(3))

def set_comp(S,idx,comp,val):
    val=np.asarray(val,dtype=np.int64)%P
    if is_zero_vec(val):
        z=np.zeros(9,dtype=np.int64); S[idx]=(z.copy(),z.copy(),z.copy())
    else:
        tmp=[S[idx][0].copy(),S[idx][1].copy(),S[idx][2].copy()]; tmp[comp]=val; S[idx]=tuple(tmp)

def apply_flip(S,typ,i,j):
    if is_zero_term(S[i]) or is_zero_term(S[j]): return False
    if not np.array_equal(S[i][typ],S[j][typ]): return False
    tn,tp=NEXT[typ],PREV[typ]
    n1,n2=S[i][tn].copy(),S[j][tn].copy(); p1,p2=S[i][tp].copy(),S[j][tp].copy()
    set_comp(S,i,tn,(n1-n2)%P); set_comp(S,j,tp,(p1+p2)%P)
    return True

def gauge_pair_equalize(S,typ,i,j):
    """Return a new scheme with S[i][typ]==S[j][typ], preserving tensor terms.

    If S[i][typ] = lam*S[j][typ], scale term i in component typ by inv(lam).
    Compensate in NEXT component by lam so product scalar remains one.
    """
    ok,lam=projective_factor_equal(S[i][typ],S[j][typ])
    if not ok: return None
    G=copy_scheme(S)
    scalars=[1,1,1]
    scalars[typ]=inv(lam)
    scalars[NEXT[typ]]=lam
    G[i]=scale_term(G[i],scalars)
    if not np.array_equal(G[i][typ],G[j][typ]):
        return None
    return G

def projective_duplicate_pairs(S):
    out=[]; buckets={}
    for typ in range(3):
        b={}
        for i,t in enumerate(S):
            if is_zero_term(t): continue
            rep,sc=canon_vec(t[typ])
            if rep is not None: b.setdefault(rep,[]).append(i)
        buckets[str(typ)]={"bucket_sizes":sorted([len(v) for v in b.values() if len(v)>=2], reverse=True), "buckets_1based":[[x+1 for x in v] for v in b.values() if len(v)>=2]}
        for inds in b.values():
            if len(inds)>=2:
                for i in inds:
                    for j in inds:
                        if i!=j: out.append((typ,i,j))
    return out,buckets

def orbitwise_projective_flip(S,typ,i,j):
    perm=compute_phi_perm(S)
    if perm is None: return None,"no_perm"
    ti,tj=perm[i],perm[j]
    # First choose a gauge for the primary pair, then recompute Phi permutation/projective relation.
    G=gauge_pair_equalize(S,typ,i,j)
    if G is None: return None,"primary_no_projective_share"
    # Also gauge the image pair in the current G; after primary gauge, image may have changed projectively but perm remains by tensor.
    G2=gauge_pair_equalize(G,SIGMA[typ],ti,tj)
    if G2 is None: return None,"image_no_projective_share"
    ok1=apply_flip(G2,typ,i,j)
    if not ok1: return None,"primary_flip_failed"
    ok2=apply_flip(G2,SIGMA[typ],ti,tj)
    if not ok2: return None,"image_flip_failed"
    if not np.array_equal(scheme_tensor(G2),T333_vec): return None,"tensor_changed"
    if not phi_invariant_projective(G2): return None,"phi_lost"
    return G2,"accepted"

def one_step(S):
    pairs,buckets=projective_duplicate_pairs(S)
    moves=[]; reasons={}
    for typ,i,j in pairs:
        new,reason=orbitwise_projective_flip(S,typ,i,j)
        reasons[reason]=reasons.get(reason,0)+1
        if new is not None:
            moves.append((typ,i,j,rank_count(new),new))
    return moves,reasons,buckets

def main():
    t0=time.time(); S=copy_scheme(terms0)
    moves,reasons,buckets=one_step(S)
    # Shallow BFS over accepted projective tau-flips.
    seen={repr(sorted(multiset_projective(S).items()))}; frontier=[S]; depth_stats=[]; hit=None
    for depth in range(1,4):
        nxt=[]; edge_count=0; reason_acc={}
        for node in frontier:
            ms,re,_=one_step(node)
            for k,v in re.items(): reason_acc[k]=reason_acc.get(k,0)+v
            edge_count += len(ms)
            for typ,i,j,r,new in ms:
                key=repr(sorted(multiset_projective(new).items()))
                if key in seen: continue
                seen.add(key); nxt.append(new)
                if r<=22 and hit is None: hit={"depth":depth,"rank":r,"move":{"type":typ,"i":i+1,"j":j+1}}
                if len(nxt)>=500: break
            if hit is not None or len(nxt)>=500: break
        ranks=[rank_count(x) for x in nxt]
        depth_stats.append({"depth":depth,"frontier_in":len(frontier),"accepted_edges":edge_count,"new_nodes":len(nxt),"rank_hist":{str(r):ranks.count(r) for r in sorted(set(ranks))},"reason_counts":reason_acc})
        if hit is not None or not nxt: break
        frontier=nxt
    out={
        "field":"F3",
        "initial_tensor_matches":bool(np.array_equal(scheme_tensor(S),T333_vec)),
        "initial_phi_invariant_projective":bool(phi_invariant_projective(S)),
        "projective_duplicate_pair_count":len(projective_duplicate_pairs(S)[0]),
        "projective_duplicate_buckets":buckets,
        "one_step_reason_counts":reasons,
        "one_step_accepted_count":len(moves),
        "one_step_min_rank":min([23]+[r for _,_,_,r,_ in moves]),
        "one_step_moves":[{"type":typ,"i":i+1,"j":j+1,"rank":r} for typ,i,j,r,_ in moves[:200]],
        "breadth_first_depth_stats":depth_stats,
        "rank22_hit":hit,
        "elapsed_sec":time.time()-t0,
        "interpretation":"Projective-gauged exact tau flips around the Laderman seed; absence of a hit is local sampled/one-neighborhood evidence, not a theorem."
    }
    path=OUT/"projective_tau_orbit_flip_probe.json"; path.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2)[:16000]); print("SAVED",path)
if __name__=='__main__': main()
