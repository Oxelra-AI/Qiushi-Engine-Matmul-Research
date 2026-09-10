#!/usr/bin/env python3
"""analysis: tau-orbit flip probe around the Laderman rank-23 seed over F3.

This is a small auditable prototype, not a replacement for khoruzhii/flip-cpd.
It ports the flip operation from flip-cpd's Scheme::flip to Python and applies
flips together with their image under the Laderman tau-type involution Phi=Phi3*Phi4.

Scientific purpose:
- Stay on the exact decomposition variety: every accepted move is a composition
  of exact flips, hence preserves T_{333}.
- Stay in the Phi-invariant stratum by accepting only moves whose resulting
  scheme is exactly Phi-invariant (same term multiset, checked projectively).
- Detect whether a local tau-symmetric flip walk from Laderman can reduce rank
  from 23 to 22, and record the flippable structure if it cannot.

Field: F3.  This keeps characteristic != 2 and matches the suggested finite
field for later Hensel lifting if a candidate appears.
"""
from __future__ import annotations
import json, random, time, math
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "laderman_tau_flip"
OUT.mkdir(parents=True, exist_ok=True)

# ---------------------------------------------------------------------------
# Load analysis Laderman term definitions without executing its output code.
# ---------------------------------------------------------------------------
src_path = SCRIPT_DIR / "laderman_tau_decomp.py"
src = src_path.read_text()
prefix = src.split('print(f"Loaded {len(terms)} Laderman terms")')[0]
ns = {"__file__": str(src_path), "__name__": "defs_only"}
exec(compile(prefix, str(src_path), "exec"), ns)
terms_Z = ns["terms"]
eps1_Z, eps2_Z, pi12_Z = ns["eps1"], ns["eps2"], ns["pi12"]

P = 3

def mod(M):
    return np.asarray(M, dtype=np.int64) % P

terms0 = [(mod(a).reshape(9), mod(b).reshape(9), mod(c).reshape(9)) for a,b,c in terms_Z]
eps1, eps2, pi12 = mod(eps1_Z), mod(eps2_Z), mod(pi12_Z)

# Phi = Phi3 after Phi4 in matrix form; maps components 0->0, 1<->2.
def Phi_term(term):
    a,b,c = [x.reshape(3,3) for x in term]
    # Phi4 then Phi3, copied from analysis formula.
    a4 = eps1 @ c @ pi12
    b4 = pi12 @ a @ pi12 @ eps1
    c4 = eps1 @ pi12 @ b @ eps1
    a5 = b4.T @ eps2
    b5 = eps2 @ a4.T
    c5 = c4.T
    return (a5.reshape(9)%P, b5.reshape(9)%P, c5.reshape(9)%P)

SIGMA = {0:0, 1:2, 2:1}
NEXT = {0:1, 1:2, 2:0}
PREV = {0:2, 1:0, 2:1}

# ---------------------------------------------------------------------------
# Exact tensor/decomposition checks over F3.
# ---------------------------------------------------------------------------
def term_tensor(term):
    a,b,c = term
    return np.einsum('i,j,k->ijk', a, b, c, optimize=True).reshape(-1) % P

T333 = np.zeros((9,9,9), dtype=np.int64)
for i in range(3):
    for j in range(3):
        for k in range(3):
            T333[3*i+j, 3*j+k, 3*k+i] = 1
T333_vec = T333.reshape(-1) % P

def scheme_tensor(scheme):
    s = np.zeros(729, dtype=np.int64)
    for t in scheme:
        if not is_zero_term(t):
            s = (s + term_tensor(t)) % P
    return s

def is_zero_vec(v):
    return bool(np.all(np.asarray(v) % P == 0))

def is_zero_term(t):
    return is_zero_vec(t[0]) or is_zero_vec(t[1]) or is_zero_vec(t[2])

def rank_count(scheme):
    return sum(0 if is_zero_term(t) else 1 for t in scheme)

# Normalize a nonzero vector to a projective canonical representative over F3.
def canon_vec(v):
    v = tuple(int(x % P) for x in v)
    if all(x == 0 for x in v):
        return None, 0
    for x in v:
        if x != 0:
            inv = 1 if x == 1 else 2
            return tuple((inv*y) % P for y in v), x
    raise AssertionError

def canon_term_projective(t):
    if is_zero_term(t):
        return ("ZERO",)
    reps=[]; scales=[]
    for comp in t:
        rep, sc = canon_vec(comp)
        if rep is None:
            return ("ZERO",)
        reps.append(rep); scales.append(sc)
    # Projective tensor scalar is product of first nonzero scales.
    lam = (scales[0]*scales[1]*scales[2]) % P
    return (tuple(reps[0]), tuple(reps[1]), tuple(reps[2]), int(lam))

def multiset_projective(scheme):
    d={}
    for t in scheme:
        key=canon_term_projective(t)
        if key == ("ZERO",):
            continue
        d[key]=d.get(key,0)+1
    return d

def phi_invariant_projective(scheme):
    return multiset_projective(scheme) == multiset_projective([Phi_term(t) for t in scheme])

# Stronger labelled Phi-map when possible: find exact target index up to projective tensor.
def projective_equal_tensor(t1, t2):
    x=term_tensor(t1); y=term_tensor(t2)
    if not np.any(x) and not np.any(y): return True
    if not np.any(x) or not np.any(y): return False
    nz=np.nonzero(y)[0]
    lam=None
    for idx in nz:
        if y[idx] % P:
            lam = (x[idx] * (1 if y[idx] == 1 else 2)) % P
            break
    return bool(np.array_equal(x % P, (lam*y)%P))

def compute_phi_perm_labelled(scheme):
    used=set(); perm=[None]*len(scheme)
    for i,t in enumerate(scheme):
        if is_zero_term(t):
            perm[i]=None; continue
        pt=Phi_term(t)
        found=None
        for j,u in enumerate(scheme):
            if j in used or is_zero_term(u): continue
            if projective_equal_tensor(pt,u):
                found=j; break
        if found is None:
            return None
        perm[i]=found; used.add(found)
    return perm

# ---------------------------------------------------------------------------
# Flip operation over F3, matching flip-cpd's algebra.
# ---------------------------------------------------------------------------
def copy_scheme(scheme):
    return [(a.copy(), b.copy(), c.copy()) for a,b,c in scheme]

def set_comp(scheme, idx, comp, new_val):
    new_val = np.asarray(new_val, dtype=np.int64) % P
    if is_zero_vec(new_val):
        z=np.zeros(9,dtype=np.int64)
        scheme[idx]=(z.copy(), z.copy(), z.copy())
    else:
        lst=[x.copy() for x in scheme[idx]]
        lst[comp]=new_val
        scheme[idx]=tuple(lst)

def apply_flip_inplace(scheme, typ, j1, j2):
    """Apply flip-cpd flip to ordered pair (j1,j2) sharing component typ."""
    if is_zero_term(scheme[j1]) or is_zero_term(scheme[j2]):
        return False
    if not np.array_equal(scheme[j1][typ] % P, scheme[j2][typ] % P):
        return False
    tn, tp = NEXT[typ], PREV[typ]
    n1 = scheme[j1][tn].copy(); n2 = scheme[j2][tn].copy()
    p1 = scheme[j1][tp].copy(); p2 = scheme[j2][tp].copy()
    set_comp(scheme, j1, tn, (n1 - n2) % P)
    set_comp(scheme, j2, tp, (p1 + p2) % P)
    return True

def duplicate_pairs(scheme):
    out=[]
    for typ in range(3):
        buckets={}
        for i,t in enumerate(scheme):
            if is_zero_term(t): continue
            key=tuple(int(x) for x in t[typ] % P)
            buckets.setdefault(key,[]).append(i)
        for key, inds in buckets.items():
            if len(inds)>=2:
                for i in inds:
                    for j in inds:
                        if i!=j:
                            out.append((typ,i,j))
    return out

def orbitwise_flip(scheme, typ, i, j, perm):
    """Apply a flip and its Phi-conjugate.  Reject if the move is not valid."""
    if perm is None:
        return None, "no_labelled_perm"
    ti, tj = perm[i], perm[j]
    typ2 = SIGMA[typ]
    # If a fixed term maps to itself, a general flip may not have a distinct image;
    # we still try the sequential composition but accept only exact invariance.
    new=copy_scheme(scheme)
    ok1=apply_flip_inplace(new, typ, i, j)
    if not ok1:
        return None, "primary_invalid"
    ok2=apply_flip_inplace(new, typ2, ti, tj)
    if not ok2:
        return None, "image_invalid_after_primary"
    if not np.array_equal(scheme_tensor(new), T333_vec):
        return None, "tensor_changed"
    if not phi_invariant_projective(new):
        return None, "phi_invariance_lost"
    return new, "accepted"

def all_one_step_moves(scheme):
    perm=compute_phi_perm_labelled(scheme)
    moves=[]; reasons={}
    for typ,i,j in duplicate_pairs(scheme):
        new,reason=orbitwise_flip(scheme,typ,i,j,perm)
        reasons[reason]=reasons.get(reason,0)+1
        if new is not None:
            moves.append((typ,i,j,rank_count(new),new))
    return moves,reasons

# ---------------------------------------------------------------------------
# Run local probes.
# ---------------------------------------------------------------------------
def main():
    t0=time.time()
    scheme=copy_scheme(terms0)
    init={
        "rank": rank_count(scheme),
        "tensor_matches_T333_F3": bool(np.array_equal(scheme_tensor(scheme), T333_vec)),
        "phi_invariant_projective": bool(phi_invariant_projective(scheme)),
        "labelled_phi_perm": compute_phi_perm_labelled(scheme),
        "duplicate_pair_count": len(duplicate_pairs(scheme)),
    }
    # Duplicate histograms by component.
    dup_hist={}
    for typ in range(3):
        buckets={}
        for i,t in enumerate(scheme):
            key=tuple(int(x) for x in t[typ] % P)
            buckets.setdefault(key,[]).append(i+1)
        dup_hist[str(typ)] = sorted([inds for inds in buckets.values() if len(inds)>=2], key=lambda x:(len(x),x))
    init["duplicate_buckets_1based"] = dup_hist

    moves,reasons=all_one_step_moves(scheme)
    one_step=[]
    best_rank=init["rank"]
    best_move=None
    for typ,i,j,r,new in moves:
        best_rank=min(best_rank,r)
        if best_move is None or r < best_move[3]:
            best_move=(typ,i,j,r)
        one_step.append({"type":typ,"i":i+1,"j":j+1,"rank":r})

    # Breadth-first to shallow depth using all accepted one-ARTIFACT moves from current nodes.
    frontier=[scheme]
    seen={repr(sorted(multiset_projective(scheme).items()))}
    depth_stats=[]
    hit=None
    max_depth=3
    max_nodes=2000
    for depth in range(1,max_depth+1):
        nxt=[]; acc=0; red=0; reason_acc={}
        for node in frontier:
            ms,re=all_one_step_moves(node)
            for k,v in re.items(): reason_acc[k]=reason_acc.get(k,0)+v
            for typ,i,j,r,new in ms:
                acc+=1
                key=repr(sorted(multiset_projective(new).items()))
                if key in seen: continue
                seen.add(key)
                nxt.append(new)
                if r < rank_count(node): red+=1
                if r <= 22 and hit is None:
                    hit={"depth":depth,"rank":r,"move":{"type":typ,"i":i+1,"j":j+1}}
                    # Save the hit scheme factors if ever found.
                    arr=np.array([[comp for t in new for comp in t]], dtype=object)
                if len(nxt) >= max_nodes:
                    break
            if len(nxt) >= max_nodes or hit is not None:
                break
        ranks=[rank_count(x) for x in nxt]
        depth_stats.append({
            "depth":depth,
            "frontier_in":len(frontier),
            "accepted_edges_from_frontier":acc,
            "new_nodes":len(nxt),
            "rank_hist":{str(r):ranks.count(r) for r in sorted(set(ranks))},
            "reduction_edge_count_seen":red,
            "reason_counts":reason_acc,
        })
        if hit is not None or not nxt:
            break
        frontier=nxt[:max_nodes]

    # Random walk with rejection to see whether the accepted graph has mobility.
    rng=random.Random(20260907)
    walk=copy_scheme(scheme)
    walk_stats={"steps":0,"accepted":0,"rejected_no_moves":0,"best_rank":rank_count(walk),"rank_hist":{}}
    for step in range(20000):
        ms,_=all_one_step_moves(walk)
        if not ms:
            walk_stats["rejected_no_moves"] += 1
            break
        typ,i,j,r,new = rng.choice(ms)
        walk = new
        walk_stats["accepted"] += 1
        walk_stats["steps"] = step+1
        rr=rank_count(walk)
        walk_stats["best_rank"] = min(walk_stats["best_rank"], rr)
        walk_stats["rank_hist"][str(rr)] = walk_stats["rank_hist"].get(str(rr),0)+1
        if rr <= 22:
            hit={"depth":"random_walk","rank":rr,"move":{"type":typ,"i":i+1,"j":j+1},"ARTIFACT":step+1}
            break

    out={
        "field":"F3",
        "source":"Laderman terms from analysis / Burichenko 1508.01110; Phi=Phi3*Phi4",
        "initial":init,
        "one_step_reason_counts":reasons,
        "one_step_accepted_count":len(moves),
        "one_step_moves":one_step[:200],
        "one_step_min_rank":best_rank,
        "one_step_best_move":None if best_move is None else {"type":best_move[0],"i":best_move[1]+1,"j":best_move[2]+1,"rank":best_move[3]},
        "breadth_first_depth_stats":depth_stats,
        "random_walk_stats":walk_stats,
        "rank22_hit":hit,
        "elapsed_sec":time.time()-t0,
        "interpretation":"Accepted moves are exact Phi-symmetric compositions of flip-cpd flips. No hit is only local evidence around the Laderman tau component, not an emptiness theorem.",
    }
    path=OUT/"tau_orbit_flip_probe.json"
    path.write_text(json.dumps(out, indent=2)+"\n")
    print(json.dumps(out, indent=2)[:12000])
    print("SAVED", path)

if __name__ == "__main__":
    main()
