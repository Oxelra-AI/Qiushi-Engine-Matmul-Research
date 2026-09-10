#!/usr/bin/env python3
"""Orbit-normalized rank-one-envelope search for the E11 core over F2.

The search works with the equivalent two-factor-span formulation.  A rank-r CPD
of an 8x9x9 core exists iff there are r nonzero rank-one 8x9 matrices whose
span contains the nine C-slices; W is then recovered by linear solving.  This
script does not impose the equal-W law from sampled rank-21 neighborhoods.

The main mathematical compression used here is the quotient stabilizer of the
E11 core A-factor space A/<E00>.  For decomposition factors the full isotropy
acts by U -> P^T U Q^{-T}.  This induces a well-defined action on the quotient
exactly when row_0(P)=e0^T and col_0(Q)=e0.  Nonzero quotient A-factors in F2^8
then split into eight orbits with sizes 3,3,9,36,36,36,36,96.  Earlier versions
of this file used the transposed complement-preserving conditions P[:,0]=e0 and
Q^{-T}[:,0]=e0, producing the invalid sizes 6,9,12,12,36,36,72,72; do not use
those for quotient orbit compression.  GL(3,2) actions on B are diagnostic only
because the middle Q is shared with the A side.

This is a global finite-field search instrument over the 130305 rank-one UV
columns, not a proof of nonexistence unless every branch in a declared finite
search tree is exhausted and independently checked.
"""
from __future__ import annotations

import argparse, json, time
from collections import Counter, defaultdict
from functools import lru_cache
from pathlib import Path
from typing import Iterable

import numpy as np

# ---------------- basic F2 linear algebra on packed integer vectors ----------------

def mask_weight(x:int)->int:
    return int(x).bit_count()


def rank_ints(vecs:Iterable[int])->int:
    basis={}
    for vv in vecs:
        v=int(vv)
        while v:
            p=v.bit_length()-1
            if p in basis:
                v ^= basis[p]
            else:
                basis[p]=v
                break
    return len(basis)


def echelon_basis(vecs:Iterable[int])->dict[int,int]:
    basis={}
    for vv in vecs:
        v=int(vv)
        while v:
            p=v.bit_length()-1
            if p in basis:
                v ^= basis[p]
            else:
                basis[p]=v
                break
    return basis


def reduce_by_basis(v:int,basis:dict[int,int])->int:
    x=int(v)
    for p in sorted(basis.keys(), reverse=True):
        if (x>>p)&1:
            x ^= basis[p]
    return x


def deficiency(cols:list[int], targets:list[int])->tuple[int,int,int]:
    rk=rank_ints(cols)
    rks=rank_ints(cols+targets)
    return (rks-rk,rk,rks)


def solve_coeffs(cols:list[int], target:int, nbits:int)->int|None:
    R=len(cols)
    rows=[]
    for bit in range(nbits):
        row=0
        for j,c in enumerate(cols):
            if (int(c)>>bit)&1:
                row |= 1<<j
        if (int(target)>>bit)&1:
            row |= 1<<R
        rows.append(row)
    pivots=[]; prow=0
    for col in range(R):
        piv=None
        for rr in range(prow,len(rows)):
            if (rows[rr]>>col)&1:
                piv=rr; break
        if piv is None:
            continue
        rows[prow],rows[piv]=rows[piv],rows[prow]
        for rr in range(len(rows)):
            if rr!=prow and ((rows[rr]>>col)&1):
                rows[rr]^=rows[prow]
        pivots.append(col); prow+=1
    mask=(1<<R)-1
    for row in rows:
        if (row & mask)==0 and ((row>>R)&1):
            return None
    sol=0
    for i,col in enumerate(pivots):
        if (rows[i]>>R)&1:
            sol |= 1<<col
    return sol


def reconstruct_w(cols:list[int], targets:list[int], nbits:int=72)->list[int]|None:
    sols=[]
    for t in targets:
        sol=solve_coeffs(cols,t,nbits)
        if sol is None:
            return None
        sols.append(sol)
    W=[]
    for i in range(len(cols)):
        wm=0
        for c,sol in enumerate(sols):
            if (sol>>i)&1:
                wm |= 1<<c
        W.append(wm)
    return W

# ---------------- tensor and masks ----------------

def core_targets(core:np.ndarray)->list[int]:
    T=(core.astype(np.uint8)&1)
    m,nv,nw=T.shape
    targets=[]
    for c in range(nw):
        x=0
        for a in range(m):
            for b in range(nv):
                if int(T[a,b,c]):
                    x |= 1<<(a*nv+b)
        targets.append(x)
    return targets


def vec_from_mask(mask:int,n:int)->np.ndarray:
    return np.array([(int(mask)>>i)&1 for i in range(n)],dtype=np.uint8)


def outer_mask(u:int,v:int,nv:int=9)->int:
    x=0; uu=int(u)
    while uu:
        lb=uu & -uu; a=lb.bit_length()-1; uu^=lb
        vv=int(v)
        while vv:
            lbv=vv & -vv; b=lbv.bit_length()-1; vv^=lbv
            x ^= 1<<(a*nv+b)
    return x


def all_rankone_cols(m:int=8,nv:int=9):
    return [(outer_mask(u,v,nv),u,v) for u in range(1,1<<m) for v in range(1,1<<nv)]

# ---------------- GL3 action and E11 quotient action ----------------

def mat_from_mask(x:int)->np.ndarray:
    return np.array([[(int(x)>>(3*i+j))&1 for j in range(3)] for i in range(3)],dtype=np.uint8)


def mask_from_mat(M:np.ndarray)->int:
    out=0
    for i in range(3):
        for j in range(3):
            if int(M[i,j])&1:
                out |= 1<<(3*i+j)
    return out


def f2_rank_mat(M:np.ndarray)->int:
    A=(M.copy().astype(np.uint8)&1); r=0; rows,cols=A.shape
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if A[i,c]: piv=i; break
        if piv is None: continue
        if piv!=r: A[[r,piv]]=A[[piv,r]]
        for i in range(rows):
            if i!=r and A[i,c]: A[i]^=A[r]
        r+=1
    return r


def mat_inv(M:np.ndarray)->np.ndarray:
    A=np.concatenate([M.copy().astype(np.uint8)&1,np.eye(3,dtype=np.uint8)],axis=1)
    r=0
    for c in range(3):
        piv=None
        for i in range(r,3):
            if A[i,c]: piv=i; break
        if piv is None: raise ValueError('singular')
        if piv!=r: A[[r,piv]]=A[[piv,r]]
        for i in range(3):
            if i!=r and A[i,c]: A[i]^=A[r]
        r+=1
    return A[:,3:]


def generate_gl3():
    return [mat_from_mask(x) for x in range(512) if f2_rank_mat(mat_from_mask(x))==3]


def stabilizer_col0_e0(gl):
    e0=np.array([1,0,0],dtype=np.uint8)
    return [G for G in gl if np.array_equal(G[:,0],e0)]


def stabilizer_row0_e0(gl):
    e0=np.array([1,0,0],dtype=np.uint8)
    return [G for G in gl if np.array_equal(G[0,:],e0)]


def quotient_mask_from_full_without_bit0(full:int)->int:
    q=0; k=0
    for bit in range(9):
        if bit==0: continue
        if (int(full)>>bit)&1:
            q |= 1<<k
        k+=1
    return q


def full_mask_from_quotient(q:int)->int:
    full=0; k=0
    for bit in range(9):
        if bit==0: continue
        if (int(q)>>k)&1:
            full |= 1<<bit
        k+=1
    return full


def apply_e11_action_to_q(q:int,P:np.ndarray,Q:np.ndarray)->int:
    """Correct action on E11-core quotient A coefficient factors.

    For QMM coefficient covectors the full matrix-multiplication isotropy acts as
        U -> P^T U Q^{-T},  V -> Q^T V R^{-T},  W -> P^{-1} W R.
    The E11 core A factors live in the quotient by <E00>, not in a preferred
    complement.  The action is well-defined on A/<E00> when row_0(P)=e0^T and
    col_0(Q)=e0; a representative with U00=0 may acquire an E00 component and
    that component must be dropped after transformation.
    """
    M=mat_from_mask(full_mask_from_quotient(q))
    N=(P.T @ M @ mat_inv(Q).T) & 1
    return quotient_mask_from_full_without_bit0(mask_from_mat(N))


def apply_B_action(v:int,Q:np.ndarray,R:np.ndarray)->int:
    M=mat_from_mask(v)
    N=(Q.T @ M @ mat_inv(R).T) & 1
    return mask_from_mat(N)


def e11_q_signature(q:int)->tuple[int,int,int]:
    M=mat_from_mask(full_mask_from_quotient(q))
    return (f2_rank_mat(M), int(M[1,0]) + 2*int(M[2,0]), mask_weight(q))


def compute_e11_orbits()->dict:
    gl=generate_gl3()
    e0=np.array([1,0,0],dtype=np.uint8)
    Ps=[P for P in gl if np.array_equal(P[0,:], e0)]
    Qs=[Q for Q in gl if np.array_equal(Q[:,0], e0)]
    actions=[]
    for P in Ps:
        for Q in Qs:
            perm=[0]*256
            for q in range(256):
                perm[q]=0 if q==0 else apply_e11_action_to_q(q,P,Q)
            actions.append(perm)
    unseen=set(range(1,256)); orbits=[]; point_orbit={}
    while unseen:
        seed=min(unseen)
        orb=set([seed]); changed=True
        while changed:
            changed=False
            # closure from current orbit under all actions
            for x in list(orb):
                for perm in actions:
                    y=perm[x]
                    if y not in orb:
                        orb.add(y); changed=True
        idx=len(orbits)
        for x in orb: point_orbit[x]=idx
        unseen-=orb
        sigs=Counter(e11_q_signature(x)[:2] for x in orb)
        weights=Counter(mask_weight(x) for x in orb)
        reps=sorted(orb, key=lambda z:(mask_weight(z),z))[:10]
        orbits.append({'orbit':idx,'size':len(orb),'seed':seed,'reps':reps,
                       'signature_counts':{str(k):v for k,v in sigs.items()},
                       'weight_counts':{str(k):v for k,v in sorted(weights.items())}})
    return {'num_actions':len(actions),'num_orbits':len(orbits),'orbits':orbits,'point_orbit':point_orbit}


def row_reduced_v_orbits()->dict:
    # Diagnostic B-side marginal orbits after imposing the corrected E11 quotient
    # condition on the shared middle matrix Q.  These cannot be used independently
    # of the A-side quotient action because the same Q acts on both sides.
    gl=generate_gl3()
    e0=np.array([1,0,0],dtype=np.uint8)
    Qs=[Q for Q in gl if np.array_equal(Q[:,0], e0)]
    Rs=gl
    actions=[]
    for Q in Qs:
        for R in Rs:
            actions.append((Q,mat_inv(R).T))
    unseen=set(range(1,512)); orbits=[]; point_orbit={}
    while unseen:
        seed=min(unseen); orb=set([seed]); frontier=[seed]
        while frontier:
            x=frontier.pop()
            M=mat_from_mask(x)
            for Q,Rit in actions:
                y=mask_from_mat((Q.T @ M @ Rit)&1)
                if y not in orb:
                    orb.add(y); frontier.append(y)
        idx=len(orbits)
        for x in orb: point_orbit[x]=idx
        unseen-=orb
        ranks=Counter(f2_rank_mat(mat_from_mask(x)) for x in orb)
        reps=sorted(orb, key=lambda z:(mask_weight(z),z))[:10]
        orbits.append({'orbit':idx,'size':len(orb),'seed':seed,'reps':reps,
                       'rank_counts':{str(k):v for k,v in ranks.items()},
                       'weight_counts':{str(k):v for k,v in Counter(mask_weight(x) for x in orb).items()}})
    return {'num_actions':len(actions),'num_orbits':len(orbits),'orbits':orbits,'point_orbit':point_orbit}

# ---------------- capacity support and search ----------------

def load_capacity_solution(path:str|None)->dict[int,int]|None:
    if not path: return None
    d=json.loads(Path(path).read_text())
    sol=d.get('final_solution')
    if sol is None and d.get('iterations'):
        # Use last solved candidate as a pilot support, if present.
        for it in reversed(d['iterations']):
            if 'solution' in it:
                sol=it['solution']; break
    if sol is None: return None
    return {int(k):int(v) for k,v in sol.items() if int(v)}


def columns_for_support(support:dict[int,int], restrict_v_orbit:int|None=None, v_point_orbit:dict[int,int]|None=None):
    cols=[]
    for u,mult in support.items():
        for v in range(1,512):
            if restrict_v_orbit is not None and v_point_orbit is not None and v_point_orbit[v]!=restrict_v_orbit:
                continue
            cols.append((outer_mask(u,v,9),u,v,mult))
    return cols


def unique_cols(cols):
    # For a fixed (u,v) the UV column is unique; keep u,v,mult metadata.
    seen={}
    for col,u,v,m in cols:
        seen.setdefault(col,(col,u,v,m))
    return list(seen.values())


def greedy_seed(targets, candidates, rank:int, rng, trials:int, beam:int=1):
    best=None
    for tr in range(trials):
        chosen=[]; chosen_cols=[]; avail=list(range(len(candidates)))
        # randomize target order/score tie by noise
        for step in range(rank):
            base=echelon_basis(chosen_cols)
            qtargets=[reduce_by_basis(t,base) for t in targets]
            curdef=rank_ints(qtargets)
            if curdef==0:
                break
            # sample candidates plus deterministic prefix to limit cost
            if len(avail)>5000:
                sample=rng.choice(avail, size=5000, replace=False).tolist()
            else:
                sample=avail
            scored=[]
            for idx in sample:
                col,u,v,m=candidates[idx]
                if col in chosen_cols: continue
                obj=deficiency(chosen_cols+[col],targets)
                # prefer larger rankK and smaller target quotient; mild sparsity variation
                score=(obj[0], -obj[1], rng.random())
                scored.append((score,idx,obj))
            if not scored: break
            scored.sort(key=lambda x:x[0])
            idx=scored[0][1]; obj=scored[0][2]
            chosen.append(idx); chosen_cols.append(candidates[idx][0])
            if obj[0]==0:
                break
        obj=deficiency(chosen_cols,targets)
        rec=(obj,chosen)
        if best is None or (obj[0],-obj[1],len(chosen)) < (best[0][0],-best[0][1],len(best[1])):
            best=rec
            print(f'  greedy trial {tr}: best deficiency={obj[0]} rankK={obj[1]} rankKS={obj[2]} chosen={len(chosen)}')
        if obj[0]==0 and len(chosen)<=rank:
            return best
    return best


def verify_and_save_solution(path:Path, chosen_cols, targets, core):
    cols=[c[0] for c in chosen_cols]
    W=reconstruct_w(cols,targets,core.shape[0]*core.shape[1])
    if W is None: return None
    # pad to rank if needed not here
    U=np.zeros((len(cols),core.shape[0]),dtype=np.uint8)
    V=np.zeros((len(cols),core.shape[1]),dtype=np.uint8)
    WW=np.zeros((len(cols),core.shape[2]),dtype=np.uint8)
    for i,(col,u,v,_) in enumerate(chosen_cols):
        U[i]=vec_from_mask(u,core.shape[0]); V[i]=vec_from_mask(v,core.shape[1]); WW[i]=vec_from_mask(W[i],core.shape[2])
    R=np.zeros_like(core,dtype=np.uint8)
    for i in range(len(cols)):
        R ^= (U[i].reshape(-1,1,1)*V[i].reshape(1,-1,1)*WW[i].reshape(1,1,-1)).astype(np.uint8)
    ok=bool(np.array_equal(R,core))
    path.parent.mkdir(parents=True,exist_ok=True)
    np.savez(path,U=U,V=V,W=WW)
    return {'solution_npz':str(path),'rank':len(cols),'verified':ok,'diff_count':int(np.sum(R^core))}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--core',default='data/restricted_cores/mask_001_E11_core.npy')
    ap.add_argument('--capacity-json',default='data/core_capacity/core_capacity_E11_s19.json')
    ap.add_argument('--rank',type=int,default=19)
    ap.add_argument('--out-json',required=True)
    ap.add_argument('--mode',choices=['orbits','support-probe','greedy-global'],default='orbits')
    ap.add_argument('--seed',type=int,default=20260904)
    ap.add_argument('--trials',type=int,default=100)
    ap.add_argument('--restrict-v-orbit',type=int,default=-1)
    args=ap.parse_args()
    t0=time.time()
    core=np.load(args.core).astype(np.uint8)&1
    targets=core_targets(core)
    result={'mode':args.mode,'core':args.core,'rank':args.rank,'target_slice_rank':rank_ints(targets)}
    eorbs=compute_e11_orbits()
    vorbs=row_reduced_v_orbits()
    result['e11_Aquot_orbits']={k:v for k,v in eorbs.items() if k!='point_orbit'}
    result['B_left_orbits']={k:v for k,v in vorbs.items() if k!='point_orbit'}
    print('E11 A quotient orbits:', result['e11_Aquot_orbits'])
    print('B left v orbits:', result['B_left_orbits'])
    if args.mode!='orbits':
        sol=load_capacity_solution(args.capacity_json)
        if sol is None:
            print('No capacity solution found in',args.capacity_json)
        else:
            orbit_mult=Counter()
            for u,m in sol.items(): orbit_mult[eorbs['point_orbit'][u]]+=m
            result['capacity_support']={'source':args.capacity_json,'total_mult':sum(sol.values()),'support_size':len(sol),
                                        'max_mult':max(sol.values()),'orbit_mult':dict(orbit_mult),
                                        'points':{str(k):v for k,v in sorted(sol.items())}}
            cols=unique_cols(columns_for_support(sol, args.restrict_v_orbit if args.restrict_v_orbit>=0 else None, vorbs['point_orbit']))
            result['candidate_uv_columns']={'count':len(cols),'restrict_v_orbit':args.restrict_v_orbit}
            print('capacity support',result['capacity_support'])
            print('candidate UV columns',len(cols))
            # Fast span check for the full envelope of this support, then random greedy subsets.
            full_obj=deficiency([c[0] for c in cols],targets)
            result['full_support_envelope_deficiency']={'deficiency':full_obj[0],'rankK':full_obj[1],'rankKS':full_obj[2]}
            print('full support envelope deficiency',full_obj)
            if args.mode in ('support-probe','greedy-global') and full_obj[0]==0:
                rng=np.random.default_rng(args.seed)
                best=greedy_seed(targets, cols, args.rank, rng, args.trials)
                if best is not None:
                    obj,idxs=best
                    result['greedy_best']={'deficiency':obj[0],'rankK':obj[1],'rankKS':obj[2],'chosen_count':len(idxs),
                                           'chosen':[(cols[i][1],cols[i][2]) for i in idxs]}
                    if obj[0]==0 and len(idxs)<=args.rank:
                        chosen=[cols[i] for i in idxs]
                        solrec=verify_and_save_solution(Path(args.out_json).with_suffix('.solution.npz'),chosen,targets,core)
                        result['solution']=solrec
    if args.mode=='greedy-global':
        # No capacity support restriction: global randomized greedy over all rank-one columns.
        allcols=all_rankone_cols(core.shape[0],core.shape[1])
        # Attach multiplicity placeholder.
        allcols=[(c,u,v,1) for c,u,v in allcols]
        rng=np.random.default_rng(args.seed)
        best=greedy_seed(targets, allcols, args.rank, rng, args.trials)
        if best is not None:
            obj,idxs=best
            result['global_greedy_best']={'deficiency':obj[0],'rankK':obj[1],'rankKS':obj[2],'chosen_count':len(idxs),
                                          'chosen':[(allcols[i][1],allcols[i][2]) for i in idxs]}
            if obj[0]==0 and len(idxs)<=args.rank:
                chosen=[allcols[i] for i in idxs]
                result['global_solution']=verify_and_save_solution(Path(args.out_json).with_suffix('.global_solution.npz'),chosen,targets,core)
    result['elapsed_sec']=time.time()-t0
    Path(args.out_json).parent.mkdir(parents=True,exist_ok=True)
    Path(args.out_json).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('wrote',args.out_json)

if __name__=='__main__':
    main()
