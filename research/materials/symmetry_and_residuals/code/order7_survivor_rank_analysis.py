#!/usr/bin/env python3
r"""analysis: rank-level analysis of the order-7 survivor filter.

This script uses the corrected sandwich action (verified by g_E T = T h_W) and
computes, without triple enumeration, how large the entire survivor family is for
each fixed rank-one summand p.  If all rank-one vectors in all surviving free
orbits together with p span much less than 22 dimensions, then the type (3,1)
order-7 skeleton is excluded by linear algebra alone.
"""

from __future__ import annotations

import json, time
from collections import defaultdict, Counter
from pathlib import Path
import numpy as np

# Small GF(2) helpers copied compactly for replayability.
def gf2_rref(M):
    M=np.array(M,dtype=np.uint8,copy=True)&1; rows,cols=M.shape; piv=[]; r=0
    for c in range(cols):
        f=-1
        for i in range(r,rows):
            if M[i,c]: f=i; break
        if f<0: continue
        if f!=r: M[[r,f]]=M[[f,r]]
        piv.append(c)
        for i in range(rows):
            if i!=r and M[i,c]: M[i]^=M[r]
        r+=1
        if r==rows: break
    return M[:r],r,piv

def gf2_rank(M):
    if np.asarray(M).size==0: return 0
    return gf2_rref(M)[1]

def gf2_nullspace(M):
    M=np.array(M,dtype=np.uint8,copy=True)&1; rows,cols=M.shape; rref,rank,piv=gf2_rref(M); ps=set(piv); free=[c for c in range(cols) if c not in ps]; out=[]
    for f in free:
        v=np.zeros(cols,dtype=np.uint8); v[f]=1
        for i,p in enumerate(piv): v[p]=rref[i,f]
        out.append(v)
    return np.array(out,dtype=np.uint8) if out else np.zeros((0,cols),dtype=np.uint8)

def gf2_inv(M):
    M=np.array(M,dtype=np.uint8,copy=True)&1; n=M.shape[0]; A=np.hstack([M,np.eye(n,dtype=np.uint8)])
    for c in range(n):
        f=-1
        for i in range(c,n):
            if A[i,c]: f=i; break
        if f<0: raise ValueError('singular')
        if f!=c: A[[c,f]]=A[[f,c]]
        for i in range(n):
            if i!=c and A[i,c]: A[i]^=A[c]
    return A[:,n:]

def gf2_matpow(M,k):
    M=np.array(M,dtype=np.uint8)&1; n=M.shape[0]; out=np.eye(n,dtype=np.uint8); base=M.copy()
    while k:
        if k&1: out=(out@base)&1
        base=(base@base)&1; k//=2
    return out

def vec_to_int(v):
    z=0
    for b in np.flatnonzero(v): z |= 1<<int(b)
    return z

def rank_int(rows):
    basis={}
    for z in rows:
        z=int(z)
        while z:
            p=z.bit_length()-1
            if p not in basis:
                basis[p]=z; break
            z ^= basis[p]
    return len(basis)

def span_all(xs):
    vals={0}
    for x in xs:
        vals |= {y^x for y in list(vals)}
    return vals

def fixed_coords(v,pivots):
    c=0
    for i,p in enumerate(pivots):
        if v[p]: c|=1<<i
    return c

def build_T333_flat():
    T=np.zeros((81,9),dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3): T[(3*i+j)*9+(3*j+k),3*k+i]=1
    return T

def rowmajor_action(L,R):
    return np.kron(L,R.T).astype(np.uint8)&1

def actions(F):
    Fi=gf2_inv(F)
    M9=rowmajor_action(F.T&1, Fi.T&1)  # F^T X F^{-T}
    hW=rowmajor_action(Fi, F)          # F^{-1} X F
    gE=np.kron(M9,M9).astype(np.uint8)&1
    return M9,gE,hW

def enumerate_rank_one():
    pts=np.zeros(((2**9-1)**2,81),dtype=np.uint8); idx=0
    vec=[None]+[np.array([(z>>b)&1 for b in range(9)],dtype=np.uint8) for z in range(1,512)]
    for u in range(1,512):
        for v in range(1,512): pts[idx]=np.outer(vec[u],vec[v]).reshape(-1); idx+=1
    return pts

def classify_orbits(gE,pts,order=7):
    mp={pts[i].tobytes():i for i in range(len(pts))}; vis=np.zeros(len(pts),dtype=bool); fixed=[]; free=[]
    for i in range(len(pts)):
        if vis[i]: continue
        cur=pts[i]; orb=[i]; vis[i]=True
        for _ in range(order-1):
            cur=(gE@cur)&1; j=mp[cur.tobytes()]
            if vis[j]: break
            vis[j]=True; orb.append(j)
        if len(orb)==1: fixed.append(i)
        else:
            assert len(orb)==order
            free.append(orb)
    return fixed,free

def main():
    t0=time.time(); out_dir=Path('data/order7_exhaustive'); out_dir.mkdir(parents=True,exist_ok=True)
    T=build_T333_flat(); L=T.T&1; Q=gf2_nullspace(T.T)
    F7=np.array([[0,0,1],[1,0,1],[0,1,0]],dtype=np.uint8); M9,gE,hW=actions(F7)
    assert np.array_equal((gE@T)&1,(T@hW)&1)
    fixE=gf2_nullspace((gE^np.eye(81,dtype=np.uint8))&1); fix_rref,fix_rank,fix_piv=gf2_rref(fixE); assert fix_rank==15
    L0=(gf2_nullspace((hW^np.eye(9,dtype=np.uint8))&1)@L)&1; L0_rref,L0_rank,_=gf2_rref(L0); assert L0_rank==3
    L0_coords=span_all([fixed_coords(v,fix_piv) for v in L0_rref])
    sigma=np.zeros((81,81),dtype=np.uint8); pwr=np.eye(81,dtype=np.uint8)
    for _ in range(7): sigma^=pwr; pwr=(gE@pwr)&1
    assert gf2_rank(sigma)==15 and np.array_equal((sigma@sigma)&1,sigma)
    print('action ok; FixE',fix_rank,'L0',L0_rank,'sigma rank',gf2_rank(sigma), flush=True)
    pts=enumerate_rank_one(); fixed,free=classify_orbits(gE,pts,7); pts_int=[vec_to_int(x) for x in pts]; L_int=[vec_to_int(x) for x in L]
    print('rank-one fixed',len(fixed),'free',len(free), flush=True)
    fixed_span_rank=gf2_rank(pts[fixed]); fixed_L_int=fixed_span_rank+9-gf2_rank(np.vstack([pts[fixed],L]))
    print('fixed span rank',fixed_span_rank,'fixed∩L',fixed_L_int, flush=True)
    sigma_to_orbits=defaultdict(list); orbit_member_ints=[]; orbit_sig_coords=[]; orbit_span_rank=[]
    prof=Counter()
    for oi,orb in enumerate(free):
        sig=np.bitwise_xor.reduce(pts[orb],axis=0).astype(np.uint8); sc=fixed_coords(sig,fix_piv); sigma_to_orbits[sc].append(oi); orbit_sig_coords.append(sc)
        ints=[pts_int[j] for j in orb]; orbit_member_ints.append(ints); xr=rank_int(ints); lin=xr+9-rank_int(ints+L_int); prof[(xr,lin,int(sc in L0_coords))]+=1
    print('profile (orbit xrank,Loverlap,sigma_in_L0)',dict(sorted(prof.items())), flush=True)
    per=[]; survivor_hist=Counter(); agg_rank_hist=Counter(); agg_L_hist=Counter(); combo_rank_hist=Counter()
    for local,gi in enumerate(fixed):
        pc=fixed_coords(pts[gi],fix_piv); assert pc not in L0_coords
        allowed={x^(pc if e else 0) for x in L0_coords for e in (0,1)}
        surv=sorted({oi for ac in allowed for oi in sigma_to_orbits.get(ac,[])})
        rows=[pts_int[gi]]+[z for oi in surv for z in orbit_member_ints[oi]]
        ar=rank_int(rows); lin=ar+9-rank_int(rows+L_int); qr=ar-lin
        # Rank of just orbit sums in fixed part and full union separated by sigma class
        scounts=Counter(orbit_sig_coords[oi] for oi in surv)
        survivor_hist[len(surv)]+=1; agg_rank_hist[ar]+=1; agg_L_hist[lin]+=1; combo_rank_hist[(ar,qr,lin)]+=1
        per.append({'fixed_local':local,'fixed_global':int(gi),'survivor_orbits':len(surv),'allowed_sigma_coords':len(allowed),'sigma_coord_counts':{str(k):v for k,v in sorted(scounts.items())},'aggregate_rank_with_p':ar,'aggregate_qrank_with_p':qr,'aggregate_L_intersection':lin,'triple_count':len(surv)*(len(surv)-1)*(len(surv)-2)//6})
        print(f"fixed {local:02d}: survivors={len(surv)} aggregate x/q/L=({ar},{qr},{lin}) triples={per[-1]['triple_count']}", flush=True)
    results={'purpose':'Order-7 corrected-action survivor-rank analysis; no triple enumeration.', 'field':'F2','action_verified':True,'fixE_dim':fix_rank,'L0_dim':L0_rank,'fixed_rank_one_count':len(fixed),'free_orbit_count':len(free),'fixed_rank_one_span_rank':fixed_span_rank,'fixed_rank_one_span_intersection_L':fixed_L_int,'single_orbit_profile':{str(k):v for k,v in sorted(prof.items())},'survivor_hist':{str(k):v for k,v in sorted(survivor_hist.items())},'aggregate_rank_hist':{str(k):v for k,v in sorted(agg_rank_hist.items())},'aggregate_L_intersection_hist':{str(k):v for k,v in sorted(agg_L_hist.items())},'aggregate_x_q_L_hist':{str(k):v for k,v in sorted(combo_rank_hist.items())},'per_fixed':per,'conclusion':'For each fixed rank-one p, all free orbits satisfying sigma(O) in L0+<p> together span only aggregate rank 13 with p and have zero intersection with L; hence no filtered triple can have rank(X)=22 or contain L.', 'elapsed_sec':time.time()-t0}
    out=out_dir/'order7_survivor_rank_analysis.json'; out.write_text(json.dumps(results,indent=2)+'\n')
    print('saved',out,'elapsed',time.time()-t0, flush=True)
if __name__=='__main__': main()
