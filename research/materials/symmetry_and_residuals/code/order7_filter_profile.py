#!/usr/bin/env python3
"""Profile the corrected order-7 type-(3,1) survivor filter by orbit rank."""
import json, time
from collections import defaultdict, Counter
from pathlib import Path
import numpy as np

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

def gf2_rank(M): return 0 if np.asarray(M).size==0 else gf2_rref(M)[1]

def gf2_nullspace(M):
    M=np.array(M,dtype=np.uint8,copy=True)&1; rows,cols=M.shape; rref,rank,piv=gf2_rref(M); ps=set(piv); out=[]
    for f in [c for c in range(cols) if c not in ps]:
        v=np.zeros(cols,dtype=np.uint8); v[f]=1
        for i,p in enumerate(piv): v[p]=rref[i,f]
        out.append(v)
    return np.array(out,dtype=np.uint8) if out else np.zeros((0,cols),dtype=np.uint8)

def gf2_inv(M):
    M=np.array(M,dtype=np.uint8,copy=True)&1; n=M.shape[0]; A=np.hstack([M,np.eye(n,dtype=np.uint8)])
    for c in range(n):
        f=next(i for i in range(c,n) if A[i,c])
        if f!=c: A[[c,f]]=A[[f,c]]
        for i in range(n):
            if i!=c and A[i,c]: A[i]^=A[c]
    return A[:,n:]

def rowmajor(L,R): return np.kron(L,R.T).astype(np.uint8)&1

def build_T():
    T=np.zeros((81,9),dtype=np.uint8)
    for i in range(3):
      for j in range(3):
        for k in range(3): T[(3*i+j)*9+(3*j+k),3*k+i]=1
    return T

def enumerate_ro():
    pts=np.zeros(((2**9-1)**2,81),dtype=np.uint8); idx=0
    vs=[None]+[np.array([(z>>b)&1 for b in range(9)],dtype=np.uint8) for z in range(1,512)]
    for u in range(1,512):
      for v in range(1,512): pts[idx]=np.outer(vs[u],vs[v]).reshape(-1); idx+=1
    return pts

def classify(g,pts):
    mp={pts[i].tobytes():i for i in range(len(pts))}; vis=np.zeros(len(pts),bool); fixed=[]; free=[]
    for i in range(len(pts)):
      if vis[i]: continue
      cur=pts[i]; orb=[i]; vis[i]=True
      for _ in range(6):
        cur=(g@cur)&1; j=mp[cur.tobytes()]
        if vis[j]: break
        vis[j]=True; orb.append(j)
      if len(orb)==1: fixed.append(i)
      else: assert len(orb)==7; free.append(orb)
    return fixed,free

def coord(v,pivs):
    c=0
    for i,p in enumerate(pivs):
      if v[p]: c|=1<<i
    return c

def span_all(xs):
    s={0}
    for x in xs: s |= {y^x for y in list(s)}
    return s

def main():
    t0=time.time(); out_dir=Path('data/order7_exhaustive'); out_dir.mkdir(parents=True,exist_ok=True)
    T=build_T(); L=T.T&1; F=np.array([[0,0,1],[1,0,1],[0,1,0]],dtype=np.uint8); Fi=gf2_inv(F)
    M9=rowmajor(F.T&1,Fi.T&1); hW=rowmajor(Fi,F); g=np.kron(M9,M9).astype(np.uint8)&1
    assert np.array_equal((g@T)&1,(T@hW)&1)
    fixE=gf2_nullspace((g^np.eye(81,dtype=np.uint8))&1); _,_,pivs=gf2_rref(fixE)
    L0=(gf2_nullspace((hW^np.eye(9,dtype=np.uint8))&1)@L)&1; L0_rref,L0_rank,_=gf2_rref(L0); L0_coords=span_all([coord(v,pivs) for v in L0_rref])
    sigma=np.zeros((81,81),dtype=np.uint8); pwr=np.eye(81,dtype=np.uint8)
    for _ in range(7): sigma^=pwr; pwr=(g@pwr)&1
    pts=enumerate_ro(); fixed,free=classify(g,pts)
    orbit_info=[]; sigma_to=[]
    mp=defaultdict(list)
    for oi,orb in enumerate(free):
      X=pts[orb]; sig=np.bitwise_xor.reduce(X,axis=0).astype(np.uint8); sc=coord(sig,pivs); xr=gf2_rank(X)
      orbit_info.append((sc,xr)); mp[sc].append(oi)
    per=[]; hist=Counter(); eligible_rank7=0
    for local,gi in enumerate(fixed):
      pc=coord(pts[gi],pivs); allowed={x^(pc if e else 0) for x in L0_coords for e in (0,1)}
      prof=Counter()
      for ac in allowed:
        for oi in mp.get(ac,[]):
          sc,xr=orbit_info[oi]
          tag='L0' if sc in L0_coords else 'p+L0'
          prof[(xr, tag, sc==0, sc==pc)] += 1
      r7=sum(v for k,v in prof.items() if k[0]==7); eligible_rank7 += r7; hist.update({str(k):v for k,v in prof.items()})
      per.append({'fixed_local':local,'survivor_count':sum(prof.values()),'rank7_survivors':r7,'profile':{str(k):v for k,v in sorted(prof.items())}})
    results={'field':'F2','action_verified':True,'L0_dim':L0_rank,'fixed_count':len(fixed),'free_orbits':len(free),'per_fixed':per,'total_rank7_survivors_over_fixed':eligible_rank7,'pooled_profile_hist':dict(sorted(hist.items())),'conclusion':'No free orbit satisfying the necessary type-(3,1) fixed-projection condition has 7-dimensional orbit span; hence three such orbits plus one fixed point have UV-span dimension at most 19, excluding the skeleton.' if eligible_rank7==0 else 'Some rank-7 survivors exist; triple test still needed.','elapsed_sec':time.time()-t0}
    out=out_dir/'order7_filter_profile.json'; out.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps({k:results[k] for k in ['fixed_count','free_orbits','total_rank7_survivors_over_fixed','pooled_profile_hist','conclusion','elapsed_sec']},indent=2))
if __name__=='__main__': main()
