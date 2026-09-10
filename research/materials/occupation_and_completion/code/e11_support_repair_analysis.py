#!/usr/bin/env python3
"""Local repair analysis for a concrete E11 Wang-occupation support.

Given a rank-19 A-multiset candidate, compute exact complete Wang-occupation
violations and search one-swap / sampled two-swap repairs.  A zero-violation
support is sent to fixed-U SAT by later pipeline; nonzero neighborhoods are only
local evidence about the occupation surface.
"""
from __future__ import annotations

import argparse, json, pickle, sys, time, random
from collections import Counter
from pathlib import Path

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))
from e11_capacity_incremental_sat import build_or_load_constraint_cache, mask_to_points  # noqa: E402


def load_cache(path: Path):
    with path.open('rb') as f:
        return pickle.load(f)


def point_caps(cache):
    caps = {}
    for m, cap, d in zip(cache['masks'], cache['caps'], cache['dims']):
        if int(d) == 1 and int(m).bit_count() == 1:
            caps[int(m).bit_length()] = int(cap)
    if set(caps) != set(range(1,256)):
        raise ValueError('bad point caps')
    return caps


def ms_to_sol(ms):
    c=Counter(int(x) for x in ms)
    return dict(sorted(c.items()))


def sol_to_ms(sol):
    out=[]
    for p,c in sorted(sol.items()):
        out.extend([p]*c)
    return out


def sol_masks(sol):
    sm=0; extra={}
    for p,c in sol.items():
        sm |= 1 << (p-1)
        if c>1: extra[p]=c-1
    return sm,extra


def occ(mask, sm, extra):
    o=(int(mask)&sm).bit_count()
    for p,e in extra.items():
        if (int(mask)>>(p-1))&1:
            o += e
    return o


def score(sol, cache, report=20):
    sm,extra=sol_masks(sol)
    vcnt=0; maxe=0; sq=0; bydim=Counter(); bycap=Counter(); byL=Counter(); head=[]
    for i,(m,cap) in enumerate(zip(cache['masks'], cache['caps'])):
        if not int(m): continue
        o=occ(int(m), sm, extra)
        if o>int(cap):
            e=o-int(cap)
            vcnt+=1; maxe=max(maxe,e); sq += e*e
            bydim[int(cache['dims'][i])] += 1
            bycap[int(cap)] += 1
            byL[int(cache['Ls'][i])] += 1
            if len(head)<report:
                head.append({'index':i,'key8':int(cache['keys8'][i]),'dim8':int(cache['dims'][i]),'L':int(cache['Ls'][i]),'cap':int(cap),'occupancy':int(o),'excess':int(e),'point_count':int(m).bit_count(),'points_head':mask_to_points(int(m))[:64]})
    obj=1000000*maxe + 1000*vcnt + sq
    return obj, {'violation_count':vcnt,'max_excess':maxe,'excess_sq':sq,'objective':obj,'violations_by_dim8':dict(bydim),'violations_by_cap':dict(bycap),'violations_by_L':dict(byL)}, head


def valid_by_caps(sol,caps,rank):
    return sum(sol.values()) == rank and all(0<c<=caps[p] for p,c in sol.items())


def one_swap_search(start, cache, caps, max_keep=30):
    base_ms=sol_to_ms(start)
    best=[]; seen=set(); t0=time.time(); n=0
    for idx,old in enumerate(base_ms):
        for new in range(1,256):
            if new==old: continue
            ms=list(base_ms); ms[idx]=new; ms.sort(); key=tuple(ms)
            if key in seen: continue
            seen.add(key)
            sol=ms_to_sol(ms)
            if not valid_by_caps(sol,caps,len(base_ms)): continue
            n+=1
            obj,stats,head=score(sol,cache,report=3)
            rec={'obj':obj,'stats':stats,'multiset':ms,'replace':[old,new],'head':head}
            if len(best)<max_keep:
                best.append(rec); best.sort(key=lambda r:r['obj'])
            elif obj<best[-1]['obj']:
                best[-1]=rec; best.sort(key=lambda r:r['obj'])
    return {'tested':n,'elapsed_sec':time.time()-t0,'best':best}


def random_two_swap(start, cache, caps, samples, seed, max_keep=30):
    rng=random.Random(seed); base=sol_to_ms(start); best=[]; seen=set(); t0=time.time(); n=0
    for _ in range(samples):
        i,j=rng.sample(range(len(base)),2)
        new1=rng.randrange(1,256); new2=rng.randrange(1,256)
        ms=list(base); ms[i]=new1; ms[j]=new2; ms.sort(); key=tuple(ms)
        if key in seen: continue
        seen.add(key)
        sol=ms_to_sol(ms)
        if not valid_by_caps(sol,caps,len(base)): continue
        n+=1
        obj,stats,head=score(sol,cache,report=3)
        rec={'obj':obj,'stats':stats,'multiset':ms,'replace_positions':[i,j],'new':[new1,new2],'head':head}
        if len(best)<max_keep:
            best.append(rec); best.sort(key=lambda r:r['obj'])
        elif obj<best[-1]['obj']:
            best[-1]=rec; best.sort(key=lambda r:r['obj'])
    return {'tested':n,'elapsed_sec':time.time()-t0,'best':best}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--cache',type=Path,default=Path('data/e11_capacity_sat/e11_capacity_cache.pkl'))
    ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank',type=int,default=19)
    ap.add_argument('--multiset',default='1,2,3,4,8,12,16,20,24,32,36,73,97,130,182,192,195,216,219')
    ap.add_argument('--skip-one-swap',action='store_true')
    ap.add_argument('--two-samples',type=int,default=0)
    ap.add_argument('--seed',type=int,default=2026090409)
    ap.add_argument('--out',type=Path,default=Path('data/e11_occupation_sat/cap4_candidate_repair.json'))
    args=ap.parse_args()
    if not args.cache.exists(): build_or_load_constraint_cache(args.lut,args.cache,args.rank)
    cache=load_cache(args.cache); caps=point_caps(cache)
    ms=[int(x) for x in args.multiset.split(',') if x.strip()]
    sol=ms_to_sol(ms)
    if not valid_by_caps(sol,caps,args.rank):
        raise SystemExit('input multiset violates singleton caps or rank')
    t0=time.time()
    base_obj,base_stats,base_head=score(sol,cache,report=100)
    print('base',json.dumps(base_stats,sort_keys=True),'ms',sol_to_ms(sol))
    one=None
    if not args.skip_one_swap:
        one=one_swap_search(sol,cache,caps)
        print('one_swap best',json.dumps(one['best'][0]['stats'] if one['best'] else None,sort_keys=True),'tested',one['tested'],'elapsed',one['elapsed_sec'])
    two=None
    if args.two_samples>0:
        two=random_two_swap(sol,cache,caps,args.two_samples,args.seed)
        print('two_swap best',json.dumps(two['best'][0]['stats'] if two and two['best'] else None,sort_keys=True),'tested',two['tested'],'elapsed',two['elapsed_sec'])
    result={'problem':'local repair analysis for E11 complete Wang occupation support','field':'F2','rank_s':args.rank,'input_multiset':sol_to_ms(sol),'base_stats':base_stats,'base_violations_head':base_head,'one_swap':one,'two_swap_sample':two,'elapsed_sec':time.time()-t0,'meaning':'Zero violations would produce a complete occupation-feasible A-multiset for fixed-U SAT; nonzero values are local neighborhood evidence only.'}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('wrote',args.out)

if __name__=='__main__': main()
