#!/usr/bin/env python3
"""Vectorized local search for complete E11 Wang-occupation-feasible supports.

This is a finite-combinatorial search aid for the E11 rank-19 route.  It uses the
cached 417,199 Wang-derived occupation constraints and a dense point/subspace
membership matrix to evaluate exact one-swap neighborhoods quickly.  A support
with zero violations is a complete occupation-feasible A-multiset and should be
sent immediately to fixed-A XOR SAT.  Nonzero local minima are only local search
evidence; they do not prove nonexistence.
"""
from __future__ import annotations

import argparse, json, pickle, random, sys, time
from collections import Counter
from pathlib import Path

import numpy as np

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))
from e11_capacity_incremental_sat import build_or_load_constraint_cache, mask_to_points  # noqa: E402


def load_cache(path: Path):
    with path.open('rb') as f:
        return pickle.load(f)


def point_caps(cache):
    caps = np.zeros(256, dtype=np.int16)
    for m, cap, d in zip(cache['masks'], cache['caps'], cache['dims']):
        if int(d) == 1 and int(m).bit_count() == 1:
            caps[int(m).bit_length()] = int(cap)
    if np.count_nonzero(caps[1:]) != 255:
        raise ValueError('bad singleton capacities')
    return caps


def build_membership(cache, npy_path: Path | None = None, force: bool = False):
    N = len(cache['masks'])
    if npy_path and npy_path.exists() and not force:
        print(f'loading membership matrix {npy_path}')
        M = np.load(npy_path, mmap_mode=None)
        if M.shape != (256, N):
            raise ValueError(f'bad membership shape {M.shape}, expected {(256,N)}')
        return M
    print(f'building membership matrix 256 x {N:,}')
    t0 = time.time()
    M = np.zeros((256, N), dtype=np.uint8)
    for i, m0 in enumerate(cache['masks']):
        m = int(m0)
        while m:
            lb = m & -m
            p = lb.bit_length()
            M[p, i] = 1
            m ^= lb
        if (i + 1) % 100000 == 0:
            print(f'  membership {i+1:,}/{N:,}')
    print(f'membership built in {time.time()-t0:.2f}s')
    if npy_path:
        npy_path.parent.mkdir(parents=True, exist_ok=True)
        np.save(npy_path, M)
        print(f'saved {npy_path}')
    return M


def ms_to_counts(ms):
    c = np.zeros(256, dtype=np.int16)
    for p in ms:
        c[int(p)] += 1
    return c


def counts_to_ms(counts):
    out = []
    for p in range(1, 256):
        out.extend([p] * int(counts[p]))
    return out


def valid_counts(counts, caps, rank):
    return int(counts[1:].sum()) == rank and bool(np.all(counts[1:] <= caps[1:])) and bool(np.all(counts[1:] >= 0))


def occupancy_vec(M, counts):
    pts = np.nonzero(counts)[0]
    if len(pts) == 0:
        return np.zeros(M.shape[1], dtype=np.int16)
    occ = np.zeros(M.shape[1], dtype=np.int16)
    for p in pts:
        occ += int(counts[p]) * M[p].astype(np.int16)
    return occ


def stats_from_occ(occ, cache):
    caps = np.asarray(cache['caps'], dtype=np.int16)
    excess = occ - caps
    viol = excess > 0
    vcnt = int(viol.sum())
    if vcnt == 0:
        return 0, {'violation_count':0,'max_excess':0,'excess_sq':0,'objective':0,'violations_by_dim8':{},'violations_by_L':{},'violations_by_cap':{}}, []
    maxe = int(excess[viol].max())
    sq = int(np.square(excess[viol].astype(np.int64)).sum())
    dims = np.asarray(cache['dims'], dtype=np.int16)
    Ls = np.asarray(cache['Ls'], dtype=np.int16)
    bydim = Counter(int(x) for x in dims[viol])
    byL = Counter(int(x) for x in Ls[viol])
    bycap = Counter(int(x) for x in caps[viol])
    obj = 1_000_000 * maxe + 1000 * vcnt + sq
    idxs = np.flatnonzero(viol)[:50]
    head = []
    for i in idxs:
        head.append({'index':int(i),'key8':int(cache['keys8'][int(i)]),'dim8':int(cache['dims'][int(i)]),'L':int(cache['Ls'][int(i)]),'cap':int(cache['caps'][int(i)]),'occupancy':int(occ[int(i)]),'excess':int(excess[int(i)]),'point_count':int(cache['masks'][int(i)]).bit_count(),'points_head':mask_to_points(int(cache['masks'][int(i)]))[:64]})
    return int(obj), {'violation_count':vcnt,'max_excess':maxe,'excess_sq':sq,'objective':int(obj),'violations_by_dim8':dict(bydim),'violations_by_L':dict(byL),'violations_by_cap':dict(bycap)}, head


def best_one_swap(counts, occ, M, cache, caps, rank, restrict_new=None):
    cur_obj, cur_stats, _ = stats_from_occ(occ, cache)
    best = {'objective':cur_obj,'stats':cur_stats,'old':None,'new':None,'counts':counts.copy(),'occ':occ.copy()}
    selected = [p for p in range(1,256) if counts[p] > 0]
    new_points = list(restrict_new) if restrict_new is not None else list(range(1,256))
    caps_arr = caps
    t0 = time.time(); tested = 0
    capvec = np.asarray(cache['caps'], dtype=np.int16)
    dims = np.asarray(cache['dims'], dtype=np.int16)
    Ls = np.asarray(cache['Ls'], dtype=np.int16)
    for old in selected:
        base_occ = occ - M[old].astype(np.int16)
        for new in new_points:
            if new == old:
                continue
            if counts[new] + 1 > caps_arr[new]:
                continue
            # if old==new already skipped; removing old may allow adding to old only skipped.
            tested += 1
            occ2 = base_occ + M[new].astype(np.int16)
            excess = occ2 - capvec
            viol = excess > 0
            vcnt = int(viol.sum())
            if vcnt == 0:
                stats = {'violation_count':0,'max_excess':0,'excess_sq':0,'objective':0,'violations_by_dim8':{},'violations_by_L':{},'violations_by_cap':{}}
                c2 = counts.copy(); c2[old] -= 1; c2[new] += 1
                return {'objective':0,'stats':stats,'old':old,'new':new,'counts':c2,'occ':occ2.copy(),'tested':tested,'elapsed_sec':time.time()-t0}
            maxe = int(excess[viol].max())
            sq = int(np.square(excess[viol].astype(np.int64)).sum())
            obj = 1_000_000 * maxe + 1000 * vcnt + sq
            if obj < best['objective']:
                bydim = Counter(int(x) for x in dims[viol])
                byL = Counter(int(x) for x in Ls[viol])
                bycap = Counter(int(x) for x in capvec[viol])
                stats = {'violation_count':vcnt,'max_excess':maxe,'excess_sq':sq,'objective':int(obj),'violations_by_dim8':dict(bydim),'violations_by_L':dict(byL),'violations_by_cap':dict(bycap)}
                c2 = counts.copy(); c2[old] -= 1; c2[new] += 1
                best = {'objective':int(obj),'stats':stats,'old':old,'new':new,'counts':c2,'occ':occ2.copy()}
    best['tested'] = tested; best['elapsed_sec'] = time.time()-t0
    return best


def random_counts(rng, caps, rank):
    c = np.zeros(256, dtype=np.int16)
    while int(c[1:].sum()) < rank:
        p = rng.randrange(1,256)
        if c[p] < caps[p]:
            c[p] += 1
    return c


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cache', type=Path, default=Path('data/e11_capacity_sat/e11_capacity_cache.pkl'))
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--membership', type=Path, default=Path('data/e11_occupation_sat/e11_membership.npy'))
    ap.add_argument('--rank', type=int, default=19)
    ap.add_argument('--seed-ms', default='1,2,3,4,8,12,16,20,24,32,36,73,97,130,182,192,195,216,219')
    ap.add_argument('--random-restarts', type=int, default=0)
    ap.add_argument('--max-greedy-steps', type=int, default=20)
    ap.add_argument('--seed', type=int, default=2026090409)
    ap.add_argument('--force-membership', action='store_true')
    ap.add_argument('--out', type=Path, default=Path('data/e11_occupation_sat/vector_local_result.json'))
    args = ap.parse_args()
    t_all=time.time()
    if not args.cache.exists():
        build_or_load_constraint_cache(args.lut, args.cache, args.rank)
    cache=load_cache(args.cache); caps=point_caps(cache); M=build_membership(cache,args.membership,args.force_membership)
    rng=random.Random(args.seed)
    starts=[]
    if args.seed_ms.strip():
        starts.append(('given', ms_to_counts([int(x) for x in args.seed_ms.split(',') if x.strip()])))
    for i in range(args.random_restarts):
        starts.append((f'random_{i}', random_counts(rng,caps,args.rank)))
    best_record=None; all_logs=[]
    for name, counts in starts:
        if not valid_counts(counts,caps,args.rank):
            raise SystemExit(f'invalid start {name}: {counts_to_ms(counts)}')
        occ=occupancy_vec(M,counts)
        obj,stats,head=stats_from_occ(occ,cache)
        print(f'start {name}: obj={obj} stats={stats} ms={counts_to_ms(counts)}')
        log=[{'ARTIFACT':0,'objective':obj,'stats':stats,'multiset':counts_to_ms(counts),'move':None}]
        if best_record is None or obj < best_record['objective']:
            best_record={'start':name,'objective':obj,'stats':stats,'multiset':counts_to_ms(counts),'head':head}
        for step in range(1,args.max_greedy_steps+1):
            mv=best_one_swap(counts,occ,M,cache,caps,args.rank)
            if mv['objective'] >= obj:
                print(f'  ARTIFACT {step}: local minimum, best neighbor obj={mv["objective"]} stats={mv["stats"]} tested={mv.get("tested")}')
                log.append({'ARTIFACT':step,'local_minimum':True,'best_neighbor_objective':mv['objective'],'best_neighbor_stats':mv['stats'],'tested':mv.get('tested'),'elapsed_sec':mv.get('elapsed_sec')})
                break
            counts=mv['counts']; occ=mv['occ']; obj=mv['objective']; stats=mv['stats']; _,_,head=stats_from_occ(occ,cache)
            print(f'  ARTIFACT {step}: move {mv["old"]}->{mv["new"]} obj={obj} stats={stats} ms={counts_to_ms(counts)}')
            log.append({'ARTIFACT':step,'objective':obj,'stats':stats,'multiset':counts_to_ms(counts),'move':{'old':mv['old'],'new':mv['new']},'tested':mv.get('tested'),'elapsed_sec':mv.get('elapsed_sec')})
            if best_record is None or obj < best_record['objective']:
                best_record={'start':name,'objective':obj,'stats':stats,'multiset':counts_to_ms(counts),'head':head}
            if stats['violation_count']==0:
                break
        all_logs.append({'start':name,'log':log})
        if best_record and best_record['stats']['violation_count']==0:
            break
    result={'problem':'vectorized local search for complete E11 Wang occupation support','field':'F2','rank_s':args.rank,'best':best_record,'logs':all_logs,'membership_path':str(args.membership),'cache_path':str(args.cache),'elapsed_sec':time.time()-t_all,'meaning':'A zero-violation support is complete occupation-feasible and must be tested by fixed-A XOR SAT; nonzero local minima are local evidence only.'}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('BEST',json.dumps(best_record,sort_keys=True)[:4000])
    print('wrote',args.out)

if __name__=='__main__':
    main()
