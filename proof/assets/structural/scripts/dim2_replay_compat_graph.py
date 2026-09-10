#!/usr/bin/env python3
"""research: repaired dim-2 replay and simultaneous high-rank compatibility graph.

This script has two purposes.

1. Reconstruct the dim-2 Wang occupation row systems using the correct orbit-
   level overlay semantics: every generated supernode key is mapped through
   Wang's closed orbit cache key_to_orbit before any raised orbit lower bound is
   applied.  This repairs the representative-only overlay mistake noted in
   research.

2. Use the resulting dim-2 lower-bound status simultaneously.  In a hypothetical
   rank-20 full decomposition, the A-slot split flattening gives

       sum_t (rank(A_t)-1) >= 7.

   The one-dimensional quotient lower bound 19 rules out two terms with the same
   high-rank A-direction (rank>=2), since quotienting by that line would leave at
   most 18 terms.  For distinct high-rank directions a,b, if span(a,b) belongs
   to a dim-2 orbit whose quotient lower bound is at least 19, quotienting by
   their span again leaves at most 18 terms and contradicts that lower bound.

   Therefore all high-rank A-directions in any surviving rank-20 candidate must
   form a clique in the graph whose vertices are the 462 rank>=2 nonzero 3x3
   matrices, with an edge precisely when the pair's dim-2 orbit is still allowed
   (current LB < 19).  The vertex weight is rank(a)-1.  If the exact maximum
   clique weight is <7, the dim-2 reduction plus split-flattening closes the
   rank-20 case, conditional on the orbit raises being independently certified.

The script records exact graph/orbit counts and an exact maximum-weight clique
by branch-and-bound.  CP-SAT INFEASIBLE statuses in the replay are solver
outputs, not proof certificates by themselves.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import time
from collections import Counter, defaultdict
from functools import lru_cache
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:
    cp_model = None

PROFILE = Path('assets/quotients/data/wang_f2_lb20/cert_profile.json')
LUT_PATH = Path('assets/quotients/data/wang_f2_lb20/wang_subspace_lut.pkl')
CACHE_PATH = Path('assets/quotients/data/wang_f2_lb20/wang_orbit_closed_cache.pkl')
CASCADE = Path('assets/occupation/data/wang_analysis/cascade/dim3_raises_to_dim2.json')
OUTDIR = Path('assets/structural/data/dim2_compat')


def popcnt(x:int)->int: return int(x).bit_count()


def rref_basis(rows: Iterable[int], nbits:int=9)->Tuple[int,...]:
    basis: List[int] = []
    for x0 in rows:
        x=int(x0)
        if x==0: continue
        for rb in basis:
            p=rb.bit_length()-1
            if (x>>p)&1:
                x ^= rb
        if x==0: continue
        p=x.bit_length()-1
        for i,rb in enumerate(basis):
            if (rb>>p)&1:
                basis[i]=rb^x
        basis.append(x)
        basis.sort(key=lambda z:z.bit_length(), reverse=True)
    return tuple(basis)


def pack_basis(basis: Sequence[int])->int:
    x=0
    for i,b in enumerate(basis):
        x |= int(b) << (9*i)
    return (x<<4)|len(basis)


def in_span(v0:int, rref: Sequence[int])->bool:
    v=int(v0)
    for rb in rref:
        p=int(rb).bit_length()-1
        if p>=0 and ((v>>p)&1):
            v ^= int(rb)
    return v==0


def free_bits(W: Sequence[int], nbits:int=9)->List[int]:
    piv={int(rb).bit_length()-1 for rb in W if int(rb)}
    return [i for i in range(nbits) if i not in piv]


def lift_q(q:int, fb: Sequence[int])->int:
    v=0
    for i,bit in enumerate(fb):
        if (int(q)>>i)&1:
            v |= 1<<bit
    return v


@lru_cache(maxsize=None)
def all_subspace_bases(k:int)->Tuple[Tuple[int,...],...]:
    spaces={tuple()}
    for v in range(1,1<<k):
        add=[]
        for sp in spaces:
            if not in_span(v, sp):
                add.append(rref_basis((*sp,v), k))
        spaces.update(add)
    return tuple(sorted(spaces, key=lambda b:(len(b),b)))


@lru_cache(maxsize=None)
def strict_nonzero_proper_subspaces(k:int)->Tuple[Tuple[int,...],...]:
    return tuple(b for b in all_subspace_bases(k) if 0<len(b)<k)


@lru_cache(maxsize=None)
def mask_from_qbasis(qbasis: Tuple[int,...])->int:
    mask=0
    d=len(qbasis)
    for m in range(1,1<<d):
        q=0
        for i,b in enumerate(qbasis):
            if (m>>i)&1:
                q ^= int(b)
        mask |= 1 << (q-1)
    return mask


def rows3(x:int)->List[int]:
    return [sum(((int(x)>>(3*i+j))&1)<<j for j in range(3)) for i in range(3)]


def rank3(x:int)->int:
    piv: Dict[int,int]={}; r=0
    for row in rows3(x):
        y=row
        while y:
            p=y.bit_length()-1
            if p in piv:
                y ^= piv[p]
            else:
                piv[p]=y; r+=1; break
    return r


def nonzero_span(basis: Sequence[int])->List[int]:
    out=[]
    for m in range(1,1<<len(basis)):
        v=0
        for i,b in enumerate(basis):
            if (m>>i)&1:
                v ^= int(b)
        out.append(v)
    return sorted(out)


def load_json(path:Path):
    return json.loads(path.read_text())


def load_lut_cache():
    with LUT_PATH.open('rb') as f:
        d=pickle.load(f)
    lut=d['lut'] if isinstance(d,dict) and 'lut' in d else d
    with CACHE_PATH.open('rb') as f:
        cache=pickle.load(f)
    return lut, cache


def load_dim3_raises()->Dict[int,int]:
    d=load_json(CASCADE)
    return {int(k):int(v) for k,v in d.get('initial_raises_from_dim3',{}).items()}


def load_all_recorded_raises()->Dict[int,int]:
    d=load_json(CASCADE)
    return {int(k):int(v) for k,v in d.get('all_raises_after_tests',{}).items()}


def orbit_lbs_from_cache(cache, raises: Dict[int,int])->Dict[int,int]:
    lbs={int(o['position']): int(o.get('raw_lb', o.get('rank_lower_bound',0))) for o in cache['orbits']}
    for pos,val in raises.items():
        if int(pos) in lbs and int(val)>lbs[int(pos)]:
            lbs[int(pos)]=int(val)
    return lbs


def current_lb_for_key(key:int, lut:Dict[int,int], cache, orbit_lbs:Dict[int,int])->int:
    pos=cache['key_to_orbit'].get(int(key))
    if pos is not None:
        return int(orbit_lbs[int(pos)])
    return int(lut[int(key)])


def node_rows(W_basis: Sequence[int], lut:Dict[int,int], cache, orbit_lbs:Dict[int,int], support_size:int):
    W=rref_basis(W_basis,9); k=9-len(W); fb=free_bits(W,9)
    constraints: Dict[int,int] = {}
    cap_hist=Counter(); dim_hist=Counter(); source_lb_hist=Counter(); pop_hist=Counter(); orbit_hist=Counter()
    missing=0; neg=0; examples=[]
    for qbasis in strict_nonzero_proper_subspaces(k):
        U=rref_basis((*W,*[lift_q(q,fb) for q in qbasis]),9)
        key=pack_basis(U)
        try:
            lb=current_lb_for_key(key,lut,cache,orbit_lbs)
        except KeyError:
            missing += 1; continue
        cap=int(support_size)-int(lb)
        mask=mask_from_qbasis(tuple(qbasis))
        if mask not in constraints or cap<constraints[mask]:
            constraints[mask]=cap
        pos=cache['key_to_orbit'].get(int(key))
        if pos is not None:
            orbit_hist[int(pos)]+=1
        cap_hist[cap]+=1; dim_hist[len(qbasis)]+=1; source_lb_hist[int(lb)]+=1; pop_hist[popcnt(mask)]+=1
        if cap<0: neg+=1
        if len(examples)<15:
            examples.append({'qdim':len(qbasis),'U_dim':len(U),'orbit_pos':None if pos is None else int(pos),'lb':int(lb),'cap':int(cap),'mask_popcount':popcnt(mask),'U_basis':[int(x) for x in U]})
    rows=sorted(constraints.items(), key=lambda mc:(mc[1],popcnt(mc[0]),mc[0]))
    meta={'quotient_dim':k,'strict_subspace_rows':len(strict_nonzero_proper_subspaces(k)),'unique_masks':len(rows),'missing':missing,'negative_cap_rows':neg,
          'cap_hist':{str(k):int(v) for k,v in sorted(cap_hist.items())},
          'source_lb_hist':{str(k):int(v) for k,v in sorted(source_lb_hist.items())},
          'quotient_subspace_dim_hist':{str(k):int(v) for k,v in sorted(dim_hist.items())},
          'mask_popcount_hist':{str(k):int(v) for k,v in sorted(pop_hist.items())},
          'supernode_orbit_hist_head':{str(k):int(v) for k,v in sorted(orbit_hist.items())[:30]},
          'examples_head':examples}
    return rows,meta


def solve_cp(rows: Sequence[Tuple[int,int]], k:int, L:int, time_limit:float, workers:int):
    if cp_model is None:
        return {'status':'NO_ORTOOLS','feasible':None}
    model=cp_model.CpModel(); npts=(1<<k)-1
    xs=[model.NewIntVar(0,L,f'x_{i+1}') for i in range(npts)]
    model.Add(sum(xs)==L)
    for mask,cap in rows:
        if cap<0:
            model.Add(0<=-1); continue
        if cap>=L:
            continue
        pts=[i for i in range(npts) if (int(mask)>>i)&1]
        if pts:
            model.Add(sum(xs[i] for i in pts)<=int(cap))
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(time_limit); solver.parameters.num_search_workers=int(workers); solver.parameters.random_seed=9032
    t0=time.time(); st=solver.Solve(model); elapsed=time.time()-t0; name=solver.StatusName(st)
    if st in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        sol=[int(solver.Value(x)) for x in xs]
        max_excess=max((sum(sol[i] for i in range(npts) if (int(mask)>>i)&1)-int(cap) for mask,cap in rows), default=0)
        nz=[(i+1,v) for i,v in enumerate(sol) if v]
        return {'status':name,'feasible':True,'elapsed_sec':elapsed,'conflicts':int(solver.NumConflicts()),'branches':int(solver.NumBranches()),'weight':sum(sol),'max_excess_replay':int(max_excess),'support_nonzero_count':len(nz),'max_multiplicity':max((v for _i,v in nz), default=0),'solution_head':nz[:80]}
    if st==cp_model.INFEASIBLE:
        return {'status':name,'feasible':False,'elapsed_sec':elapsed,'conflicts':int(solver.NumConflicts()),'branches':int(solver.NumBranches())}
    return {'status':name,'feasible':None,'elapsed_sec':elapsed,'conflicts':int(solver.NumConflicts()),'branches':int(solver.NumBranches())}


def dim2_replay(lut, cache, time_limit:float, workers:int):
    prof=load_json(PROFILE)
    dim3_raises=load_dim3_raises()
    orbit_lbs=orbit_lbs_from_cache(cache, dim3_raises)
    records=[]
    for rec in prof['dimension_2_orbits']:
        idx=int(rec['index'])
        W=[int(x) for x in rec['constraint_values']]
        ranks=[rank3(x) for x in nonzero_span(W)]
        old=int(rec['rank_lower_bound'])
        L=old
        rows,meta=node_rows(W,lut,cache,orbit_lbs,L)
        row_hash_input=';'.join(f'{m}:{c}' for m,c in rows)
        sol=solve_cp(rows,9-len(rref_basis(W,9)),L,time_limit,workers)
        raised_by_replay = (sol.get('feasible') is False)
        current_lb=old + (1 if raised_by_replay else 0)
        records.append({'index':idx,'basis':W,'basis_rref':list(rref_basis(W,9)),'old_lb':old,'support_size_tested':L,'rank_pattern':ranks,'rank_ge2_count':sum(1 for r in ranks if r>=2),'relevant_two_high_rank_generators':sum(1 for r in ranks if r>=2)>=2,'row_meta':meta,'row_sha256':hashlib.sha256(row_hash_input.encode()).hexdigest(),'solve':sol,'replay_raises_to':current_lb if raised_by_replay else old})
        print('replay idx',idx,'ranks',ranks,'old',old,'rows',len(rows),'cap_hist',meta['cap_hist'],'status',sol['status'],'feasible',sol.get('feasible'),flush=True)
    return records


def pair_orbit(a:int,b:int,cache)->int:
    key=pack_basis(rref_basis([a,b],9))
    pos=cache['key_to_orbit'].get(int(key))
    if pos is None:
        raise KeyError(f'no orbit for dim2 key {key}')
    return int(pos)


def exact_max_weight_clique(adj: List[int], weights: List[int]):
    n=len(weights)
    order=sorted(range(n), key=lambda v:(weights[v], (adj[v]).bit_count()), reverse=True)
    pos={v:i for i,v in enumerate(order)}
    # Reorder graph to improve recursion.
    rw=[weights[v] for v in order]
    radj=[0]*n
    for i,v in enumerate(order):
        m=0; av=adj[v]
        for u in range(n):
            if (av>>u)&1:
                m |= 1<<pos[u]
        radj[i]=m

    best_w=0; best_cliques: List[List[int]]=[]; nodes=0

    def color_bound(P:int):
        """Greedy color classes for unweighted graph, with weight-sum color bound.

        Returns vertices in selection order and a nondecreasing upper bound on
        the additional weight available up to that prefix.  Because each color
        class contributes at most its maximum vertex weight to a clique, the sum
        of class maxima is a valid weighted clique bound.
        """
        verts=[]; bounds=[]; classes=[]
        U=P
        while U:
            color_set=U; cls=[]; maxw=0
            while color_set:
                lsb=color_set & -color_set; v=lsb.bit_length()-1
                cls.append(v); maxw=max(maxw,rw[v])
                U &= ~lsb
                color_set &= ~lsb
                color_set &= ~radj[v]
            classes.append(maxw)
            # Vertices assigned in this color class get the current cumulative
            # bound after all colors up to this one are available.
            cum=sum(classes)
            for v in cls:
                verts.append(v); bounds.append(cum)
        return verts,bounds

    def expand(P:int, cur_w:int, clique:List[int]):
        nonlocal best_w,best_cliques,nodes
        nodes += 1
        if not P:
            if cur_w>best_w:
                best_w=cur_w; best_cliques=[clique.copy()]
            elif cur_w==best_w and len(best_cliques)<64:
                best_cliques.append(clique.copy())
            return
        verts,bounds=color_bound(P)
        # Tomita style: process from end; bounds[i] upper-bounds remaining branch.
        for i in range(len(verts)-1,-1,-1):
            if cur_w + bounds[i] < best_w:
                return
            v=verts[i]
            if not ((P>>v)&1):
                continue
            if cur_w + rw[v] + sum(rw[u] for u in range(n) if ((P & radj[v])>>u)&1) < best_w:
                P &= ~(1<<v); continue
            clique.append(v)
            expand(P & radj[v], cur_w+rw[v], clique)
            clique.pop()
            P &= ~(1<<v)
            if cur_w + bounds[i] < best_w:
                return
    expand((1<<n)-1,0,[])
    # Convert reordered indices back to original vertex indices.
    orig_cliques=[[order[i] for i in cl] for cl in best_cliques]
    return {'max_weight':int(best_w),'num_best_cliques_stored':len(orig_cliques),'best_cliques':orig_cliques,'search_nodes':int(nodes)}


def brute_force_small_weight_check(adj: List[int], weights: List[int], target:int=7):
    # Independent bounded search for existence of a clique of weight >= target;
    # useful because target is tiny and the mathematical conclusion only needs
    # the threshold.  Recurses on original ordering with suffix weight bounds.
    n=len(weights)
    order=sorted(range(n), key=lambda v:(weights[v], adj[v].bit_count()), reverse=True)
    suffix=[0]*(n+1)
    for i in range(n-1,-1,-1):
        suffix[i]=suffix[i+1]+weights[order[i]]
    calls=0; witness=None
    def rec(i:int, cand:int, w:int, chosen:List[int]):
        nonlocal calls,witness
        calls+=1
        if w>=target:
            witness=chosen.copy(); return True
        if i>=n or w+suffix[i]<target:
            return False
        # choose next available according to order
        while i<n and not ((cand>>order[i])&1):
            i+=1
        if i>=n or w+suffix[i]<target:
            return False
        v=order[i]
        if rec(i+1, cand & adj[v], w+weights[v], chosen+[v]):
            return True
        if rec(i+1, cand & ~(1<<v), w, chosen):
            return True
        return False
    exists=rec(0,(1<<n)-1,0,[])
    return {'target':target,'exists':bool(exists),'witness':witness,'calls':calls}


def compatibility_graph(cache, current_lb_by_pos: Dict[int,int]):
    vertices=[v for v in range(1,512) if rank3(v)>=2]
    ranks=[rank3(v) for v in vertices]
    weights=[r-1 for r in ranks]
    n=len(vertices)
    adj=[0]*n
    orbit_pair_counts=Counter(); allowed_pair_counts=Counter(); excluded_pair_counts=Counter()
    missing=0
    for i in range(n):
        a=vertices[i]
        for j in range(i+1,n):
            b=vertices[j]
            pos=pair_orbit(a,b,cache)
            orbit_pair_counts[pos]+=1
            lb=int(current_lb_by_pos.get(pos,0))
            if lb<19:
                adj[i] |= 1<<j; adj[j] |= 1<<i
                allowed_pair_counts[pos]+=1
            else:
                excluded_pair_counts[pos]+=1
    degree_hist=Counter(x.bit_count() for x in adj)
    # Components of allowed graph.
    seen=0; comps=[]
    for i in range(n):
        if (seen>>i)&1: continue
        stack=[i]; seen|=1<<i; comp=[]
        while stack:
            v=stack.pop(); comp.append(v)
            m=adj[v] & ~seen
            while m:
                lsb=m & -m; u=lsb.bit_length()-1
                seen |= lsb; stack.append(u); m ^= lsb
        comps.append(comp)
    comp_stats=sorted([{'size':len(c),'weight_sum':sum(weights[i] for i in c),'rank_hist':dict(Counter(ranks[i] for i in c))} for c in comps], key=lambda d:(d['weight_sum'],d['size']), reverse=True)
    clique=exact_max_weight_clique(adj,weights)
    threshold=brute_force_small_weight_check(adj,weights,7)
    best_records=[]
    for cl in clique['best_cliques'][:20]:
        mats=[vertices[i] for i in cl]
        edge_orbits=Counter()
        for x in range(len(cl)):
            for y in range(x+1,len(cl)):
                edge_orbits[pair_orbit(mats[x],mats[y],cache)] += 1
        best_records.append({'indices':cl,'matrices':mats,'hex':[hex(x) for x in mats],'ranks':[rank3(x) for x in mats],'weight':sum(rank3(x)-1 for x in mats),'edge_orbit_hist':{str(k):int(v) for k,v in sorted(edge_orbits.items())}})
    return {'vertex_count':n,'vertex_rank_hist':{str(k):int(v) for k,v in sorted(Counter(ranks).items())},'vertex_weight_sum':sum(weights),
            'edge_count_allowed':sum(a.bit_count() for a in adj)//2,'degree_hist':{str(k):int(v) for k,v in sorted(degree_hist.items())},
            'orbit_pair_counts':{str(k):int(v) for k,v in sorted(orbit_pair_counts.items())},
            'allowed_pair_counts':{str(k):int(v) for k,v in sorted(allowed_pair_counts.items())},
            'excluded_pair_counts':{str(k):int(v) for k,v in sorted(excluded_pair_counts.items())},
            'components':comp_stats[:30],'component_count':len(comps),
            'max_weight_clique':{k:v for k,v in clique.items() if k!='best_cliques'},'best_clique_records':best_records,
            'threshold_weight7_check':threshold}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--time-limit',type=float,default=60.0)
    ap.add_argument('--workers',type=int,default=8)
    ap.add_argument('--skip-replay',action='store_true')
    ap.add_argument('--out',type=Path,default=OUTDIR/'dim2_replay_compat_graph.json')
    args=ap.parse_args()
    t0=time.time(); OUTDIR.mkdir(parents=True,exist_ok=True)
    lut,cache=load_lut_cache()
    replay_records=[]
    if not args.skip_replay:
        replay_records=dim2_replay(lut,cache,args.time_limit,args.workers)
    raw_lbs={int(o['position']):int(o.get('raw_lb',0)) for o in cache['orbits']}
    all_raises=load_all_recorded_raises()
    current_lbs=orbit_lbs_from_cache(cache, all_raises)
    # Check one-dimensional line lower bounds across all 511 nonzero directions.
    line_stats=defaultdict(lambda: Counter())
    line_bad=[]
    for a in range(1,512):
        key=pack_basis(rref_basis([a],9)); pos=cache['key_to_orbit'].get(int(key)); lb=current_lbs[int(pos)] if pos is not None else lut[key]
        r=rank3(a); line_stats[r][lb]+=1
        if r>=2 and lb<19:
            line_bad.append({'a':a,'hex':hex(a),'rank':r,'orbit':None if pos is None else int(pos),'lb':int(lb)})
    graph=compatibility_graph(cache,current_lbs)
    out={'schema':'s0908_dim2_replay_compat_graph_v1',
         'meaning':'Correct orbit-level dim-2 occupation replay plus simultaneous compatibility graph on all high-rank A-directions. A max clique weight below 7 would close rank20 only after the recorded orbit raises have independent proof support.',
         'sources':{'profile':str(PROFILE),'lut':str(LUT_PATH),'cache':str(CACHE_PATH),'cascade':str(CASCADE)},
         'replay_records':replay_records,
         'replay_summary':{'raised_by_replay':[r['index'] for r in replay_records if r['solve'].get('feasible') is False], 'feasible':[r['index'] for r in replay_records if r['solve'].get('feasible') is True], 'unknown':[r['index'] for r in replay_records if r['solve'].get('feasible') is None]},
         'current_dim2_lbs_from_recorded_cascade':{str(i):int(current_lbs[i]) for i in range(478,492) if i in current_lbs},
         'line_lb_hist_by_matrix_rank':{str(r):{str(k):int(v) for k,v in sorted(c.items())} for r,c in sorted(line_stats.items())},
         'line_high_rank_lb_lt19':line_bad,
         'compatibility_graph':graph,
         'conditional_conclusion':{'split_flattening_required_weight':7,'max_allowed_clique_weight':graph['max_weight_clique']['max_weight'],'if_orbit_raises_certified_then_rank20_excluded_by_graph':bool(graph['max_weight_clique']['max_weight']<7 and not line_bad)},
         'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(args.out),'replay_summary':out['replay_summary'],'line_hist':out['line_lb_hist_by_matrix_rank'],'graph':{'vertices':graph['vertex_count'],'allowed_edges':graph['edge_count_allowed'],'max_weight':graph['max_weight_clique']['max_weight'],'best_cliques_stored':graph['max_weight_clique']['num_best_cliques_stored'],'threshold7_exists':graph['threshold_weight7_check']['exists'],'search_nodes':graph['max_weight_clique']['search_nodes'],'allowed_pair_counts':graph['allowed_pair_counts']} ,'conditional':out['conditional_conclusion'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))


if __name__=='__main__':
    main()
