#!/usr/bin/env python3
"""analysis: full A-side Boolean Wang CEGAR with conditional re-pivot cuts.

This model works with Boolean variables z_a for the 511 nonzero full A-directions.
For n=20 this is justified as a necessary-condition search because the complete
full Wang table has one-dimensional cap 1 rows; hence a valid length-20 A
multiset cannot repeat a nonzero direction.  The model can impose a fixed pivot
and quotient branch constraints, but it also includes full-direction conditions
that couple other selected rank-2 pivots:

    sum_{b in B(a,C)} z_b + 9 z_a <= 20.

Candidate supports are replayed against the complete full Wang LUT; any
INFEASIBLE status is only for the active rows actually encoded, while a complete
absence of full-LUT violations would still be only A-side evidence, not a full
bilinear decomposition.
"""
from __future__ import annotations
import argparse, hashlib, json, pickle, sys, time
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model

ROOT=Path('research/research_record')
S04=Path('scripts')
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import unpack_basis  # type: ignore

LUT_PATH=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
COND_PATH=ROOT/'workspace/data/quotient_lift/conditional_cuts/conditional_rank2_cut_masks_from_two_orbits.json'
OUTDIR=ROOT/'workspace/data/quotient_lift/conditional_cuts'
OUTDIR.mkdir(parents=True,exist_ok=True)
PIVOTS={'rank2':17,'rank3':273}


def sha_file(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''):
            h.update(c)
    return h.hexdigest()


def load_lut(path:Path):
    with path.open('rb') as f: payload=pickle.load(f)
    return payload['lut'], payload.get('meta',{})


def subspace_mask_from_basis(basis):
    pts=[0]
    for b in basis:
        pts += [x^int(b) for x in pts]
    m=0
    for a in pts:
        if a: m |= 1<<a
    return m


def points_from_mask(mask:int, maxbit:int=512):
    return [i for i in range(1,maxbit) if (mask>>i)&1]


def reduce_by_pivots(x:int,pairs):
    y=int(x)
    for hb,b in pairs:
        if (y>>hb)&1:
            y ^= int(b)
            if y==0: return 0
    return y


def in_span(x:int,pairs)->bool:
    return reduce_by_pivots(x,pairs)==0


def section_lift(qpoint:int,pivot:int)->int:
    h=pivot.bit_length()-1
    return (qpoint & ((1<<h)-1)) | ((qpoint>>h)<<(h+1))


def bits_to_mat(mask:int):
    return [[(mask>>(3*i+j))&1 for j in range(3)] for i in range(3)]


def gf2_rank_mat(A):
    M=[row[:] for row in A]; r=0
    for c in range(3):
        piv=None
        for i in range(r,3):
            if M[i][c]: piv=i; break
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]
        for i in range(3):
            if i!=r and M[i][c]: M[i]=[M[i][j]^M[r][j] for j in range(3)]
        r+=1
    return r

RANKS={a:gf2_rank_mat(bits_to_mat(a)) for a in range(1,512)}


def build_initial_rows(lut,n:int,initial_dim:int,initial_cap:int):
    rows=[]; row_keys=set(); cap_hist=Counter(); dim_hist=Counter(); skipped=Counter(); t0=time.time()
    for idx,(key,lb0) in enumerate(lut.items()):
        basis=unpack_basis(int(key)); d=len(basis); cap=n-int(lb0)
        if d>initial_dim: continue
        if cap<0 or cap>=n or cap>initial_cap: continue
        mask=subspace_mask_from_basis(basis)
        active=mask.bit_count()
        if active<=cap:
            skipped['tautological_bool']+=1; continue
        k=(mask,cap)
        if k in row_keys:
            skipped['duplicate']+=1; continue
        row_keys.add(k); rows.append({'idx':idx,'dim':d,'lb':int(lb0),'cap':int(cap),'mask':mask,'active':active,'basis':list(map(int,basis))})
        cap_hist[cap]+=1; dim_hist[d]+=1
    return rows,row_keys,{'rows':len(rows),'cap_hist':dict(sorted(cap_hist.items())),'dim_hist':dict(sorted(dim_hist.items())),'skipped':dict(skipped),'elapsed_sec':time.time()-t0}


def load_conditionals(path:Path):
    data=json.loads(path.read_text())
    cuts=[]; seen=set(); coeff_hist=Counter()
    for r in data['conditional_cuts']:
        a=int(r['pivot_a']); Bmask=int(r['B_mask_hex'],16)
        if (Bmask>>a)&1: raise AssertionError('conditional B contains pivot')
        key=(a,Bmask)
        if key in seen: continue
        seen.add(key)
        B=points_from_mask(Bmask,512)
        coeff_hist[len(B)]+=1
        cuts.append({'pivot_a':a,'Bmask':Bmask,'B':B,'source_index':r.get('source_index'),'cut_index':r.get('cut_index')})
    return cuts, {'path':str(path),'sha256':sha_file(path),'count':len(cuts),'B_size_hist':dict(sorted(coeff_hist.items()))}


def solve_model(rows, conditionals, n:int, pivot:int|None, force_q:set[int], forbid_q:set[int], use_rank_sum:bool, time_limit:float, seed:int):
    model=cp_model.CpModel(); z={a:model.NewBoolVar(f'z_{a}') for a in range(1,512)}
    model.Add(sum(z.values()) == n)
    if use_rank_sum:
        model.Add(sum(RANKS[a]*z[a] for a in range(1,512)) >= 27)
    if pivot is not None:
        model.Add(z[pivot] == 1)
        for p in force_q:
            s=section_lift(p,pivot); model.Add(z[s] + z[s^pivot] == 1)
        for p in forbid_q:
            s=section_lift(p,pivot); model.Add(z[s] == 0); model.Add(z[s^pivot] == 0)
    for r in rows:
        pts=points_from_mask(r['mask'],512)
        model.Add(sum(z[a] for a in pts) <= int(r['cap']))
    for c in conditionals:
        model.Add(sum(z[b] for b in c['B']) + 9*z[c['pivot_a']] <= 20)
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(time_limit); solver.parameters.num_search_workers=8; solver.parameters.random_seed=int(seed)
    t0=time.time(); st=solver.Solve(model); elapsed=time.time()-t0
    rec={'status':solver.StatusName(st),'solve_elapsed_sec':elapsed,'wall_time':solver.WallTime(),'conflicts':solver.NumConflicts(),'branches':solver.NumBranches(),'active_rows':len(rows),'conditional_cuts':len(conditionals)}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        support=[a for a in range(1,512) if solver.Value(z[a])]
        rec['support']=support; rec['rank_hist']=dict(sorted((str(k),int(v)) for k,v in Counter(RANKS[a] for a in support).items()))
        rec['rank_sum']=sum(RANKS[a] for a in support)
    return rec


def eval_conditionals(support, conditionals):
    S=set(map(int,support)); best=[]; viol=[]
    for i,c in enumerate(conditionals):
        za=1 if c['pivot_a'] in S else 0
        if not za: continue
        occ=sum(1 for b in c['B'] if b in S); lhs=occ+9
        r={'index':i,'pivot_a':c['pivot_a'],'occ_B':occ,'lhs':lhs,'B_selected':sorted([b for b in c['B'] if b in S]),'source_index':c.get('source_index')}
        best.append(r)
        if lhs>20: viol.append(r)
    best.sort(key=lambda r:(-r['lhs'],r['pivot_a'],r['index']))
    return {'active_tests':len(best),'violations':len(viol),'violating_pivot_count':len({r['pivot_a'] for r in viol}),'max_lhs':best[0]['lhs'] if best else None,'max_occ_B':best[0]['occ_B'] if best else None,'best_head':best[:20],'violation_head':viol[:20]}


def check_candidate(lut,support,n:int,max_report:int=5000):
    S=set(map(int,support)); viol=[]; cap_hist=Counter(); dim_hist=Counter(); excess_hist=Counter(); checked=0; t0=time.time()
    for idx,(key,lb0) in enumerate(lut.items()):
        cap=n-int(lb0)
        if cap>=n: continue
        basis=unpack_basis(int(key)); pairs=tuple((int(b).bit_length()-1,int(b)) for b in basis if b)
        occ=sum(1 for a in S if in_span(a,pairs))
        checked+=1
        if occ>cap:
            v={'idx':idx,'dim':len(basis),'lb':int(lb0),'cap':int(cap),'occ':int(occ),'excess':int(occ-cap),'basis':list(map(int,basis))}
            viol.append(v); cap_hist[cap]+=1; dim_hist[len(basis)]+=1; excess_hist[occ-cap]+=1
    viol.sort(key=lambda v:(-v['excess'],v['cap'],v['dim'],v['idx']))
    stats={'checked_rows':checked,'violation_count':len(viol),'violation_cap_hist':dict(sorted((str(k),int(v)) for k,v in cap_hist.items())),'violation_dim_hist':dict(sorted((str(k),int(v)) for k,v in dim_hist.items())),'violation_excess_hist':dict(sorted((str(k),int(v)) for k,v in excess_hist.items())),'elapsed_sec':time.time()-t0}
    return viol[:max_report], stats


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--n',type=int,default=20)
    ap.add_argument('--initial-dim',type=int,default=2)
    ap.add_argument('--initial-cap',type=int,default=2)
    ap.add_argument('--rounds',type=int,default=5)
    ap.add_argument('--time-per-round',type=float,default=120.0)
    ap.add_argument('--total-time',type=float,default=900.0)
    ap.add_argument('--add-limit',type=int,default=5000)
    ap.add_argument('--seed',type=int,default=25000)
    ap.add_argument('--pivot-name',choices=['rank2','rank3'],default=None)
    ap.add_argument('--force-quotient',default='')
    ap.add_argument('--forbid-quotient',default='')
    ap.add_argument('--no-conditionals',action='store_true')
    ap.add_argument('--no-rank-sum',action='store_true')
    ap.add_argument('--label',required=True)
    args=ap.parse_args(); t0=time.time()
    print(f'Loading LUT {LUT_PATH}',flush=True); lut,meta=load_lut(LUT_PATH); print(f'LUT rows={len(lut)} coverage={meta.get("coverage_ok")}',flush=True)
    rows,row_keys,init_stats=build_initial_rows(lut,args.n,args.initial_dim,args.initial_cap)
    conditionals=[]; cond_meta=None
    if not args.no_conditionals:
        conditionals,cond_meta=load_conditionals(COND_PATH)
    pivot=PIVOTS[args.pivot_name] if args.pivot_name else None
    force_q={int(x) for x in args.force_quotient.split(',') if x.strip()}
    forbid_q={int(x) for x in args.forbid_quotient.split(',') if x.strip()}
    print(f'initial_rows={len(rows)} init_stats={init_stats} conditionals={len(conditionals)} pivot={pivot} force_q={sorted(force_q)} forbid_q={len(forbid_q)}',flush=True)
    rounds=[]
    for rnd in range(args.rounds):
        if time.time()-t0 >= args.total_time: break
        tl=min(args.time_per_round,args.total_time-(time.time()-t0))
        print(f'round {rnd}: active_rows={len(rows)} tl={tl:.1f}',flush=True)
        rec=solve_model(rows,conditionals,args.n,pivot,force_q,forbid_q,not args.no_rank_sum,tl,args.seed+rnd)
        if 'support' not in rec:
            rounds.append(rec); print(f"  {rec['status']} no support",flush=True); break
        rec['conditional_eval']=eval_conditionals(rec['support'],conditionals) if conditionals else None
        viol,stats=check_candidate(lut,rec['support'],args.n)
        rec['full_check_stats']=stats; rec['violation_head']=viol[:50]
        print(f"  {rec['status']} rank_sum={rec['rank_sum']} rank_hist={rec['rank_hist']} cond_max={rec['conditional_eval']['max_lhs'] if rec['conditional_eval'] else None} full_viol={stats['violation_count']} cap_hist={stats['violation_cap_hist']}",flush=True)
        if not viol:
            rec['fully_full_wang_admissible']=True; rounds.append(rec); break
        new=0
        for v in viol[:args.add_limit]:
            mask=subspace_mask_from_basis(v['basis']); cap=int(v['cap']); active=mask.bit_count()
            if active<=cap: continue
            k=(mask,cap)
            if k not in row_keys:
                row_keys.add(k); rows.append({'idx':v['idx'],'dim':v['dim'],'lb':v['lb'],'cap':cap,'mask':mask,'active':active,'basis':v['basis']}); new+=1
        rec['new_rows_added']=new
        rounds.append(rec)
        if new==0: break
    out={'schema':'s0908_fullA_global_boolean_wang_cegar_v1','meaning':'Full A-side Boolean support CEGAR with optional fixed-pivot branch constraints, split-flattening rank-sum, complete-LUT replay, and conditional re-pivoted rank-2 lift-obstruction cuts. Infeasibility of active rows is not by itself full proof unless row/proof coverage is independently certified; full-LUT admissibility is only A-side evidence.',
         'source_lut':str(LUT_PATH),'source_lut_sha256':sha_file(LUT_PATH),'lut_coverage_ok':meta.get('coverage_ok'),
         'n':args.n,'initial_dim':args.initial_dim,'initial_cap':args.initial_cap,'initial_stats':init_stats,
         'conditionals_meta':cond_meta,'use_conditionals':not args.no_conditionals,'use_rank_sum':not args.no_rank_sum,
         'pivot_name':args.pivot_name,'pivot':pivot,'force_quotient':sorted(force_q),'forbid_quotient':sorted(forbid_q),
         'rounds':rounds,'final_row_count':len(rows),'final_status':rounds[-1]['status'] if rounds else 'no_rounds','found_full_wang_admissible':any(r.get('fully_full_wang_admissible') for r in rounds),'elapsed_sec':time.time()-t0}
    outp=OUTDIR/f'{args.label}.json'; outp.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('saved',outp,flush=True)
    print(json.dumps({'out':str(outp),'final_status':out['final_status'],'rounds':len(rounds),'found_full_wang_admissible':out['found_full_wang_admissible'],'final_row_count':out['final_row_count'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True),flush=True)

if __name__=='__main__': main()
