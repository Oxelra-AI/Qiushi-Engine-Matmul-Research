#!/usr/bin/env python3
"""analysis: random multi-plane replacements of the pure (4,9) core over F3.

This samples rank-22 (m=9,f=4) tau-free spans near the pure row-column anti core
by replacing t of its nine planes with random decomposable planes.  Only samples
that still contain L_anti and have dim((F+L1)/F) <= 4 can possibly work; those are
then tested with the full fixed-square quotient condition from the compact exact
script.  A hit would be replayed by the imported routine.
"""
from __future__ import annotations
import argparse, json, random, time, importlib.util
from pathlib import Path
import numpy as np

SCRIPT_DIR=Path(__file__).resolve().parent
WS=SCRIPT_DIR.parent
OUT=WS/'data'/'zF_search'
OUT.mkdir(parents=True,exist_ok=True)

spec=importlib.util.spec_from_file_location('zcore', SCRIPT_DIR/'zF_laderman_anti_span_search.py')
z=importlib.util.module_from_spec(spec); spec.loader.exec_module(z)
spec2=importlib.util.spec_from_file_location('pcore', SCRIPT_DIR/'pure_one_replacement_compact.py')
pc=importlib.util.module_from_spec(spec2); spec2.loader.exec_module(pc)

def canonical_projective(v,p):
    v=np.asarray(v,dtype=np.int64)%p
    if not np.any(v): return None
    i=int(np.nonzero(v)[0][0]); return (v*z.inv(v[i],p))%p

def rand_proj(rng,p):
    while True:
        v=np.array([rng.randrange(p) for _ in range(9)],dtype=np.int64)
        c=canonical_projective(v,p)
        if c is not None: return c

def rand_pair(rng,p):
    while True:
        v=rand_proj(rng,p); w=rand_proj(rng,p)
        if z.rank(np.vstack([v,w])%p,p)==2: return v,w

def light(p,pairs,L1,Lanti81):
    F=pc.F_from_pairs(p,pairs); Fb,_=z.row_basis(F,p)
    rankF=Fb.shape[0]; rankS=z.rank(np.vstack([Fb,L1])%p,p); Fcap=rankF+z.rank(L1,p)-rankS; qdim=rankS-rankF
    anti_ok,_,_,anti_def=z.row_contains(Fb,Lanti81,p)
    return {'rankF':int(rankF),'rankF_plus_L1':int(rankS),'Fcap':int(Fcap),'qdim':int(qdim),'anti_ok':bool(anti_ok),'anti_defect':int(anti_def)}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--p',type=int,default=3); ap.add_argument('--samples',type=int,default=10000); ap.add_argument('--t-list',default='2,3,4'); ap.add_argument('--seed',type=int,default=6804); ap.add_argument('--time-budget',type=float,default=600)
    args=ap.parse_args(); p=args.p; rng=random.Random(args.seed); t0=time.time(); ts=[int(x) for x in args.t_list.split(',') if x]
    L1=z.build_L1(p); Lsym,Lanti81=z.build_Lsym_Lanti_81(p); X,Sq=z.precompute_fixed_squares(p); core=pc.pure_core_pairs(p)
    out={'field':f'F_{p}','seed':args.seed,'samples_requested_per_t':args.samples,'time_budget_sec':args.time_budget,'t_results':{},'hits':[], 'interpretation':'Random t-plane replacements of pure m=9 core; exact fixed-square quotient test is applied only when anti_ok and qdim<=4.'}
    for t in ts:
        summ={'t_replaced':t,'samples_done':0,'anti_ok_count':0,'possible_qdim_le4_count':0,'full_tests':0,'light_hist':{},'fixed_hist':{},'best':[],'hit_count':0}
        best=[]
        for s in range(args.samples):
            if time.time()-t0>args.time_budget: summ['timed_out']=True; break
            rems=rng.sample(range(9),t)
            pairs=list(core)
            for r in rems: pairs[r]=rand_pair(rng,p)
            info=light(p,pairs,L1,Lanti81); summ['samples_done']+=1
            key=(info['anti_ok'],info['anti_defect'],info['Fcap'],info['qdim'],info['rankF'])
            summ['light_hist'][str(key)]=summ['light_hist'].get(str(key),0)+1
            rec=None
            if info['anti_ok']:
                summ['anti_ok_count']+=1
                if info['qdim']<=4:
                    summ['possible_qdim_le4_count']+=1
                    rec=pc.quotient_test(p,pairs,L1,Sq,4); summ['full_tests']+=1
                    fkey=(rec['Fcap'],rec['qdim'],rec.get('Z_count',-1),rec.get('Z_rank',-1),rec.get('mode'),rec.get('hit'))
                    summ['fixed_hist'][str(fkey)]=summ['fixed_hist'].get(str(fkey),0)+1
                    if rec.get('hit'):
                        summ['hit_count']+=1
                        out['hits'].append({'t':t,'sample':s,'removed':rems,'record':rec,'replacement_pairs':[{'index':r,'v':[int(x) for x in pairs[r][0].tolist()],'w':[int(x) for x in pairs[r][1].tolist()]} for r in rems]})
            score=(1 if rec and rec.get('hit') else 0, 1 if info['anti_ok'] else 0, info['Fcap'], -info['qdim'], 0 if rec is None else rec.get('Z_rank',0), 0 if rec is None else rec.get('Z_count',0))
            comp={'score':[int(x) for x in score],'sample':s,'removed':rems,'light':info}
            if rec is not None: comp['fixed']={k:v for k,v in rec.items() if k not in ('group_histogram_(size,rank,defect,contains)','best_groups')}
            best.append(comp); best=sorted(best,key=lambda x:tuple(x['score']),reverse=True)[:20]
        summ['best']=best; out['t_results'][str(t)]=summ
    path=OUT/f'pure_multi_replacement_random_F{p}.json'; path.write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2)); print(f'SAVED {path}')
if __name__=='__main__': main()
