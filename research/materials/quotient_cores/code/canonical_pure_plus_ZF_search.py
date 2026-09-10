#!/usr/bin/env python3
"""analysis: Z(F) search from the pure row-column anti core.

The nine pure free pairs v=e_{b,k}, w=e_{a,k} for a<b have
L_anti plus the three off-diagonal L_sym directions in F∩L1, so qdim=3.
This is a contrasting anti-feasible core to transported Laderman, where qdim=6.
We add k random free orbits and test the exact Z(F) condition for rank-22
skeletons m=9+k, f=22-2m.
"""
from __future__ import annotations
import argparse, json, random, time, importlib.util
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "zF_search"
OUT.mkdir(parents=True, exist_ok=True)

spec = importlib.util.spec_from_file_location("zcore", SCRIPT_DIR / "zF_laderman_anti_span_search.py")
z = importlib.util.module_from_spec(spec)
spec.loader.exec_module(z)

def canonical_projective(v, p):
    v = np.asarray(v, dtype=np.int64) % p
    if not np.any(v): return None
    first = int(np.nonzero(v)[0][0])
    return (v * z.inv(v[first], p)) % p

def random_projective(rng, p):
    while True:
        v = np.array([rng.randrange(p) for _ in range(9)], dtype=np.int64)
        c = canonical_projective(v, p)
        if c is not None: return c

def random_pair(rng, p):
    while True:
        v = random_projective(rng, p); w = random_projective(rng, p)
        if z.rank(np.vstack([v,w])%p,p)==2: return v,w

def pure_core_pairs(p):
    pairs=[]
    for a in range(3):
        for b in range(a+1,3):
            for k in range(3):
                v=np.zeros(9,dtype=np.int64); w=np.zeros(9,dtype=np.int64)
                v[3*b+k]=1; w[3*a+k]=1
                pairs.append((v%p,w%p))
    return pairs

def light_dims(p,pairs,L1):
    F=[]
    for v,w in pairs: F.extend(z.free_slots_from_pair(v,w,p))
    F=np.vstack(F)%p; Fb,_=z.row_basis(F,p)
    rF=Fb.shape[0]; rS=z.rank(np.vstack([Fb,L1])%p,p); Fcap=rF+z.rank(L1,p)-rS; qdim=rS-rF
    return rF,rS,Fcap,qdim

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--p',type=int,default=3); ap.add_argument('--samples',type=int,default=5000); ap.add_argument('--k-list',default='0,1,2'); ap.add_argument('--seed',type=int,default=6803); ap.add_argument('--time-budget',type=float,default=600)
    args=ap.parse_args(); p=args.p; rng=random.Random(args.seed); t0=time.time(); ks=[int(x) for x in args.k_list.split(',') if x!='']
    L1=z.build_L1(p); Lsym,Lanti=z.build_Lsym_Lanti_81(p); X,Sq=z.precompute_fixed_squares(p)
    core=pure_core_pairs(p)
    core_rec=z.analyze_configuration(p,core,X,Sq,L1,Lsym,Lanti,f_allowed=4,want_replay=False)
    out={'field':f'F_{p}','seed':args.seed,'samples_requested_per_k':args.samples,'time_budget_sec':args.time_budget,'pure_core_record':core_rec,'k_results':{},'hits':[], 'interpretation':'Pure row-column core has qdim 3; random extra orbits test whether Z(F) can supply remaining fixed terms or whether F can absorb more L_sym.'}
    for k in ks:
        m=9+k; f_allowed=22-2*m
        if f_allowed<0: continue
        summ={'k_extra_orbits':k,'m':m,'f_allowed':f_allowed,'samples_done':0,'rankF_hist':{},'F_cap_L1_hist':{},'qdim_hist':{},'candidate_qdim_le_f_count':0,'full_Z_tests':0,'Z_count_hist':{},'Z_qrank_hist':{},'hit_count':0,'best':[]}
        best=[]
        samples=1 if k==0 else args.samples
        for s in range(samples):
            if time.time()-t0>args.time_budget: summ['timed_out']=True; break
            extras=[random_pair(rng,p) for _ in range(k)]
            pairs=list(core)+extras
            rF,rS,Fcap,qdim=light_dims(p,pairs,L1); summ['samples_done']+=1
            for name,val in [('rankF_hist',rF),('F_cap_L1_hist',Fcap),('qdim_hist',qdim)]: summ[name][str(int(val))]=summ[name].get(str(int(val)),0)+1
            rec=None
            if qdim<=f_allowed:
                summ['candidate_qdim_le_f_count']+=1; rec=z.analyze_configuration(p,pairs,X,Sq,L1,Lsym,Lanti,f_allowed=f_allowed,want_replay=False); summ['full_Z_tests']+=1
                summ['Z_count_hist'][str(rec['Z_fixed_squares_count_over_Fp'])]=summ['Z_count_hist'].get(str(rec['Z_fixed_squares_count_over_Fp']),0)+1
                summ['Z_qrank_hist'][str(rec['Z_quotient_rank'])]=summ['Z_qrank_hist'].get(str(rec['Z_quotient_rank']),0)+1
                if rec['rank22_condition_met_by_Z']:
                    rec2=z.analyze_configuration(p,pairs,X,Sq,L1,Lsym,Lanti,f_allowed=f_allowed,want_replay=True)
                    hit={'k':k,'m':m,'sample':s,'record':rec2,'extra_pairs':[{'v':[int(x) for x in v.tolist()],'w':[int(x) for x in w.tolist()]} for v,w in extras]}
                    out['hits'].append(hit); summ['hit_count']+=1
                    if rec2['replay'] and rec2['replay'].get('full_T333_replay'):
                        summ['best']=best; out['k_results'][str(k)]=summ; path=OUT/f'canonical_pure_plus_ZF_F{p}.json'; path.write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2)); print(f'SAVED {path}'); return
            score=(Fcap,-qdim,0 if rec is None else rec['Z_quotient_rank'],0 if rec is None else rec['Z_fixed_squares_count_over_Fp'])
            comp={'score':[int(score[0]),int(score[1]),int(score[2]),int(score[3])],'sample':int(s),'rankF':int(rF),'rankF_plus_L1':int(rS),'F_cap_L1_dim':int(Fcap),'qdim':int(qdim),'extra_pairs':[{'v':[int(x) for x in v.tolist()],'w':[int(x) for x in w.tolist()]} for v,w in extras]}
            if rec is not None:
                comp['Z_fixed_squares_count_over_Fp']=int(rec['Z_fixed_squares_count_over_Fp']); comp['Z_quotient_rank']=int(rec['Z_quotient_rank']); comp['rank22_condition_met_by_Z']=bool(rec['rank22_condition_met_by_Z']); comp['selected_Z_indices_for_basis']=rec['selected_Z_indices_for_basis']
            best.append(comp); best=sorted(best,key=lambda x:tuple(x['score']),reverse=True)[:20]
        summ['best']=best; out['k_results'][str(k)]=summ
    path=OUT/f'canonical_pure_plus_ZF_F{p}.json'; path.write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2)); print(f'SAVED {path}')
if __name__=='__main__': main()
