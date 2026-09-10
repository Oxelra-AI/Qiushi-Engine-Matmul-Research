#!/usr/bin/env python3
"""Exact F2 rank-19 search for the E11 restricted core via two-factor span.

For a 3-way tensor T in F2^{8 x 9 x 9}, a rank-R CPD exists iff there are R rank-one
8x9 matrices M_i=u_i v_i^T whose linear span contains the 9 C-slices T[:,:,c].
Then W is recovered by solving T[:,:,c]=sum_i W[i,c] M_i over F2.

This attacks research_record's E11 core directly, using the known 21-term cn122 restriction
as a warm start and searching replacements among all nonzero rank-one 8x9 matrices.
"""
from __future__ import annotations
import argparse, itertools, json, random, time
from pathlib import Path
import numpy as np

CORE_A_INDICES=[1,2,3,4,5,6,7,8]


def parse_qmm(path):
    terms=[]; cur=None
    for raw in Path(path).read_text().splitlines():
        line=raw.strip()
        if not line or line.startswith('#'): continue
        p=line.split()
        if p[0]=='term':
            if cur is not None: terms.append(cur)
            cur={'index':int(p[1])}
        elif p[0] in ('u','v','w'):
            cur[p[0]]=[int(x)&1 for x in p[1:]]
    if cur is not None: terms.append(cur)
    return terms


def mask_from_vec(vec):
    m=0
    for i,b in enumerate(vec):
        if int(b)&1: m |= 1<<i
    return m


def outer_mask(u_mask,v_mask,nv=9):
    x=0
    um=u_mask
    while um:
        lb=um & -um; a=lb.bit_length()-1; um^=lb
        vm=v_mask
        while vm:
            lbv=vm & -vm; b=lbv.bit_length()-1; vm^=lbv
            x ^= 1 << (a*nv+b)
    return x


def rank_ints(vecs):
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


def rref_basis(vecs):
    basis={}
    coeffs={}
    for idx,vv in enumerate(vecs):
        v=int(vv); c=1<<idx
        while v:
            p=v.bit_length()-1
            if p in basis:
                v ^= basis[p]; c ^= coeffs[p]
            else:
                basis[p]=v; coeffs[p]=c; break
    return basis, coeffs


def deficiency(cols, targets):
    rk=rank_ints(cols)
    rks=rank_ints(list(cols)+list(targets))
    return rks-rk, rk, rks


def solve_coeffs(cols, target, nbits=72):
    R=len(cols)
    rows=[]
    for bit in range(nbits):
        row=0
        for j,c in enumerate(cols):
            if (c>>bit)&1: row |= 1<<j
        if (target>>bit)&1: row |= 1<<R
        rows.append(row)
    pivots=[]; prow=0
    for col in range(R):
        piv=None
        for rr in range(prow,len(rows)):
            if (rows[rr]>>col)&1:
                piv=rr; break
        if piv is None: continue
        rows[prow],rows[piv]=rows[piv],rows[prow]
        for rr in range(len(rows)):
            if rr!=prow and ((rows[rr]>>col)&1):
                rows[rr]^=rows[prow]
        pivots.append(col); prow+=1
    for row in rows:
        if (row & ((1<<R)-1))==0 and ((row>>R)&1):
            return None
    sol=0
    for i,col in enumerate(pivots):
        if (rows[i]>>R)&1:
            sol |= 1<<col
    return sol


def core_targets(core):
    T=(core.astype(np.uint8)&1)
    targets=[]
    for c in range(T.shape[2]):
        x=0
        for a in range(T.shape[0]):
            for b in range(T.shape[1]):
                if int(T[a,b,c]): x |= 1<<(a*9+b)
        targets.append(x)
    return targets


def cn122_core_terms(qmm_path):
    terms=parse_qmm(qmm_path)
    out=[]; vanished=[]
    for idx,t in enumerate(terms):
        u=[t['u'][i] for i in CORE_A_INDICES]
        v=t['v']; w=t['w']
        um=mask_from_vec(u); vm=mask_from_vec(v); wm=mask_from_vec(w)
        if um==0 or vm==0 or wm==0:
            vanished.append(idx); continue
        out.append({'source_index':idx,'u':um,'v':vm,'w':wm,'uv':outer_mask(um,vm)})
    return out, vanished


def all_rankone_cols():
    arr=[]
    for u in range(1,1<<8):
        for v in range(1,1<<9):
            arr.append((outer_mask(u,v),u,v))
    return arr


def reconstruct(UV, targets):
    cols=[x[0] for x in UV]
    W=[]
    for tar in targets:
        sol=solve_coeffs(cols,tar)
        if sol is None: return None
        W.append(sol)
    # Return W per term as 9-bit masks.
    wm=[]
    for i in range(len(UV)):
        m=0
        for c,sol in enumerate(W):
            if (sol>>i)&1: m |= 1<<c
        wm.append(m)
    return wm


def verify_cpd(UV, wm, targets):
    recon=[0]*9
    for (col,u,v),w in zip(UV,wm):
        for c in range(9):
            if (w>>c)&1: recon[c] ^= col
    return recon==list(targets)


def save_solution(path, UV, wm, source, targets):
    U=np.zeros((len(UV),8),dtype=np.uint8); V=np.zeros((len(UV),9),dtype=np.uint8); W=np.zeros((len(UV),9),dtype=np.uint8)
    for i,(col,u,v) in enumerate(UV):
        for a in range(8): U[i,a]=(u>>a)&1
        for b in range(9): V[i,b]=(v>>b)&1
        for c in range(9): W[i,c]=(wm[i]>>c)&1
    np.savez(path,U=U,V=V,W=W)
    return {'solution_npz':str(path),'rank':len(UV),'verified':verify_cpd(UV,wm,targets),
            'source':source,'U':U.tolist(),'V':V.tolist(),'W':W.tolist()}


def local_replace_search(seed, pool, targets, seconds, rng, max_trials=10**9):
    state=list(seed); best_state=list(seed)
    best=deficiency([x[0] for x in state],targets)
    cur=best
    start=time.time(); trials=0; accepts=0
    temperature=0.05
    while time.time()-start<seconds and trials<max_trials:
        trials+=1
        pos=rng.randrange(len(state))
        cand=pool[rng.randrange(len(pool))]
        if cand[0] in [x[0] for x in state]:
            continue
        new=list(state); new[pos]=cand
        obj=deficiency([x[0] for x in new],targets)
        oldscore=cur[0]*100+(19-cur[1])*0.01
        newscore=obj[0]*100+(19-obj[1])*0.01
        if obj[0]==0:
            return new,obj,{'trials':trials,'accepts':accepts,'elapsed':time.time()-start,'hit':'local'}
        if newscore<oldscore or rng.random()<temperature**max(0,newscore-oldscore):
            state=new; cur=obj; accepts+=1
            if newscore < best[0]*100+(19-best[1])*0.01:
                best=obj; best_state=list(new)
        if trials%2000==0:
            temperature*=0.995
    return best_state,best,{'trials':trials,'accepts':accepts,'elapsed':time.time()-start,'hit':None}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--core',default='data/restricted_cores/mask_001_E11_core.npy')
    ap.add_argument('--qmm',default='data/cn122_r23_reproduce/scheme.qmm')
    ap.add_argument('--json-out',required=True)
    ap.add_argument('--solution-out',default='data/e11_rank19_candidate.npz')
    ap.add_argument('--seconds',type=float,default=180)
    ap.add_argument('--top-seeds',type=int,default=20)
    ap.add_argument('--seed',type=int,default=95019)
    args=ap.parse_args()
    core=np.load(args.core)
    targets=core_targets(core)
    print('target slice rank',rank_ints(targets),'nnz',sum(t.bit_count() for t in targets))
    rank21,vanished=cn122_core_terms(args.qmm)
    print('cn122 core terms',len(rank21),'vanished',vanished,'def',deficiency([t['uv'] for t in rank21],targets))
    # all 19-subsets of the 21 known terms
    seeds=[]
    for rem in itertools.combinations(range(len(rank21)),2):
        UV=[(t['uv'],t['u'],t['v']) for i,t in enumerate(rank21) if i not in rem]
        obj=deficiency([x[0] for x in UV],targets)
        seeds.append({'removed_surviving_indices':rem,'removed_source_indices':[rank21[i]['source_index'] for i in rem],
                      'deficiency':obj[0],'rankK':obj[1],'rankKS':obj[2],'UV':UV})
    seeds.sort(key=lambda s:(s['deficiency'],-s['rankK']))
    print('best subset seeds:')
    for s in seeds[:10]:
        print({k:s[k] for k in ['removed_source_indices','deficiency','rankK','rankKS']})
        if s['deficiency']==0:
            wm=reconstruct(s['UV'],targets)
            sol=save_solution(Path(args.solution_out),s['UV'],wm,{'type':'subset','seed':{k:s[k] for k in s if k!='UV'}},targets)
            Path(args.json_out).write_text(json.dumps({'status':'found_subset','solution':sol,'best_subsets':[{k:v for k,v in q.items() if k!='UV'} for q in seeds[:20]]},indent=2)+'\n')
            return
    pool=all_rankone_cols()
    print('rank-one pool size',len(pool))
    # Exhaustive one-replacement scan from best seeds.
    one_best=[]; checked=0
    for si,s in enumerate(seeds[:args.top_seeds]):
        UV=s['UV']
        base_cols=[x[0] for x in UV]
        for pos in range(19):
            used=set(base_cols); used.discard(base_cols[pos])
            for cand in pool:
                if cand[0] in used: continue
                new=list(UV); new[pos]=cand
                obj=deficiency([x[0] for x in new],targets); checked+=1
                if len(one_best)<10 or (obj[0],-obj[1]) < (one_best[-1]['deficiency'],-one_best[-1]['rankK']):
                    rec={'seed_rank':si,'replace_pos':pos,'deficiency':obj[0],'rankK':obj[1],'rankKS':obj[2],
                         'removed_source_indices':s['removed_source_indices']}
                    one_best.append(rec); one_best.sort(key=lambda z:(z['deficiency'],-z['rankK'])); one_best=one_best[:10]
                if obj[0]==0:
                    wm=reconstruct(new,targets)
                    sol=save_solution(Path(args.solution_out),new,wm,{'type':'one_replacement','record':rec},targets)
                    Path(args.json_out).write_text(json.dumps({'status':'found_one_replacement','solution':sol,
                        'best_subsets':[{k:v for k,v in q.items() if k!='UV'} for q in seeds[:20]],
                        'one_replacement_checked':checked,'one_replacement_best':one_best},indent=2)+'\n')
                    print('FOUND one replacement',rec)
                    return
        print('finished one-replacement seed',si,'checked',checked,'best',one_best[0])
    rng=random.Random(args.seed)
    best_local={'deficiency':99,'rankK':0}
    best_state=None; local_logs=[]
    per=max(1.0,args.seconds/max(1,args.top_seeds))
    for si,s in enumerate(seeds[:args.top_seeds]):
        state,obj,log=local_replace_search(s['UV'],pool,targets,per,rng)
        rec={'seed_rank':si,'start_removed_source_indices':s['removed_source_indices'],
             'deficiency':obj[0],'rankK':obj[1],'rankKS':obj[2],**log}
        local_logs.append(rec)
        print('local',rec)
        if obj[0]==0:
            wm=reconstruct(state,targets)
            sol=save_solution(Path(args.solution_out),state,{'type':'local_replace','record':rec},targets)
            Path(args.json_out).write_text(json.dumps({'status':'found_local','solution':sol,
                'best_subsets':[{k:v for k,v in q.items() if k!='UV'} for q in seeds[:20]],
                'one_replacement_checked':checked,'one_replacement_best':one_best,'local_logs':local_logs},indent=2)+'\n')
            return
        if (obj[0],-obj[1]) < (best_local['deficiency'],-best_local['rankK']):
            best_local={'deficiency':obj[0],'rankK':obj[1],'rankKS':obj[2],'seed_rank':si}; best_state=state
    out={'status':'not_found','target_slice_rank':rank_ints(targets),'cn122_rank21_deficiency':deficiency([t['uv'] for t in rank21],targets),
         'best_subsets':[{k:v for k,v in q.items() if k!='UV'} for q in seeds[:30]],
         'one_replacement_checked':checked,'one_replacement_best':one_best,
         'local_best':best_local,'local_logs':local_logs,
         'interpretation':'No rank-19 E11 core CPD found by subset, exhaustive single replacement from best cn122 subsets, or the bounded stochastic replacement search. This is not a nonexistence proof.'}
    Path(args.json_out).write_text(json.dumps(out,indent=2)+'\n')
    print('NOT FOUND wrote',args.json_out)

if __name__=='__main__':
    main()
