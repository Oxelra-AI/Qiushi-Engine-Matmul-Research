#!/usr/bin/env python3
"""Compare W-factor multiplicity and two-deletion deficiency patterns in F2 rank-21 cores."""
from __future__ import annotations
import argparse, itertools, json
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np


def outer_mask(u:int,v:int,nv:int=9)->int:
    x=0
    while u:
        lb=u & -u; a=lb.bit_length()-1; u^=lb
        vv=v
        while vv:
            lbv=vv & -vv; b=lbv.bit_length()-1; vv^=lbv
            x ^= 1<<(a*nv+b)
    return x


def rank_ints(vecs):
    basis={}
    for vv in vecs:
        v=int(vv)
        while v:
            p=v.bit_length()-1
            if p in basis: v ^= basis[p]
            else: basis[p]=v; break
    return len(basis)


def deficiency(cols,targets):
    rk=rank_ints(cols); rks=rank_ints(list(cols)+list(targets)); return rks-rk,rk,rks


def targets_from_core(path):
    T=np.load(path).astype(np.uint8)&1
    m,nv,nw=T.shape
    targets=[]
    for c in range(nw):
        x=0
        for a in range(m):
            for b in range(nv):
                if int(T[a,b,c]): x |= 1<<(a*nv+b)
        targets.append(x)
    return targets


def bits(mask,n=9): return [i for i in range(n) if (int(mask)>>i)&1]


def analyze_one(label,core,pool,rank=21):
    targets=targets_from_core(core)
    arr=np.load(pool)
    out={'label':label,'core':core,'pool':pool,'rows':int(arr.shape[0]),'rank':rank,
         'target_slice_rank':rank_ints(targets),'verified':0,
         'w_mult_profile':Counter(), 'w_repeated_pair_count_profile':Counter(),
         'pair_def_profile':Counter(), 'same_w_pair_def_profile':Counter(), 'diff_w_pair_def_profile':Counter(),
         'def1_same_w':0, 'def1_diff_w':0, 'same_w_def1':0, 'same_w_not_def1':0,
         'repeated_w_masks':Counter(), 'def1_w_masks':Counter(), 'same_w_examples':[], 'diff_w_def1_examples':[]}
    for si,row in enumerate(arr):
        vals=[int(x) for x in row.tolist()]
        terms=[tuple(vals[3*i:3*i+3]) for i in range(rank)]
        uv=[outer_mask(u,v) for u,v,w in terms]
        # verify
        recon=[0]*9
        for (u,v,w),col in zip(terms,uv):
            for c in range(9):
                if (w>>c)&1: recon[c]^=col
        if recon!=targets:
            continue
        out['verified']+=1
        wcnt=Counter(w for u,v,w in terms)
        mults=tuple(sorted(wcnt.values(),reverse=True))
        out['w_mult_profile'][mults]+=1
        repeated_pairs=sum(c*(c-1)//2 for c in wcnt.values())
        out['w_repeated_pair_count_profile'][repeated_pairs]+=1
        for w,c in wcnt.items():
            if c>=2: out['repeated_w_masks'][w]+=c*(c-1)//2
        for i,j in itertools.combinations(range(rank),2):
            obj=deficiency([uv[k] for k in range(rank) if k not in (i,j)], targets)
            out['pair_def_profile'][obj]+=1
            same=(terms[i][2]==terms[j][2])
            if same:
                out['same_w_pair_def_profile'][obj]+=1
                if obj[0]==1:
                    out['same_w_def1']+=1
                    out['def1_same_w']+=1
                    out['def1_w_masks'][terms[i][2]]+=1
                    if len(out['same_w_examples'])<20:
                        out['same_w_examples'].append({'scheme_index':si,'pair':[i,j],'w':terms[i][2],'w_bits':bits(terms[i][2]),'def':obj,
                                                       'deleted_u':[terms[i][0],terms[j][0]],'deleted_v':[terms[i][1],terms[j][1]]})
                else:
                    out['same_w_not_def1']+=1
            else:
                out['diff_w_pair_def_profile'][obj]+=1
                if obj[0]==1:
                    out['def1_diff_w']+=1
                    if len(out['diff_w_def1_examples'])<20:
                        out['diff_w_def1_examples'].append({'scheme_index':si,'pair':[i,j],'w':[terms[i][2],terms[j][2]],'w_bits':[bits(terms[i][2]),bits(terms[j][2])],'def':obj})
    # JSON-friendly conversion
    for key in ['w_mult_profile','w_repeated_pair_count_profile','pair_def_profile','same_w_pair_def_profile','diff_w_pair_def_profile']:
        out[key]={str(k):v for k,v in sorted(out[key].items(), key=lambda kv:str(kv[0]))}
    out['repeated_w_masks']=[{'w':w,'bits':bits(w),'pair_occurrences':c} for w,c in out['repeated_w_masks'].most_common(50)]
    out['def1_w_masks']=[{'w':w,'bits':bits(w),'count':c} for w,c in out['def1_w_masks'].most_common(50)]
    out['interpretation']='def1_same_w/diff_w compare whether near-miss two-deletions come from deleting equal W factors; this is structural evidence for paired-slice channels, not a nonexistence proof.'
    return out


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--json-out',required=True)
    ap.add_argument('items',nargs='+',help='Triples label:core.npy:pool.npy')
    args=ap.parse_args()
    results=[]
    for item in args.items:
        label,core,pool=item.split(':',2)
        results.append(analyze_one(label,core,pool))
    Path(args.json_out).write_text(json.dumps({'results':results},indent=2)+'\n')
    for r in results:
        print('\n===',r['label'],'===')
        print('verified',r['verified'],'w mult profiles top',list(r['w_mult_profile'].items())[:5])
        print('pair_def_profile',r['pair_def_profile'])
        print('same_w profile',r['same_w_pair_def_profile'])
        print('diff_w profile',r['diff_w_pair_def_profile'])
        print('def1_same_w',r['def1_same_w'],'def1_diff_w',r['def1_diff_w'],'same_w_not_def1',r['same_w_not_def1'])
        print('def1_w_masks top',r['def1_w_masks'][:10])
    print('wrote',args.json_out)

if __name__=='__main__': main()
