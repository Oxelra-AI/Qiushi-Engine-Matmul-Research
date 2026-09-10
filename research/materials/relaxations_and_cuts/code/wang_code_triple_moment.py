#!/usr/bin/env python3
"""Third-moment code relaxation for the Wang T-level s=20 problem.

This strengthens wang_code_lp.py by adding unordered triple category variables.
A real 20-point A-support induces:
  * split codeword counts A_{matrix-rank, Hamming-weight};
  * column-rank counts n_q;
  * pair-category counts P_c;
  * triple-category counts Q_d.
The constraints tie first, second and third Hamming moments for messages of each
matrix rank, plus ordinary MacWilliams identities for the [20,9] binary code.

If this relaxation is infeasible, it is a compact code-theoretic proof target for
R_F2(T)>20.  If feasible, it quantifies the remaining slack beyond ordinary
MacWilliams and low moments.
"""
from __future__ import annotations
import argparse, json, math, time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Tuple

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import lil_matrix

N=20; K=9; CODE_SIZE=1<<K
POINTS=list(range(1,1<<9))
RANK_COUNTS={1:49,2:294,3:168}
MIN_WEIGHT={1:3,2:6,3:9}


def mat_rank(mask:int)->int:
    rows=[(mask>>(3*i))&7 for i in range(3)]
    rows=[r for r in rows if r]
    rank=0; bit=4
    while bit:
        piv=None
        for i in range(rank,len(rows)):
            if rows[i]&bit: piv=i; break
        if piv is not None:
            rows[rank],rows[piv]=rows[piv],rows[rank]
            for j in range(len(rows)):
                if j!=rank and (rows[j]&bit): rows[j]^=rows[rank]
            rank+=1
        bit >>= 1
    return rank

def dot(a:int,b:int)->int: return (a&b).bit_count()&1

def kraw(j:int,w:int,n:int=N)->int:
    s=0
    for i in range(j+1):
        if i<=w and j-i<=n-w:
            s += ((-1)**i)*math.comb(w,i)*math.comb(n-w,j-i)
    return s


def hit_bitsets():
    msgs_by_rank={r:[m for m in POINTS if mat_rank(m)==r] for r in (1,2,3)}
    rank_mask={}
    msg_index={}
    idx=0
    for r in (1,2,3):
        b=0
        for m in msgs_by_rank[r]:
            msg_index[m]=idx; b |= 1<<idx; idx+=1
        rank_mask[r]=b
    hb={}
    for p in POINTS:
        b=0
        for m,i in msg_index.items():
            if dot(m,p): b |= 1<<i
        hb[p]=b
    return hb, rank_mask


def incidence_counts(hb, rank_mask):
    ranks={p:mat_rank(p) for p in POINTS}
    reps={r:next(p for p in POINTS if ranks[p]==r) for r in (1,2,3)}
    inc={}
    for mr in (1,2,3):
        for cr in (1,2,3):
            inc[(mr,cr)]=(hb[reps[cr]] & rank_mask[mr]).bit_count()
    return inc


def pair_key(a:int,b:int,hb,rank_mask,ranks):
    ra,rb=ranks[a],ranks[b]
    hit2=tuple(((hb[a]&hb[b]&rank_mask[mr]).bit_count()) for mr in (1,2,3))
    return (min(ra,rb),max(ra,rb),ranks[a^b],hit2)


def build_pair_categories(hb,rank_mask,ranks):
    cats={}; pair_to_cat={}
    for ii,a in enumerate(POINTS):
        for b in POINTS[ii+1:]:
            key=pair_key(a,b,hb,rank_mask,ranks)
            if key not in cats:
                ra,rb=ranks[a],ranks[b]
                ep={1:0,2:0,3:0}; ep[ra]+=1; ep[rb]+=1
                cats[key]={'key':key,'endpoint_mult':ep,'rank_sum':ranks[a^b],'hit2':{1:key[3][0],2:key[3][1],3:key[3][2]},'available_pairs':0,'example':[a,b]}
            cats[key]['available_pairs']+=1
            pair_to_cat[(a,b)]=key
    ordered=sorted(cats.values(), key=lambda c:c['key'])
    key_to_idx={c['key']:i for i,c in enumerate(ordered)}
    pair_idx={ab:key_to_idx[k] for ab,k in pair_to_cat.items()}
    return ordered, pair_idx


def build_triple_categories(hb,rank_mask,ranks,pair_idx, pair_cats, progress=False):
    t0=time.time(); cats={}; total=0
    for ia,a in enumerate(POINTS[:-2]):
        if progress and ia%50==0:
            print(f'triples progress a-index {ia}/{len(POINTS)} cats={len(cats)} total={total:,} elapsed={time.time()-t0:.1f}s', flush=True)
        hba=hb[a]
        for jb in range(ia+1,len(POINTS)-1):
            b=POINTS[jb]; hab=hba & hb[b]
            pab=pair_idx[(a,b)]
            for kidx in range(jb+1,len(POINTS)):
                c=POINTS[kidx]
                bits=hab & hb[c]
                hit3=(bits & rank_mask[1]).bit_count(), (bits & rank_mask[2]).bit_count(), (bits & rank_mask[3]).bit_count()
                pr=tuple(sorted((pab, pair_idx[(a,c)], pair_idx[(b,c)])))
                rc=[0,0,0]
                rc[ranks[a]-1]+=1; rc[ranks[b]-1]+=1; rc[ranks[c]-1]+=1
                key=(tuple(rc), pr, hit3)
                if key not in cats:
                    cats[key]={'key':key,'endpoint_mult':{1:rc[0],2:rc[1],3:rc[2]},'pair_cat_mult':dict(Counter(pr)),'hit3':{1:hit3[0],2:hit3[1],3:hit3[2]},'available_triples':0,'example':[a,b,c]}
                cats[key]['available_triples']+=1; total+=1
    ordered=sorted(cats.values(), key=lambda c:c['key'])
    return ordered, {'category_count':len(ordered),'total_triples':total,'elapsed_sec':time.time()-t0}


class VI:
    def __init__(self): self.names=[]; self.lb=[]; self.ub=[]; self.intg=[]; self.A={}; self.n={}; self.P={}; self.Q={}; self.B={}
    def add(self,name,lb=0,ub=math.inf,integer=False):
        i=len(self.names); self.names.append(name); self.lb.append(lb); self.ub.append(ub); self.intg.append(1 if integer else 0); return i


def build(integer=False, progress=False):
    hb,rm=hit_bitsets(); ranks={p:mat_rank(p) for p in POINTS}; inc=incidence_counts(hb,rm)
    tcat0=time.time(); pair_cats,pair_idx=build_pair_categories(hb,rm,ranks)
    triple_cats,triple_meta=build_triple_categories(hb,rm,ranks,pair_idx,pair_cats,progress=progress)
    vi=VI()
    for r in (1,2,3):
        for w in range(MIN_WEIGHT[r],N+1): vi.A[(r,w)]=vi.add(f'A_r{r}_w{w}',0,RANK_COUNTS[r],integer)
    for q in (1,2,3): vi.n[q]=vi.add(f'n_col_rank{q}',0,RANK_COUNTS[q],integer)
    for i,c in enumerate(pair_cats): vi.P[i]=vi.add(f'P{i}',0,c['available_pairs'],integer)
    for i,c in enumerate(triple_cats): vi.Q[i]=vi.add(f'Q{i}',0,c['available_triples'],integer)
    for j in range(N+1): vi.B[j]=vi.add(f'B{j}',0,1<<(N-K),integer)
    rows=[]; rhs=[]
    def row(): return defaultdict(float)
    def eq(r,b): rows.append(r); rhs.append(b)
    # rank message counts
    for r in (1,2,3):
        rr=row();
        for w in range(MIN_WEIGHT[r],N+1): rr[vi.A[(r,w)]]=1
        eq(rr,RANK_COUNTS[r])
    # columns
    rr=row();
    for q in (1,2,3): rr[vi.n[q]]=1
    eq(rr,N)
    for mr in (1,2,3):
        rr=row();
        for w in range(MIN_WEIGHT[mr],N+1): rr[vi.A[(mr,w)]] += w
        for cr in (1,2,3): rr[vi.n[cr]] -= inc[(mr,cr)]
        eq(rr,0)
    # pairs total and endpoint consistency
    rr=row();
    for i in vi.P: rr[vi.P[i]]=1
    eq(rr,math.comb(N,2))
    for q in (1,2,3):
        rr=row();
        for i,c in enumerate(pair_cats): rr[vi.P[i]] += c['endpoint_mult'][q]
        rr[vi.n[q]] -= (N-1)
        eq(rr,0)
    for mr in (1,2,3):
        rr=row();
        for w in range(MIN_WEIGHT[mr],N+1): rr[vi.A[(mr,w)]] += w*(w-1)
        for i,c in enumerate(pair_cats): rr[vi.P[i]] -= 2*c['hit2'][mr]
        eq(rr,0)
    # triples total, endpoint consistency, pair consistency, third moments
    rr=row();
    for i in vi.Q: rr[vi.Q[i]]=1
    eq(rr,math.comb(N,3))
    for q in (1,2,3):
        rr=row()
        for i,c in enumerate(triple_cats): rr[vi.Q[i]] += c['endpoint_mult'][q]
        rr[vi.n[q]] -= math.comb(N-1,2)
        eq(rr,0)
    for pc_i in range(len(pair_cats)):
        rr=row()
        for qi,c in enumerate(triple_cats): rr[vi.Q[qi]] += c['pair_cat_mult'].get(pc_i,0)
        rr[vi.P[pc_i]] -= (N-2)
        eq(rr,0)
    for mr in (1,2,3):
        rr=row()
        for w in range(MIN_WEIGHT[mr],N+1): rr[vi.A[(mr,w)]] += w*(w-1)*(w-2)
        for i,c in enumerate(triple_cats): rr[vi.Q[i]] -= 6*c['hit3'][mr]
        eq(rr,0)
    # MacWilliams exact dual enumerator.
    for j in range(N+1):
        rr=row()
        for (r,w),idx in vi.A.items(): rr[idx] += kraw(j,w)
        rr[vi.B[j]] -= CODE_SIZE
        eq(rr,-kraw(j,0))
    for j,val in [(0,1),(1,0),(2,0)]:
        rr=row(); rr[vi.B[j]]=1; eq(rr,val)
    M=lil_matrix((len(rows),len(vi.names)),dtype=float)
    for i,rw in enumerate(rows):
        for j,v in rw.items():
            if v: M[i,j]=v
    meta={'num_vars':len(vi.names),'num_equalities':len(rhs),'pair_category_count':len(pair_cats),'triple_meta':triple_meta,'incidence_counts':{f'msg{m}_col{c}':inc[(m,c)] for m in (1,2,3) for c in (1,2,3)},'build_elapsed_sec':time.time()-tcat0}
    return vi,M.tocsr(),np.array(rhs,dtype=float),meta,pair_cats,triple_cats


def solve(integer=False,time_limit=None,progress=False):
    vi,Aeq,beq,meta,pair_cats,triple_cats=build(integer=integer,progress=progress)
    c=np.zeros(len(vi.names)); bounds=Bounds(np.array(vi.lb,float),np.array(vi.ub,float)); t0=time.time()
    if integer:
        opts={'disp':True,'mip_rel_gap':0.0}
        if time_limit is not None: opts['time_limit']=time_limit
        res=milp(c=c,integrality=np.array(vi.intg),bounds=bounds,constraints=[LinearConstraint(Aeq,beq,beq)],options=opts)
        x=None if res.x is None else np.array(res.x); msg=str(res.message); success=bool(res.success); status=int(res.status)
    else:
        opts={'presolve':True}
        if time_limit is not None: opts['time_limit']=time_limit
        res=linprog(c,A_eq=Aeq,b_eq=beq,bounds=list(zip(vi.lb,vi.ub)),method='highs',options=opts)
        x=None if res.x is None else np.array(res.x); msg=str(res.message); success=bool(res.success); status=int(res.status)
    out={'problem':'[20,9] rank-split third-moment relaxation for Wang T-level s=20','integer':integer,'meta':meta,'solver_status':status,'solver_message':msg,'success':success,'solve_elapsed_sec':time.time()-t0}
    if x is not None:
        Awt={0:1.0}; split={}
        for (r,w),idx in vi.A.items():
            val=float(x[idx]);
            if abs(val)>1e-7: split.setdefault(r,{})[w]=val; Awt[w]=Awt.get(w,0)+val
        B={}
        for j in range(N+1):
            val=kraw(j,0)+sum(float(x[idx])*kraw(j,w) for (r,w),idx in vi.A.items())
            if abs(val)>1e-7: B[j]=val/CODE_SIZE
        out['split_weight_enumerator']={str(r):{str(w):v for w,v in ww.items()} for r,ww in split.items()}
        out['A_weight_enumerator']={str(w):v for w,v in sorted(Awt.items()) if abs(v)>1e-7}
        out['dual_weight_enumerator_from_A']={str(j):v for j,v in sorted(B.items())}
        out['column_rank_counts']={str(q):float(x[idx]) for q,idx in vi.n.items()}
        out['nonzero_pair_category_count']=sum(1 for idx in vi.P.values() if abs(x[idx])>1e-7)
        out['nonzero_triple_category_count']=sum(1 for idx in vi.Q.values() if abs(x[idx])>1e-7)
    return out


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--integer',action='store_true'); ap.add_argument('--time-limit',type=float,default=None); ap.add_argument('--progress',action='store_true'); ap.add_argument('--out',type=Path,required=True); args=ap.parse_args()
    res=solve(integer=args.integer,time_limit=args.time_limit,progress=args.progress)
    print(json.dumps({k:res[k] for k in ['problem','integer','meta','solver_status','solver_message','success','solve_elapsed_sec']},indent=2,sort_keys=True))
    if 'column_rank_counts' in res: print('column_rank_counts',res['column_rank_counts']); print('A weights',res.get('A_weight_enumerator')); print('dual B',res.get('dual_weight_enumerator_from_A'))
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(res,indent=2,sort_keys=True)+'\n'); print('saved',args.out)
if __name__=='__main__': main()
