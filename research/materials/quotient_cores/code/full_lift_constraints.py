#!/usr/bin/env python3
"""analysis: derive full-rank-20 A-lift constraints over quotient supports.

For a rank-20 full tensor decomposition with distinguished A-factor q, quotient
support points p_i in F2^9/<q> lift as s(p_i)+eps_i q.  Every full-tensor Wang
occupation row W gives
  1_{q in W} + sum_i 1_{s(p_i)+eps_i q in W} <= cap20(W).

This script projects those full rows to constraints on the quotient point and the
lift bit eps.  Rows containing q give the usual quotient occupation constraints.
Rows not containing q give extra binary-lift constraints discarded by quotient-only
search.  The output is a census and a small set of strong nontrivial rows for later
SAT/DFS coupling.
"""
from __future__ import annotations
import argparse, json, time, hashlib, sys
from pathlib import Path
from collections import Counter, defaultdict

ROOT=Path('research/research_record')
S04=Path('scripts')
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
OUTDIR=ROOT/'workspace/data/quotient_lift'
PIVOTS={'rank2':17,'rank3':273}

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()

def rref(rows, n=9):
    basis=[0]*n
    for x0 in rows:
        x=int(x0)
        while x:
            p=x.bit_length()-1
            if basis[p]: x ^= basis[p]
            else:
                basis[p]=x; break
    return tuple(b for b in reversed(basis) if b)

def in_span(x,basis):
    y=int(x)
    for b in sorted(basis,key=lambda v:-v.bit_length()):
        if y==0: return True
        hb=b.bit_length()-1
        if (y>>hb)&1: y ^= b
    return y==0

def subspace_points(basis):
    pts=set(); b=list(basis); d=len(b)
    for m in range(1,1<<d):
        x=0
        for i,v in enumerate(b):
            if (m>>i)&1: x ^= v
        pts.add(x)
    return pts

def quotient_project(a,pivot):
    if a==0 or a==pivot: return 0
    h=pivot.bit_length()-1
    if (a>>h)&1: a ^= pivot
    low=a & ((1<<h)-1)
    high=(a>>(h+1))<<h
    return low|high

def lift0(p,pivot):
    h=pivot.bit_length()-1
    low=p & ((1<<h)-1)
    high=(p>>h)<<(h+1)
    return low|high

def classify_full_row(basis,pivot,N=20):
    pts=subspace_points(basis)
    contains_q=pivot in pts
    # For every quotient point, membership of the two lifts.
    pairs=[]; only0=only1=both=neither=0
    for p in range(1,256):
        a0=lift0(p,pivot); a1=a0^pivot
        m0=a0 in pts; m1=a1 in pts
        if m0 and m1:
            both+=1; pairs.append((p,2))
        elif m0:
            only0+=1; pairs.append((p,0))
        elif m1:
            only1+=1; pairs.append((p,1))
        else:
            neither+=1
    return {'contains_q':contains_q,'pairs':pairs,'counts':{'only0':only0,'only1':only1,'both':both,'neither':neither}}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--top',type=int,default=200); args=ap.parse_args()
    OUTDIR.mkdir(parents=True,exist_ok=True)
    t0=time.time(); lut,_=load_lut(LUT)
    out={'schema':'s0908_full_lift_constraints_v1','source_lut':str(LUT),'source_lut_sha256':sha(LUT),'N':20,'pivots':{},'elapsed_sec':None}
    for name,pivot in PIVOTS.items():
        census=Counter(); cap_hist=Counter(); dim_hist=Counter(); patterns=Counter(); strong=[]; quotient_like=0; nontrivial=0; impossible_no_const=[]
        total=0
        for key,lb0 in lut.items():
            key=int(key); lb=int(lb0); cap=20-lb; dim=key&0xF
            if cap<0 or cap>=20: continue
            basis=tuple(unpack_basis(key)); total+=1
            c=classify_full_row(basis,pivot,20); cq=c['contains_q']; rhs=cap-(1 if cq else 0)
            if rhs<0: impossible_no_const.append({'key':key,'cap20':cap,'contains_q':cq})
            cnt=c['counts'];
            if cq:
                # For rows containing q, membership is invariant across lift bit: only both should occur.
                if cnt['only0']==0 and cnt['only1']==0:
                    quotient_like += 1
            else:
                # Extra lift rows not visible as quotient rows unless both>0.
                if cnt['only0'] or cnt['only1'] or cnt['both']:
                    nontrivial += 1
            census[(cq,cnt['only0'],cnt['only1'],cnt['both'],rhs)] += 1
            cap_hist[(cq,rhs)] += 1; dim_hist[(cq,dim)] += 1
            # Score rows that strongly constrain eps choices but are not just quotient masks.
            if (not cq) and rhs>=0 and (cnt['only0']+cnt['only1']+cnt['both']>0):
                # Minimum selected contribution over a quotient support is not known, but small rhs and many conditioned points are useful.
                score=(cnt['only0']+cnt['only1']+2*cnt['both'])-rhs
                if rhs<=5 or score>=20 or cnt['both']>0:
                    strong.append({'key':key,'lb':lb,'cap20':cap,'rhs_after_q':rhs,'dim':dim,'counts':cnt,'score':score})
        strong.sort(key=lambda r:(r['rhs_after_q'],-r['score'],-r['counts']['both'],r['dim'],r['key']))
        out['pivots'][name]={
            'pivot':pivot,
            'total_full_rows_considered':total,
            'quotient_like_rows_containing_q':quotient_like,
            'nontrivial_rows_not_containing_q':nontrivial,
            'cap_rhs_hist_by_contains_q':{str(k):v for k,v in sorted(cap_hist.items(), key=lambda kv:(kv[0][0],kv[0][1]))},
            'dim_hist_by_contains_q':{str(k):v for k,v in sorted(dim_hist.items(), key=lambda kv:(kv[0][0],kv[0][1]))},
            'pattern_count':len(census),
            'pattern_head':[{'contains_q':k[0],'only0':k[1],'only1':k[2],'both':k[3],'rhs_after_q':k[4],'rows':v} for k,v in census.most_common(20)],
            'strong_noncontaining_rows_head':strong[:args.top],
            'strong_noncontaining_rows_selected':min(len(strong),args.top),
            'strong_noncontaining_rows_total_by_filter':len(strong),
            'impossible_after_distinguished_q_head':impossible_no_const[:20],
        }
    out['elapsed_sec']=time.time()-t0
    path=OUTDIR/'full_lift_constraints_census.json'; path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({name:{'pivot':v['pivot'],'total':v['total_full_rows_considered'],'quotient_like':v['quotient_like_rows_containing_q'],'noncontaining':v['nontrivial_rows_not_containing_q'],'patterns':v['pattern_count'],'strong_total':v['strong_noncontaining_rows_total_by_filter']} for name,v in out['pivots'].items()},indent=2,sort_keys=True)); print('saved',path)
if __name__=='__main__': main()
