#!/usr/bin/env python3
"""Analyze one-row and two-row residual-capacity cover power on saved split frontiers.

For each JSONL prefix emitted by cover_exhaust_prefix, replay the cap<=5
Wang saturation from its forced points to reconstruct the actual future domain F.
Then compute:
  single margin min_R (cap-|P∩R|)+|F\R|-need;
  pair margin min_{R,S} exact maximum extension size under two row capacities minus need.
Negative margin gives a short checkable closure certificate for that prefix.
"""
from __future__ import annotations
import argparse, json, struct, time
from collections import Counter
from pathlib import Path
ROOT=Path('research/research_record')
ROWS5=ROOT/'workspace/data/domain_dfs_soundness/e11_wang_cap5_rebuilt.bin'
DEFAULT_COVER=ROOT/'workspace/data/domain_dfs_soundness/e11_wang_cap67_first512_cover.bin'
OUT=ROOT/'workspace/data/domain_dfs_soundness/pair_cover_frontier_analysis.json'
WORDS=4; MAXP=255; MAGIC=b'E11WANG1'; REC='<BBHQQQQ'; RECSZ=struct.calcsize(REC)

def bit(w,p): return (w[p>>6]>>(p&63))&1
def pop(w): return sum(int(x).bit_count() for x in w)
def clr(w,p): w[p>>6] &= ~(1<<(p&63))
def andw(a,b): return [a[i]&b[i] for i in range(WORDS)]
def andnot(a,b): return [a[i]&~b[i] for i in range(WORDS)]
def xor_unused(): pass

def load_rows(path):
    data=Path(path).read_bytes(); assert data[:8]==MAGIC, path; n=struct.unpack_from('<I',data,8)[0]; off=12; rows=[]
    for i in range(n):
        cap,dim,res,*ws=struct.unpack_from(REC,data,off); off+=RECSZ
        rows.append({'cap':cap,'dim':dim,'words':ws,'idx':i})
    return rows

def point_rows(rows):
    pr=[[] for _ in range(256)]
    for i,r in enumerate(rows):
        for p in range(1,256):
            if bit(r['words'],p): pr[p].append(i)
    return pr

def replay_domain(force,rows5,pr5):
    dom=[(1<<64)-1]*4; dom[0]&=~1; cnt=[0]*len(rows5)
    for q in force:
        if not bit(dom,q):
            return None,None,'not_in_domain'
        for ri in pr5[q]:
            if cnt[ri]+1>rows5[ri]['cap']:
                return None,None,'over_cap'
        clr(dom,q)
        touched=[]
        for ri in pr5[q]:
            cnt[ri]+=1; touched.append(ri)
        for ri in touched:
            if cnt[ri]==rows5[ri]['cap']:
                rw=rows5[ri]['words']
                for k in range(WORDS): dom[k] &= ~rw[k]
    return dom,cnt,'ok'

def cover_counts(force,cpr,n):
    cnt=[0]*n
    for q in force:
        for ri in cpr[q]: cnt[ri]+=1
    return cnt

def future(dom,minp):
    fut=dom.copy()
    for p in range(1,minp): clr(fut,p)
    return fut

def single_best(fut,avail,need,cover,ccnt):
    best=10**9; besti=-1; bestrec=None
    for i,r in enumerate(cover):
        u=r['cap']-ccnt[i]
        if u>=need: continue
        rin=pop(andw(fut,r['words'])); out=avail-rin; margin=u+out-need
        if margin<best:
            best=margin; besti=i; bestrec=(i,r['cap'],ccnt[i],u,rin,out,margin)
    return best,besti,bestrec

def pair_best(fut,avail,need,cover,ccnt,limit):
    best=10**9; bestpair=None; n=min(limit,len(cover))
    # cache future intersections and residuals
    fwords=[]; fins=[]; us=[]
    for i in range(n):
        fw=andw(fut,cover[i]['words']); fwords.append(fw); fins.append(pop(fw)); us.append(cover[i]['cap']-ccnt[i])
    for i in range(n):
        ui=us[i]
        for j in range(i+1,n):
            uj=us[j]
            # If both residual capacities alone exceed need, pair rarely helps but can still with almost all future in union; keep exact.
            both=pop([fwords[i][k]&fwords[j][k] for k in range(WORDS)])
            bi=fins[i]-both; cj=fins[j]-both; outside=avail-(both+bi+cj)
            max_inside=0; upper=min(both,ui,uj)
            # small loop: capacities <= 10 here
            for x in range(max(0, upper+1)):
                val=x+min(bi,ui-x)+min(cj,uj-x)
                if val>max_inside: max_inside=val
            bound=outside+max_inside; margin=bound-need
            if margin<best:
                best=margin; bestpair=(i,j,cover[i]['cap'],cover[j]['cap'],ccnt[i],ccnt[j],ui,uj,both,bi,cj,outside,bound,margin)
    return best,bestpair

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--frontier',type=Path,required=True); ap.add_argument('--cover',type=Path,default=DEFAULT_COVER); ap.add_argument('--max-records',type=int,default=5000); ap.add_argument('--pair-limit',type=int,default=128); ap.add_argument('--out',type=Path,default=OUT)
    args=ap.parse_args(); t0=time.time(); rows5=load_rows(ROWS5); pr5=point_rows(rows5); cover=load_rows(args.cover); cpr=point_rows(cover)
    total=0; bad=Counter(); single_hist=Counter(); pair_hist=Counter(); single_prunes=0; pair_extra=0; avail_mismatch=0; examples=[]
    with args.frontier.open() as f:
        for line in f:
            if total>=args.max_records: break
            rec=json.loads(line); total+=1
            force=rec['force']; need=rec['need']; minp=rec['next_min']
            dom,_,status=replay_domain(force,rows5,pr5)
            if status!='ok': bad[status]+=1; continue
            fut=future(dom,minp); avail=pop(fut)
            if avail!=rec.get('avail'): avail_mismatch+=1
            ccnt=cover_counts(force,cpr,len(cover))
            sb,si,srec=single_best(fut,avail,need,cover,ccnt)
            pb,prec=pair_best(fut,avail,need,cover,ccnt,args.pair_limit)
            single_hist['none' if sb==10**9 else ('neg' if sb<0 else str(min(sb,8)))] += 1
            pair_hist['none' if pb==10**9 else ('neg' if pb<0 else str(min(pb,8)))] += 1
            sprune=sb<0; pprune=pb<0
            single_prunes += int(sprune); pair_extra += int((not sprune) and pprune)
            if len(examples)<20 and ((not sprune and pprune) or (sb>=0 and sb<=1) or (pb<sb)):
                examples.append({'idx':total-1,'force':force,'need':need,'minp':minp,'avail':avail,'single_best':srec,'pair_best':prec,'single_prune':sprune,'pair_prune':pprune})
    out={'schema':'s0908_pair_cover_frontier_analysis_v1','frontier':str(args.frontier),'cover':str(args.cover),'rows5':str(ROWS5),'records_read':total,'pair_limit':args.pair_limit,'bad_replay':dict(bad),'avail_mismatch':avail_mismatch,'single_prunes':single_prunes,'pair_extra_prunes_over_single':pair_extra,'single_margin_hist':dict(single_hist),'pair_margin_hist':dict(pair_hist),'examples_head':examples,'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
