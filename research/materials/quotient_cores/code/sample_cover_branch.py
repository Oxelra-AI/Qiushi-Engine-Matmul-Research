#!/usr/bin/env python3
"""analysis: sample partial nodes in unresolved E11 branches and evaluate one-row residual-capacity certificates.

The goal is not to enumerate supports, but to measure whether larger omitted Wang
rows (cap 6,7,8,10,13,16) can close realistic partial states by the sound bound
u_R + |F\R| < t.  The sampler mimics the repaired Wang saturation semantics for
cap<=5 rows, branches by orbit representative, and greedily chooses random valid
partial supports to requested depths.
"""
from __future__ import annotations
import argparse, json, random, struct, time
from collections import Counter, defaultdict
from pathlib import Path
ROOT=Path('research/research_record')
ROWS5=ROOT/'workspace/data/domain_dfs_soundness/e11_wang_cap5_rebuilt.bin'
ROWS16=ROOT/'workspace/data/domain_dfs_soundness/e11_wang_cap16_rebuilt.bin'
OUT=ROOT/'workspace/data/domain_dfs_soundness/sample_cover_branch.json'
WORDS=4; MAXP=255
REPS=[1,4,5,8,10,40,42,80]
MEMBERS=[
    [1,2,3], [4,32,36], [5,6,7,33,34,35,37,38,39],
    [8,9,12,13,16,18,20,22,24,27,28,31,64,65,72,73,96,97,108,109,128,130,144,146,160,162,180,182,192,195,216,219,224,227,252,255],
    [10,11,14,15,17,19,21,23,25,26,29,30,66,67,74,75,98,99,110,111,129,131,145,147,161,163,181,183,193,194,217,218,225,226,253,254],
    [40,41,44,45,48,50,52,54,56,59,60,63,68,69,76,77,100,101,104,105,132,134,148,150,164,166,176,178,196,199,220,223,228,231,248,251],
    [42,43,46,47,49,51,53,55,57,58,61,62,70,71,78,79,102,103,106,107,133,135,149,151,165,167,177,179,197,198,221,222,229,230,249,250],
    [80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,136,137,138,139,140,141,142,143,152,153,154,155,156,157,158,159,168,169,170,171,172,173,174,175,184,185,186,187,188,189,190,191,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247]
]

def bit(words,p): return (words[p>>6]>>(p&63))&1

def pop_words(words): return sum(int(w).bit_count() for w in words)

def mask_from_pts(pts):
    w=[0,0,0,0]
    for p in pts: w[p>>6] |= 1<<(p&63)
    return w

def and_words(a,b): return [a[i]&b[i] for i in range(WORDS)]
def andnot_words(a,b): return [a[i]&~b[i] for i in range(WORDS)]
def clear_word_bit(w,p): w[p>>6] &= ~(1<<(p&63))
def set_word_bit(w,p): w[p>>6] |= 1<<(p&63)

def load_rows(path):
    data=path.read_bytes(); assert data[:8]==b'E11WANG1'; n=struct.unpack_from('<I',data,8)[0]; off=12; rows=[]
    for i in range(n):
        cap,dim,res,*ws=struct.unpack_from('<BBHQQQQ',data,off); off+=36
        rows.append({'cap':cap,'dim':dim,'words':ws,'idx':i,'size':pop_words(ws)})
    return rows

def point_rows(rows):
    pr=[[] for _ in range(256)]
    for i,r in enumerate(rows):
        for p in range(1,256):
            if bit(r['words'],p): pr[p].append(i)
    return pr

def branch_initial(branch):
    dom=[(1<<64)-1]*4; dom[0] &= ~1
    forbid=[]
    for i in range(branch): forbid += MEMBERS[i]
    rep=REPS[branch]
    for p in forbid: clear_word_bit(dom,p)
    return dom,rep

def run_sample(branch,depth,rows5,pr5,cover_rows,cpr,seed,tries):
    rng=random.Random(seed); records=[]; fail_counter=Counter(); cap_success=Counter(); cap_near=Counter(); best_margins=[]; completed=0
    for tr in range(tries):
        dom,rep=branch_initial(branch); cnt=[0]*len(rows5); ccnt=[0]*len(cover_rows); chosen=[]
        def select(q):
            if not bit(dom,q): return False
            for ri in pr5[q]:
                if cnt[ri]+1>rows5[ri]['cap']: return False
            clear_word_bit(dom,q); chosen.append(q)
            touched=[]
            for ri in pr5[q]: cnt[ri]+=1; touched.append(ri)
            for ri in cpr[q]: ccnt[ri]+=1
            # saturation propagation; no backtracking inside one sample path
            for ri in touched:
                if cnt[ri]==rows5[ri]['cap']:
                    rw=rows5[ri]['words']
                    for wi in range(WORDS): dom[wi] &= ~rw[wi]
            return True
        if not select(rep):
            fail_counter['rep_failed']+=1; continue
        minp=rep+1
        ok=True
        while len(chosen)<depth:
            need=depth-len(chosen)
            cand=[p for p in range(minp,256) if bit(dom,p)]
            if len(cand)<need: ok=False; fail_counter[f'short_before_depth_{len(chosen)}']+=1; break
            # Prefer points that keep future domain small, but add randomness.
            scored=[]
            sample=cand if len(cand)<=80 else rng.sample(cand,80)
            for p in sample:
                # cheap score: number of saturated rows it would touch if selected
                sat=sum(1 for ri in pr5[p] if cnt[ri]+1==rows5[ri]['cap'])
                scored.append((sat+rng.random()*0.25,p))
            scored.sort(reverse=True)
            q=scored[0][1]
            if not select(q):
                # very rare because candidate checked only by current caps; try alternatives
                alternatives=[p for _,p in scored[1:]]
                done=False
                for p in alternatives:
                    if select(p): q=p; done=True; break
                if not done: ok=False; fail_counter['select_failed']+=1; break
            minp=q+1
        if not ok: continue
        completed+=1
        # Future domain respects increasing-order minp.
        fut=dom.copy()
        for p in range(1,minp): clear_word_bit(fut,p)
        avail=pop_words(fut); need=19-len(chosen)
        best_margin=10**9; best=None; pruned=False; tested=0; close_rows=[]
        for j,r in enumerate(cover_rows):
            u=r['cap']-ccnt[j]
            if u>=need: continue
            tested+=1
            rin=pop_words(and_words(fut,r['words'])); outside=avail-rin; bound=u+outside; margin=bound-need
            if margin<best_margin:
                best_margin=margin; best=(j,r['cap'],r['dim'],r['size'],count,u,rin,outside,bound,margin)
            if margin<0:
                pruned=True; cap_success[r['cap']]+=1
                if len(close_rows)<3: close_rows.append(best)
                break
            elif margin<=2:
                cap_near[(r['cap'],margin)] += 1
        best_margins.append(best_margin if best is not None else None)
        if len(records)<20 and (pruned or (best is not None and best[-1]<=2)):
            records.append({'trial':tr,'branch':branch,'chosen':chosen,'minp':minp,'depth':len(chosen),'need':need,'avail':avail,'tested_rows':tested,'pruned':pruned,'best':best,'close_rows':close_rows})
    hist=Counter(('none' if m is None else ('neg' if m<0 else str(min(m,10)))) for m in best_margins)
    return {'branch':branch,'target_sample_depth':depth,'tries':tries,'completed_samples':completed,'fail_counter':dict(fail_counter),'best_margin_hist_clipped':dict(hist),'cap_success':{str(k):int(v) for k,v in sorted(cap_success.items())},'cap_near':{str(k):int(v) for k,v in cap_near.items()},'records_head':records}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--tries',type=int,default=500); ap.add_argument('--depths',default='10,12,14,16'); ap.add_argument('--branches',default='0,1,2,3'); ap.add_argument('--seed',type=int,default=1502); ap.add_argument('--out',type=Path,default=OUT)
    args=ap.parse_args(); t0=time.time(); rows5=load_rows(ROWS5); rows16=load_rows(ROWS16); pr5=point_rows(rows5)
    cover=[r for r in rows16 if r['cap']>5 and r['cap']<19]
    cpr=point_rows(cover)
    summaries=[]
    for b in [int(x) for x in args.branches.split(',') if x!='']:
        for d in [int(x) for x in args.depths.split(',') if x!='']:
            summaries.append(run_sample(b,d,rows5,pr5,cover,cpr,args.seed+100*b+d,args.tries))
    out={'schema':'s0908_sample_cover_branch_v1','semantics':'Random greedy partial nodes under cap<=5 saturation; evaluates omitted larger Wang rows by u+|F\\R|<need.','rows5':str(ROWS5),'rows16':str(ROWS16),'cover_rows_count':len(cover),'tries_per_branch_depth':args.tries,'summaries':summaries,'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
