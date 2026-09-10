#!/usr/bin/env python3
"""analysis: minimize residual-capacity cover conflicts from split-frontier prefixes.

The analysis prefix splitter emitted depth-limit nodes before applying elementary
cardinality, one-row cover, and mixed tests.  This script replays prefixes under
sound cap<=5 Wang saturation, explicitly applies the numerical-order exclusions
from the JSONL line, separates cardinality-only dead nodes from genuine cover
certificates, and then tries to shrink one-row or two-row cover certificates to a
small sufficient set of forced selected points A and explicitly excluded points E.

A minimized record with forced A, excluded E, and row certificate proves the
learned clause
    OR_{p in A} not x_p  OR  OR_{q in E} x_q
for the same row system: no size-19 distinct support extension can satisfy all
points in A selected and all points in E absent.

Saturation removals are derived from A via cap<=5 rows; explicit E is retained
only when the minimizer cannot drop it.  The arithmetic certificate is a one-row
bound u+outside < need or an exact two-row capacity bound on the future domain.
"""
from __future__ import annotations
import argparse, hashlib, json, random, struct, time
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path('research/research_record')
ROWS5 = ROOT/'workspace/data/domain_dfs_soundness/e11_wang_cap5_rebuilt.bin'
DEFAULT_COVER = ROOT/'workspace/data/domain_dfs_soundness/e11_wang_cap67_first512_cover.bin'
DEFAULT_FRONTIER = ROOT/'workspace/data/domain_dfs_soundness/branch1_prefix_d10_frontier.jsonl'
OUT = ROOT/'workspace/data/domain_dfs_soundness/cover_conflict_minimize.json'
WORDS=4; MAXP=255; MAGIC=b'E11WANG1'; REC='<BBHQQQQ'; RECSZ=struct.calcsize(REC)

def sha(path: Path) -> str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda:f.read(1<<20), b''):
            h.update(chunk)
    return h.hexdigest()

def bit(w,p): return (w[p>>6]>>(p&63))&1

def pop(w): return sum(int(x).bit_count() for x in w)

def clr(w,p): w[p>>6] &= ~(1<<(p&63))

def andw(a,b): return [a[i]&b[i] for i in range(WORDS)]

def load_rows(path: Path):
    data=path.read_bytes()
    assert data[:8]==MAGIC, path
    n=struct.unpack_from('<I',data,8)[0]
    rows=[]; off=12
    for i in range(n):
        cap,dim,res,*ws=struct.unpack_from(REC,data,off); off+=RECSZ
        rows.append({'idx':i,'cap':int(cap),'dim':int(dim),'words':[int(x) for x in ws]})
    assert off==len(data)
    return rows

def point_rows(rows):
    pr=[[] for _ in range(256)]
    for i,r in enumerate(rows):
        ww=r['words']
        for p in range(1,256):
            if bit(ww,p): pr[p].append(i)
    return pr

def empty_domain():
    dom=[(1<<64)-1]*4
    dom[0] &= ~1  # remove direction 0
    # remove bits >255 in word 3; harmless for p-loop, but pop() uses them.
    dom[3] &= (1<<64)-1
    return dom

class Replayer:
    def __init__(self, rows5, cover):
        self.rows5=rows5; self.cover=cover
        self.pr5=point_rows(rows5); self.cpr=point_rows(cover)
    def replay(self, forced, excluded):
        """Return status, future domain, row counts, cover counts after forced/excluded."""
        A=sorted(set(int(x) for x in forced))
        E=set(int(x) for x in excluded)
        if len(A)!=len(forced):
            return {'status':'duplicate_forced'}
        if any(q in E for q in A):
            return {'status':'forced_excluded'}
        dom=empty_domain()
        for q in E:
            if 1<=q<=MAXP: clr(dom,q)
        cnt=[0]*len(self.rows5); ccnt=[0]*len(self.cover)
        saturated_rows=[]; sat_removed_total=0
        for q in A:
            if not (1<=q<=MAXP): return {'status':'bad_forced'}
            if not bit(dom,q):
                return {'status':'forced_not_available','failed_point':q,'forced_before':A}
            for ri in self.pr5[q]:
                if cnt[ri]+1>self.rows5[ri]['cap']:
                    return {'status':'cap5_over','failed_point':q,'row':ri,'cap':self.rows5[ri]['cap'],'count':cnt[ri]+1}
            for ri in self.cpr[q]:
                if ccnt[ri]+1>self.cover[ri]['cap']:
                    return {'status':'cover_over','failed_point':q,'row':ri,'cap':self.cover[ri]['cap'],'count':ccnt[ri]+1}
            clr(dom,q)
            touched=[]
            for ri in self.pr5[q]:
                cnt[ri]+=1; touched.append(ri)
            for ri in self.cpr[q]:
                ccnt[ri]+=1
            for ri in touched:
                if cnt[ri]==self.rows5[ri]['cap']:
                    before=pop(dom)
                    rw=self.rows5[ri]['words']
                    for k in range(WORDS): dom[k] &= ~rw[k]
                    after=pop(dom)
                    if before>after:
                        saturated_rows.append(ri)
                        sat_removed_total += before-after
        return {'status':'ok','dom':dom,'cnt5':cnt,'ccnt':ccnt,'saturated_rows':saturated_rows,'sat_removed_total':sat_removed_total}
    def one_row_cert(self, A, E, row_idx):
        rep=self.replay(A,E)
        if rep['status']!='ok': return {'kind':'preconflict','status':rep['status'],'valid':True,'bound':-1}
        need=19-len(set(A)); avail=pop(rep['dom']); r=self.cover[row_idx]
        u=r['cap']-rep['ccnt'][row_idx]
        if u<0: return {'kind':'one','valid':True,'row':row_idx,'cap':r['cap'],'count':rep['ccnt'][row_idx],'residual':u,'future_in':0,'future_out':avail,'bound':-1,'need':need,'margin':-999,'avail':avail}
        rin=pop(andw(rep['dom'],r['words'])); outside=avail-rin; bound=u+outside
        return {'kind':'one','valid':bound<need,'row':row_idx,'cap':r['cap'],'count':rep['ccnt'][row_idx],'residual':u,'future_in':rin,'future_out':outside,'bound':bound,'need':need,'margin':bound-need,'avail':avail,'sat_removed_total':rep['sat_removed_total']}
    def two_row_cert(self, A, E, i, j):
        rep=self.replay(A,E)
        if rep['status']!='ok': return {'kind':'preconflict','status':rep['status'],'valid':True,'bound':-1}
        need=19-len(set(A)); avail=pop(rep['dom'])
        ri,rj=self.cover[i],self.cover[j]
        ui=ri['cap']-rep['ccnt'][i]; uj=rj['cap']-rep['ccnt'][j]
        if ui<0 or uj<0:
            return {'kind':'two','valid':True,'rows':[i,j],'residuals':[ui,uj],'bound':-1,'need':need,'margin':-999,'avail':avail}
        fi=andw(rep['dom'],ri['words']); fj=andw(rep['dom'],rj['words'])
        both=pop([fi[k]&fj[k] for k in range(WORDS)])
        ionly=pop(fi)-both; jonly=pop(fj)-both; outside=avail-(both+ionly+jonly)
        max_inside=0; best_x=0
        for x in range(0, min(both,ui,uj)+1):
            val=x+min(ionly,ui-x)+min(jonly,uj-x)
            if val>max_inside: max_inside=val; best_x=x
        bound=outside+max_inside
        return {'kind':'two','valid':bound<need,'rows':[i,j],'caps':[ri['cap'],rj['cap']], 'counts':[rep['ccnt'][i],rep['ccnt'][j]], 'residuals':[ui,uj], 'both':both,'i_only':ionly,'j_only':jonly,'outside':outside,'max_inside':max_inside,'best_both_take':best_x,'bound':bound,'need':need,'margin':bound-need,'avail':avail,'sat_removed_total':rep['sat_removed_total']}

def best_single_pair(rep, cover, pair_limit):
    dom=rep['dom']; ccnt=rep['ccnt']; need=rep['need']; avail=pop(dom)
    best_s=None
    for i,r in enumerate(cover):
        u=r['cap']-ccnt[i]
        if u>=need: continue
        if u<0:
            rec=(i,r['cap'],ccnt[i],u,0,avail,-999); margin=-999
        else:
            rin=pop(andw(dom,r['words'])); out=avail-rin; margin=u+out-need
            rec=(i,r['cap'],ccnt[i],u,rin,out,margin)
        if best_s is None or margin<best_s[-1]: best_s=rec
    best_p=None; n=min(pair_limit,len(cover))
    fwords=[]; fins=[]; us=[]
    for i in range(n):
        fw=andw(dom,cover[i]['words']); fwords.append(fw); fins.append(pop(fw)); us.append(cover[i]['cap']-ccnt[i])
    for i in range(n):
        for j in range(i+1,n):
            ui,uj=us[i],us[j]
            both=pop([fwords[i][k]&fwords[j][k] for k in range(WORDS)])
            ionly=fins[i]-both; jonly=fins[j]-both; outside=avail-(both+ionly+jonly)
            if ui<0 or uj<0:
                bound=-1; margin=-999; max_inside=0; best_x=0
            else:
                max_inside=0; best_x=0
                for x in range(0,min(both,ui,uj)+1):
                    val=x+min(ionly,ui-x)+min(jonly,uj-x)
                    if val>max_inside: max_inside=val; best_x=x
                bound=outside+max_inside; margin=bound-need
            rec=(i,j,cover[i]['cap'],cover[j]['cap'],ccnt[i],ccnt[j],ui,uj,both,ionly,jonly,outside,bound,margin,max_inside,best_x)
            if best_p is None or margin<best_p[13]: best_p=rec
    return best_s,best_p

def explicit_exclusions(rec):
    if 'exclude_lt_next' in rec:
        return [int(x) for x in rec['exclude_lt_next']]
    force=set(rec['force']); return [p for p in range(1,int(rec['next_min'])) if p not in force]

def minimize_fixed(repl, force, excl, kind, rows, rounds=8, seed=1):
    """Greedy minimize A,E for fixed one- or two-row certificate."""
    rng=random.Random(seed)
    bestA=tuple(sorted(set(force))); bestE=tuple(sorted(set(excl)))
    def cert(A,E):
        if kind=='one': return repl.one_row_cert(A,E,rows[0])
        return repl.two_row_cert(A,E,rows[0],rows[1])
    c0=cert(bestA,bestE)
    if not c0.get('valid'):
        return None
    # Several deletion orders; prefer fewer total literals, then fewer exclusions.
    best=(len(bestA)+len(bestE),len(bestE),bestA,bestE,c0)
    base_items=[('A',x) for x in bestA]+[('E',x) for x in bestE]
    for rr in range(rounds):
        A=set(bestA); E=set(bestE)
        changed=True
        # include a deterministic A-high/E-high bias and randomized passes
        while changed:
            changed=False
            items=[('A',x) for x in sorted(A)]+[('E',x) for x in sorted(E)]
            if rr%3==1: items=[('E',x) for x in sorted(E, reverse=True)]+[('A',x) for x in sorted(A, reverse=True)]
            elif rr%3==2:
                items=[('A',x) for x in A]+[('E',x) for x in E]; rng.shuffle(items)
            for typ,x in list(items):
                if typ=='A' and x in A:
                    A.remove(x); cc=cert(tuple(sorted(A)),tuple(sorted(E)))
                    if cc.get('valid'):
                        changed=True
                    else:
                        A.add(x)
                elif typ=='E' and x in E:
                    E.remove(x); cc=cert(tuple(sorted(A)),tuple(sorted(E)))
                    if cc.get('valid'):
                        changed=True
                    else:
                        E.add(x)
        cc=cert(tuple(sorted(A)),tuple(sorted(E)))
        tup=(len(A)+len(E),len(E),tuple(sorted(A)),tuple(sorted(E)),cc)
        if tup[:2] < best[:2]: best=tup
    return {'A':list(best[2]),'E':list(best[3]),'certificate':best[4], 'literal_count':best[0], 'excluded_count':best[1]}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--frontier',type=Path,default=DEFAULT_FRONTIER)
    ap.add_argument('--cover',type=Path,default=DEFAULT_COVER)
    ap.add_argument('--max-records',type=int,default=5000)
    ap.add_argument('--pair-limit',type=int,default=64)
    ap.add_argument('--minimize-limit',type=int,default=50)
    ap.add_argument('--rounds',type=int,default=8)
    ap.add_argument('--out',type=Path,default=OUT)
    args=ap.parse_args(); t0=time.time()
    rows5=load_rows(ROWS5); cover=load_rows(args.cover); repl=Replayer(rows5,cover)
    stats=Counter(); single_hist=Counter(); pair_hist=Counter(); examples=[]; minimized=[]; rows_used=Counter(); pair_used=Counter()
    total=0
    with args.frontier.open() as f:
        for line in f:
            if total>=args.max_records: break
            rec=json.loads(line); total+=1
            force=[int(x) for x in rec['force']]; excl=explicit_exclusions(rec)
            rep=repl.replay(force,excl)
            if rep['status']!='ok': stats['bad_replay_'+rep['status']]+=1; continue
            need=19-len(set(force)); avail=pop(rep['dom']); rep['need']=need
            if avail != rec.get('avail'):
                stats['avail_mismatch']+=1
            if avail < need:
                stats['cardinality_dead']+=1
                continue
            stats['live_after_cardinality']+=1
            bs,bp=best_single_pair(rep,cover,args.pair_limit)
            sm = None if bs is None else bs[-1]
            pm = None if bp is None else bp[13]
            single_hist['none' if sm is None else ('neg' if sm<0 else str(min(sm,8)))] += 1
            pair_hist['none' if pm is None else ('neg' if pm<0 else str(min(pm,8)))] += 1
            sprune = sm is not None and sm<0
            pprune = pm is not None and pm<0
            if sprune: stats['one_row_cover_dead_live']+=1
            if pprune: stats['pair_cover_dead_live']+=1
            if pprune and not sprune: stats['pair_extra_dead_live']+=1
            if (sprune or pprune) and len(examples)<100:
                examples.append({'idx':total-1,'force':force,'need':need,'avail':avail,'single_best':bs,'pair_best':bp,'single_prune':sprune,'pair_prune':pprune})
            if len(minimized)<args.minimize_limit and (sprune or (pprune and not sprune)):
                if pprune and not sprune:
                    kind='two'; rows=(bp[0],bp[1]); seed=1000+total
                else:
                    kind='one'; rows=(bs[0],); seed=2000+total
                mini=minimize_fixed(repl,force,excl,kind,rows,rounds=args.rounds,seed=seed)
                if mini:
                    rows_used[str(rows[0])] += 1
                    if kind=='two': pair_used[f'{rows[0]},{rows[1]}'] += 1
                    # Also see whether a one-row certificate exists for the minimized A/E.
                    rrep=repl.replay(mini['A'],mini['E'])
                    if rrep['status']=='ok':
                        rrep['need']=19-len(set(mini['A']))
                        s2,p2=best_single_pair(rrep,cover,args.pair_limit)
                    else:
                        s2=p2=None
                    minimized.append({'source_idx':total-1,'source_force_size':len(force),'source_exclude_size':len(excl),'source_need':need,'source_avail':avail,'kind':kind,'rows':list(rows),'minimized':mini,'best_single_after_min':s2,'best_pair_after_min':p2,'learned_clause':' OR '.join([f'not x{p}' for p in mini['A']]+[f'x{q}' for q in mini['E']])})
    # group minimized clauses by literal set and row pair
    groups=defaultdict(list)
    for m in minimized:
        key=(tuple(m['minimized']['A']), tuple(m['minimized']['E']), tuple(m['rows']))
        groups[str(key)].append(m['source_idx'])
    out={'schema':'s0908_cover_conflict_minimize_v1','purpose':'separate cardinality-dead prefixes from live cover certificates and shrink cover contradictions into learned clauses','frontier':str(args.frontier),'rows5':str(ROWS5),'cover':str(args.cover),'hashes':{'rows5_sha256':sha(ROWS5),'cover_sha256':sha(args.cover)},'records_read':total,'pair_limit':args.pair_limit,'stats':dict(stats),'single_margin_hist_live':dict(single_hist),'pair_margin_hist_live':dict(pair_hist),'examples_live_head':examples[:30],'minimized_count':len(minimized),'minimized_head':minimized[:30],'row_use_hist':dict(rows_used),'pair_use_hist':dict(pair_used),'duplicate_minimized_clause_groups':{k:v for k,v in groups.items() if len(v)>1},'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
