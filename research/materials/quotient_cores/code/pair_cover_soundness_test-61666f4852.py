#!/usr/bin/env python3
"""Small brute-force tests for pair_cover_dfs.

The combined runner mixes saturation, signed-pair propagation, mandatory points,
and residual-cover pruning.  This review checks it on artificial small domains
against direct enumeration of all supports satisfying ordinary rows, pair
inequalities, and cover rows.
"""
from __future__ import annotations
import json, random, struct, subprocess, tempfile
from itertools import combinations
from pathlib import Path

ROOT=Path('research/research_record')
BIN=ROOT/'workspace/scripts/pair_cover_dfs'
OUT=ROOT/'workspace/data/domain_dfs_soundness/pair_cover_soundness_test.json'
MAGIC=b'E11WANG1'

def mask_words(points):
    w=[0,0,0,0]
    for p in points:
        w[p>>6] |= 1<<(p&63)
    return w

def write_rows(path, rows):
    with path.open('wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I',len(rows)))
        for cap,pts in rows:
            f.write(struct.pack('<BBHQQQQ', int(cap),0,0,*mask_words(pts)))

def eval_support(supp,constraints,pair_rows,cover_rows,target):
    S=set(supp)
    for cap,pts in list(constraints)+list(cover_rows):
        if len(S & set(pts)) > cap:
            return False
    for i,(ci,Ri) in enumerate(pair_rows):
        Ri=set(Ri)
        for cj,Rj in pair_rows[i+1:]:
            thr=target-ci-cj
            if thr<=0: continue
            Rj=set(Rj); I=Ri&Rj; O=set(range(1,256))-(Ri|Rj)
            if len(S&O)-len(S&I) < thr:
                return False
    return True

def brute(domain,force,constraints,pair_rows,cover_rows,target):
    force=tuple(sorted(force)); fset=set(force); avail=[p for p in domain if p not in fset]
    if len(force)>target: return []
    sol=[]
    for comb in combinations(avail,target-len(force)):
        s=tuple(sorted(force+comb))
        if eval_support(s,constraints,pair_rows,cover_rows,target):
            sol.append(s)
    return sol

def run_case(td,name,domain,force,constraints,pair_rows,cover_rows,target=4,timeout=8,cover_min_depth=0):
    cp=td/f'{name}_cons.bin'; pp=td/f'{name}_pair.bin'; vp=td/f'{name}_cover.bin'; op=td/f'{name}_out.json'
    write_rows(cp,constraints); write_rows(pp,pair_rows); write_rows(vp,cover_rows)
    exclude=[p for p in range(1,256) if p not in set(domain)]
    cmd=[str(BIN),'--constraints',str(cp),'--pair-rows',str(pp),'--cover-constraints',str(vp),'--target',str(target),'--timeout',str(timeout),'--cover-min-depth',str(cover_min_depth),'--output',str(op)]
    if force: cmd += ['--force', ','.join(map(str,sorted(force)))]
    if exclude: cmd += ['--exclude', ','.join(map(str,exclude))]
    proc=subprocess.run(cmd,text=True,capture_output=True,timeout=timeout+5)
    if proc.returncode!=0:
        raise RuntimeError(f'runner failed {proc.returncode}\nSTDOUT={proc.stdout}\nSTDERR={proc.stderr}')
    data=json.loads(op.read_text()); return data['result'],proc.stdout,proc.stderr

def main():
    random.seed(27027); cases=[]; mismatches=[]
    with tempfile.TemporaryDirectory(dir=ROOT/'workspace/data/domain_dfs_soundness') as d:
        td=Path(d)
        # Pair mandatory plus cover pruning positive case.
        domain=[1,2,3,4,5,6]; target=4; force=[]
        constraints=[(1,{1,2,3}),(1,{1,2,4})]
        pair_rows=list(constraints)
        cover_rows=[(2,{3,4,5})]
        b=brute(domain,force,constraints,pair_rows,cover_rows,target)
        r,_,_=run_case(td,'mandatory_cover_positive',domain,force,constraints,pair_rows,cover_rows,target)
        cases.append({'name':'mandatory_cover_positive','brute':len(b),'cpp':r['solutions'],'solutions_head':[list(x) for x in b[:5]],'pair_forces':r['pair_forces'],'cover_prunes':r['cover_prunes'],'complete':r['complete']})
        # Cover-only rejection at terminal/interior.
        domain=[1,2,3,4,5,6,7]; target=4; force=[]
        constraints=[]; pair_rows=[(3,{1,2,3,4})]  # no useful pair alone
        cover_rows=[(1,{1,2,3}), (2,{4,5,6})]
        b=brute(domain,force,constraints,pair_rows,cover_rows,target)
        r,_,_=run_case(td,'cover_reject',domain,force,constraints,pair_rows,cover_rows,target)
        cases.append({'name':'cover_reject','brute':len(b),'cpp':r['solutions'],'solutions_head':[list(x) for x in b[:5]],'cover_prunes':r['cover_prunes'],'complete':r['complete']})
        total_b=0; total_cpp=0; total_pair=0; total_cover=0
        for t in range(150):
            n=random.randint(6,10); domain=list(range(1,n+1)); target=random.randint(2,min(5,n)); force=sorted(random.sample(domain,random.randint(0,min(2,target))))
            constraints=[]; cover_rows=[]; pair_rows=[]
            for _ in range(random.randint(0,5)):
                pts=set(random.sample(domain,random.randint(1,n))); cap=random.randint(0,min(len(pts),target)); constraints.append((cap,pts))
            for _ in range(random.randint(0,5)):
                pts=set(random.sample(domain,random.randint(1,n))); cap=random.randint(0,min(len(pts),target)); cover_rows.append((cap,pts))
            for _ in range(random.randint(2,6)):
                pts=set(random.sample(domain,random.randint(1,n))); cap=random.randint(0,min(len(pts),max(1,target-1))); pair_rows.append((cap,pts))
            b=brute(domain,force,constraints,pair_rows,cover_rows,target)
            r,_,_=run_case(td,f'rand{t}',domain,force,constraints,pair_rows,cover_rows,target,timeout=5,cover_min_depth=0)
            total_b+=len(b); total_cpp+=int(r['solutions']); total_pair+=int(r.get('pair_prunes',0)); total_cover+=int(r.get('cover_prunes',0))
            if (not r['complete']) or int(r['solutions'])!=len(b):
                mismatches.append({'trial':t,'domain':domain,'target':target,'force':force,'constraints':[(c,sorted(p)) for c,p in constraints],'pair_rows':[(c,sorted(p)) for c,p in pair_rows],'cover_rows':[(c,sorted(p)) for c,p in cover_rows],'brute':len(b),'cpp':r})
                if len(mismatches)>=5: break
        cases.append({'name':'random_suite','trials':150,'mismatches':mismatches,'total_brute':total_b,'total_cpp':total_cpp,'total_pair_prunes':total_pair,'total_cover_prunes':total_cover})
    out={'schema':'s0908_pair_cover_soundness_test_v1','runner':str(BIN),'cases':cases,'status':'ok' if not mismatches and all(c.get('brute',c.get('total_brute'))==c.get('cpp',c.get('total_cpp')) for c in cases[:-1]) else 'mismatch'}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
