#!/usr/bin/env python3
"""analysis: brute-force soundness tests for one-row residual-capacity pruning.

The tested C++ runner has three row families:
  * constraints: upper rows used for saturation propagation and over-cap checks;
  * cover-constraints: upper Wang rows used for over-cap checks and residual-
    capacity global-size pruning |Q| <= u_R + |F\R|;
  * mixed lower cuts.
A cap-zero row restricts the C++ universe to {1..n}.
"""
from __future__ import annotations
import itertools, json, random, struct, subprocess, time
from pathlib import Path
ROOT=Path('research/research_record')
BIN=ROOT/'workspace/scripts/cover_bitset_dfs'
OUT=ROOT/'workspace/data/domain_dfs_soundness/cover_soundness_test.json'
MAGIC_ROWS=b'E11WANG1'; MAGIC_CUTS=b'MIXCUT1\0'

def words(pts):
    w=[0,0,0,0]
    for p in pts:
        w[p>>6] |= 1<<(p&63)
    return w

def write_rows(path:Path,n:int,rows,add_outside=True):
    packed=[]
    if add_outside:
        packed.append((0,0,words(range(n+1,256))))
    for cap,pts in rows:
        packed.append((int(cap),0,words(pts)))
    blob=bytearray(); blob.extend(MAGIC_ROWS); blob.extend(struct.pack('<I',len(packed)))
    for cap,dim,w in packed:
        blob.extend(struct.pack('<BBHQQQQ',cap,dim,0,*w))
    path.write_bytes(blob)

def write_cuts(path:Path,cuts):
    blob=bytearray(); blob.extend(MAGIC_CUTS); blob.extend(struct.pack('<I',len(cuts)))
    for K,c1,c2 in cuts:
        if set(c1)&set(c2): raise AssertionError('overlap')
        blob.extend(struct.pack('<BBHQQQQQQQQ',int(K),0,0,*words(c1),*words(c2)))
    path.write_bytes(blob)

def feasible(S,constraints,covers,cuts):
    SS=set(S)
    for cap,pts in constraints+[(cap,pts) for cap,pts in covers]:
        if len(SS & set(pts))>cap: return False
    for K,c1,c2 in cuts:
        if len(SS&set(c1))+2*len(SS&set(c2))<K: return False
    return True

def brute(n,target,constraints,covers,cuts,force=(),exclude=()):
    f=set(force); e=set(exclude); ans=[]
    for S in itertools.combinations(range(1,n+1),target):
        SS=set(S)
        if not f<=SS or SS&e: continue
        if feasible(S,constraints,covers,cuts): ans.append(list(S))
    return ans

def run_cpp(rp,cp,cup,target,force=(),exclude=(),min_depth=999,max_slack=-1):
    cmd=[str(BIN),'--constraints',str(rp),'--cover-constraints',str(cp),'--cuts',str(cup),'--target',str(target),'--timeout','10','--cover-min-depth',str(min_depth),'--cover-max-slack',str(max_slack)]
    if force: cmd += ['--force',','.join(map(str,force))]
    if exclude: cmd += ['--exclude',','.join(map(str,exclude))]
    out=subprocess.run(cmd,capture_output=True,text=True,check=True).stdout.strip().splitlines()[0]
    return json.loads(out)

def random_instance(rng,n):
    constraints=[]; covers=[]; cuts=[]
    for _ in range(rng.randint(0,4)):
        pts=[p for p in range(1,n+1) if rng.random()<rng.uniform(0.2,0.65)] or [rng.randint(1,n)]
        constraints.append((rng.randint(0,len(pts)),pts))
    for _ in range(rng.randint(1,7)):
        pts=[p for p in range(1,n+1) if rng.random()<rng.uniform(0.25,0.85)] or [rng.randint(1,n)]
        covers.append((rng.randint(0,len(pts)),pts))
    for _ in range(rng.randint(0,3)):
        c1=[]; c2=[]
        for p in range(1,n+1):
            r=rng.random()
            if r<0.20: c2.append(p)
            elif r<0.48: c1.append(p)
        if c1 or c2: cuts.append((rng.randint(0,len(c1)+2*len(c2)),c1,c2))
    target=rng.randint(0,min(6,n))
    force=[]; exclude=[]
    for p in range(1,n+1):
        r=rng.random()
        if r<0.04: force.append(p)
        elif r<0.09: exclude.append(p)
    if len(force)>target: force=force[:target]
    return target,constraints,covers,cuts,force,exclude

def main():
    t0=time.time(); rng=random.Random(1501); OUT.parent.mkdir(parents=True,exist_ok=True); td=OUT.parent/'cover_tmp'; td.mkdir(parents=True,exist_ok=True)
    cases=[]; mism=[]; skipped=0
    fixed=[
        # Unsat only via cover row with target size: after forcing 1, row {1,2,3,4} cap2 leaves u=1 and only one outside future point, so cannot fill need 3.
        (5,4,[],[(2,[1,2,3,4])],[],[1],[],0,-1),
        # Satisfiable counterpart where outside domain permits filling.
        (6,4,[],[(2,[1,2,3,4])],[],[1],[],0,-1),
        # Combination with a mixed lower cut.
        (6,3,[(1,[1,2])],[(2,[2,3,4,5])],[(4,[6],[3])],[1],[],0,-1),
    ]
    for idx,(n,target,constraints,covers,cuts,force,exclude,md,ms) in enumerate(fixed):
        rp=td/f'fixed{idx}.rows.bin'; cp=td/f'fixed{idx}.covers.bin'; cup=td/f'fixed{idx}.cuts.bin'
        write_rows(rp,n,constraints,True); write_rows(cp,n,covers,False); write_cuts(cup,cuts)
        b=brute(n,target,constraints,covers,cuts,force,exclude); c=run_cpp(rp,cp,cup,target,force,exclude,md,ms)
        rec={'kind':'fixed','idx':idx,'n':n,'target':target,'force':force,'constraints':constraints,'covers':covers,'cuts':cuts,'brute':len(b),'cpp':c['solutions'],'complete':c['complete'],'timeout':c['timeout'],'cover_prunes':c['cover_prunes'],'cover_certificates_head':c.get('cover_certificates_head',[]),'head':b[:5],'cpp_head':c['solutions_head'][:5]}
        cases.append(rec)
        if len(b)!=c['solutions'] or not c['complete'] or c['timeout'] or sorted(b[:5])!=sorted(c['solutions_head'][:5]): mism.append(rec)
    for trial in range(100):
        n=rng.randint(4,10); target,constraints,covers,cuts,force,exclude=random_instance(rng,n)
        b=brute(n,target,constraints,covers,cuts,force,exclude)
        if len(b)>100: skipped+=1; continue
        rp=td/f'r{trial}.bin'; cp=td/f'cov{trial}.bin'; cup=td/f'cut{trial}.bin'
        write_rows(rp,n,constraints,True); write_rows(cp,n,covers,False); write_cuts(cup,cuts)
        # Exercise both always-cover and slack-trigger modes deterministically.
        md=0 if trial%2==0 else 3; ms=-1 if trial%3 else 2
        c=run_cpp(rp,cp,cup,target,force,exclude,md,ms)
        rec={'kind':'random','trial':trial,'n':n,'target':target,'force':force,'exclude':exclude,'constraints':constraints,'covers':covers,'cuts':cuts,'cover_min_depth':md,'cover_max_slack':ms,'brute':len(b),'cpp':c['solutions'],'complete':c['complete'],'timeout':c['timeout'],'cover_prunes':c['cover_prunes'],'head':b[:5],'cpp_head':c['solutions_head'][:5]}
        cases.append(rec)
        if len(b)!=c['solutions'] or not c['complete'] or c['timeout']: mism.append(rec)
    out={'schema':'s0908_cover_soundness_v1','semantics':'Tiny brute-force comparison for upper constraints, separate cover upper rows with residual-capacity pruning, and mixed lower cuts.','trials_recorded':len(cases),'skipped_bruteforce_gt100':skipped,'mismatch_count':len(mism),'mismatches':mism[:5],'cases_head':cases[:8],'total_bruteforce_solutions':sum(c['brute'] for c in cases),'total_cpp_solutions':sum(c['cpp'] for c in cases),'total_cover_prunes':sum(c.get('cover_prunes',0) for c in cases),'elapsed_sec':time.time()-t0}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
