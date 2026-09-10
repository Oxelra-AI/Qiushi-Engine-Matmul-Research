#!/usr/bin/env python3
"""analysis: small-instance tests for the bitset upper/lower-row enumerator.

The C++ bitset search is used on the E11 A-support problem, but this file tests
it on tiny independently enumerable systems.  Rows of type E11WANG1 are upper
bounds |S∩R|<=cap.  Rows of type MIXCUT1 are lower bounds sum c_p x_p >= K with
c_p in {0,1,2}.  A cap-zero row removes all points outside the tiny universe so
that the C++ MAXP=255 search is exactly comparable with brute force on {1..n}.
"""
from __future__ import annotations
import itertools, json, random, shutil, struct, subprocess, time
from pathlib import Path

ROOT=Path('research/research_record')
BIN=ROOT/'workspace/scripts/sound_bitset_dfs'
OUT=ROOT/'workspace/data/domain_dfs_soundness/bitset_mixed_soundness_test.json'
MAGIC_ROWS=b'E11WANG1'
MAGIC_CUTS=b'MIXCUT1\0'


def words(pts):
    w=[0,0,0,0]
    for p in pts:
        w[p>>6] |= 1 << (p&63)
    return w


def write_rows(path:Path,n:int,rows):
    packed=[]
    outside=list(range(n+1,256))
    packed.append((0,0,words(outside)))
    for cap,pts in rows:
        packed.append((int(cap),0,words(pts)))
    blob=bytearray(); blob.extend(MAGIC_ROWS); blob.extend(struct.pack('<I',len(packed)))
    for cap,dim,w in packed:
        blob.extend(struct.pack('<BBHQQQQ',cap,dim,0,*w))
    path.write_bytes(blob)


def write_cuts(path:Path,cuts):
    blob=bytearray(); blob.extend(MAGIC_CUTS); blob.extend(struct.pack('<I',len(cuts)))
    for K,c1,c2 in cuts:
        w1=words(c1); w2=words(c2)
        if set(c1)&set(c2):
            raise AssertionError('cut coefficient sets overlap')
        blob.extend(struct.pack('<BBHQQQQQQQQ',int(K),0,0,*w1,*w2))
    path.write_bytes(blob)


def feasible(S,rows,cuts):
    SS=set(S)
    for cap,pts in rows:
        if len(SS & set(pts)) > cap:
            return False
    for K,c1,c2 in cuts:
        val=len(SS & set(c1)) + 2*len(SS & set(c2))
        if val < K:
            return False
    return True


def brute(n,target,rows,cuts,force=(),exclude=()):
    f=set(force); e=set(exclude)
    ans=[]
    for S in itertools.combinations(range(1,n+1),target):
        SS=set(S)
        if not f <= SS or SS & e:
            continue
        if feasible(S,rows,cuts):
            ans.append(list(S))
    return ans


def run_cpp(row_path,cut_path,target,force=(),exclude=(),timeout=5):
    cmd=[str(BIN),'--constraints',str(row_path),'--target',str(target),'--timeout',str(timeout)]
    if cut_path is not None:
        cmd += ['--cuts',str(cut_path)]
    if force:
        cmd += ['--force',','.join(map(str,force))]
    if exclude:
        cmd += ['--exclude',','.join(map(str,exclude))]
    cp=subprocess.run(cmd,capture_output=True,text=True,check=True)
    # first stdout line is the single-run JSON
    line=cp.stdout.strip().splitlines()[0]
    return json.loads(line)


def random_instance(rng,n):
    rows=[]
    for _ in range(rng.randint(2,7)):
        pts=[p for p in range(1,n+1) if rng.random()<rng.uniform(0.25,0.75)]
        if not pts:
            pts=[rng.randint(1,n)]
        cap=rng.randint(0,len(pts))
        rows.append((cap,pts))
    cuts=[]
    for _ in range(rng.randint(0,4)):
        c1=[]; c2=[]
        for p in range(1,n+1):
            r=rng.random()
            if r<0.22: c2.append(p)
            elif r<0.52: c1.append(p)
        maxv=len(c1)+2*len(c2)
        if maxv:
            K=rng.randint(0,min(maxv, max(0, 2*n)))
            cuts.append((K,c1,c2))
    target=rng.randint(0,min(n,5))
    force=[]; exclude=[]
    for p in range(1,n+1):
        r=rng.random()
        if r<0.05: force.append(p)
        elif r<0.10: exclude.append(p)
    if len(force)>target:
        force=force[:target]
    return target,rows,cuts,force,exclude


def main():
    t0=time.time(); rng=random.Random(1401)
    OUT.parent.mkdir(parents=True,exist_ok=True)
    cases=[]; mismatches=[]; skipped_many=0
    td=OUT.parent/'bitset_mixed_tmp'
    td.mkdir(parents=True, exist_ok=True)
    # Deterministic lower-cut example: upper bounds alone have many supports,
    # the lower row requires a high coefficient point.
    fixed=[(4,3,[(1,[1,2]),(2,[2,3,4])],[(2,[4],[1])],[1],[])]
    for idx,(n,target,rows,cuts,force,exclude) in enumerate(fixed):
        rp=td/f'fixed{idx}.rows.bin'; cp=td/f'fixed{idx}.cuts.bin'; write_rows(rp,n,rows); write_cuts(cp,cuts)
        b=brute(n,target,rows,cuts,force,exclude); c=run_cpp(rp,cp,target,force,exclude)
        cases.append({'kind':'fixed','idx':idx,'n':n,'target':target,'brute':len(b),'cpp':c['solutions'],'head':b[:10],'cpp_head':c['solutions_head']})
        if len(b)!=c['solutions'] or sorted(b[:5])!=sorted(c['solutions_head'][:5]):
            mismatches.append(cases[-1])
    for trial in range(80):
        n=rng.randint(4,10)
        target,rows,cuts,force,exclude=random_instance(rng,n)
        b=brute(n,target,rows,cuts,force,exclude)
        if len(b)>100:
            skipped_many += 1
            continue
        rp=td/f'r{trial}.bin'; cp=td/f'c{trial}.bin'; write_rows(rp,n,rows); write_cuts(cp,cuts)
        c=run_cpp(rp,cp,target,force,exclude)
        rec={'kind':'random','trial':trial,'n':n,'target':target,'force':force,'exclude':exclude,'rows':rows,'cuts':cuts,'brute':len(b),'cpp':c['solutions'],'cpp_complete':c['complete'],'cpp_timeout':c['timeout'],'head':b[:5],'cpp_head':c['solutions_head'][:5]}
        cases.append(rec)
        if len(b)!=c['solutions'] or not c['complete'] or c['timeout']:
            mismatches.append(rec)
    out={'schema':'s0908_bitset_mixed_soundness_v1','semantics':'Tiny brute-force comparison for upper Wang rows and mixed lower cuts; outside points removed by a cap-zero row.','trials_recorded':len(cases),'skipped_bruteforce_gt100':skipped_many,'mismatch_count':len(mismatches),'mismatches':mismatches[:5],'cases_head':cases[:8],'total_bruteforce_solutions':sum(c['brute'] for c in cases),'total_cpp_solutions':sum(c['cpp'] for c in cases),'elapsed_sec':time.time()-t0}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
