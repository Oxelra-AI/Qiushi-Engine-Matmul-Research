#!/usr/bin/env python3
"""Compare analysis C++ upper-bound DFS with brute force on random small instances."""
from __future__ import annotations
import itertools, json, random, struct, subprocess, tempfile
from pathlib import Path

OUT = Path("data/domain_dfs_soundness")
CPP = Path("scripts/sound_domain_dfs")
MAGIC = b"E11WANG1"


def words(points):
    w=[0,0,0,0]
    for p in points:
        w[p>>6] |= 1 << (p&63)
    return w


def write_bin(path, rows):
    with open(path,'wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I', len(rows)))
        for cap, pts in rows:
            f.write(struct.pack('<BBHQQQQ', cap, min(7, len(pts)), 0, *words(pts)))


def brute(n, target, rows, force=(), exclude=()):
    force=set(force); exclude=set(exclude)
    ans=[]
    for comb in itertools.combinations(range(1,n+1), target):
        s=set(comb)
        if not force <= s: continue
        if s & exclude: continue
        if all(len(s & set(pts)) <= cap for cap,pts in rows):
            ans.append(tuple(comb))
    return ans


def run_cpp(bin_path, n, target, force=(), exclude=()):
    out_path = OUT / "tmp_cpp_random_out.json"
    cmd=[str(CPP),'--constraints',str(bin_path),'--target',str(target),'--max-point',str(n),'--timeout','30','--output',str(out_path)]
    if force:
        cmd += ['--force', ','.join(map(str, sorted(force)))]
    if exclude:
        cmd += ['--exclude', ','.join(map(str, sorted(exclude)))]
    proc=subprocess.run(cmd, text=True, capture_output=True, timeout=35)
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr)
    data=json.loads(out_path.read_text())
    return data


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    rng=random.Random(13091702)
    mismatches=[]; examples=[]; aggregate={"trials":0,"total_bruteforce":0,"total_cpp_reported":0,"cases_with_force":0,"cases_with_exclude":0}
    for t in range(120):
        n=rng.randint(4,10); target=rng.randint(0,min(5,n))
        rows=[]
        for _ in range(rng.randint(0,10)):
            size=rng.randint(0,n)
            pts=tuple(sorted(rng.sample(range(1,n+1), size)))
            cap=rng.randint(0,size) if size else 0
            rows.append((cap,pts))
        # Sometimes force/exclude points to exercise preloaded selections and forbidden points.
        force=tuple(sorted(rng.sample(range(1,n+1), rng.randint(0,min(2,target))))) if rng.random()<0.35 else tuple()
        possible_ex=[p for p in range(1,n+1) if p not in force]
        exclude=tuple(sorted(rng.sample(possible_ex, rng.randint(0,min(2,len(possible_ex)))))) if rng.random()<0.35 else tuple()
        if force: aggregate["cases_with_force"] += 1
        if exclude: aggregate["cases_with_exclude"] += 1
        bin_path=OUT/f"tmp_random_{t}.bin"
        write_bin(bin_path, rows)
        b=brute(n,target,rows,force,exclude)
        data=run_cpp(bin_path,n,target,force,exclude)
        cpp_sols=[tuple(x) for x in data['results'][0]['solutions_head']]
        # C++ stores only first 5 solutions, but reports total count.
        ok_count=(data['total_solutions']==len(b))
        ok_head=all(s in b for s in cpp_sols)
        aggregate["trials"] += 1
        aggregate["total_bruteforce"] += len(b)
        aggregate["total_cpp_reported"] += data['total_solutions']
        if not (ok_count and ok_head and data['all_complete']):
            mismatches.append({
                'trial':t,'n':n,'target':target,'rows':[{'cap':cap,'pts':pts} for cap,pts in rows],
                'force':force,'exclude':exclude,'brute_count':len(b),'brute_head':b[:10],
                'cpp_total':data['total_solutions'],'cpp_head':cpp_sols,'all_complete':data['all_complete'],
                'cpp_summary':{k:data[k] for k in ['global_max_depth','total_recursive_calls','total_candidate_tests','total_saturation_point_removals']}
            })
            break
        if len(examples)<5 and data['total_saturation_point_removals']:
            examples.append({'trial':t,'n':n,'target':target,'rows':[{'cap':cap,'pts':pts} for cap,pts in rows], 'force':force,'exclude':exclude,'solutions':len(b),'cpp_summary':{k:data[k] for k in ['total_recursive_calls','total_candidate_tests','total_saturation_point_removals','total_global_shortage']}})
        try: bin_path.unlink()
        except OSError: pass
    result={'schema':'s0908_cpp_soundness_random_v1','aggregate':aggregate,'mismatches':mismatches,'examples':examples}
    out=OUT/'cpp_soundness_random.json'
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
