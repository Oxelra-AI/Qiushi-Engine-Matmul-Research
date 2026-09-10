#!/usr/bin/env python3
"""analysis soundness tests for signed pair-inequality propagation DFS.

The analysis runner maintained pair margins with future O-points, which is a valid
search upper bound but not a terminal validity test.  This review checks the
patched analysis runner against brute force on small artificial E11WANG1 systems,
including satisfiable cases where propagation marks mandatory points.
"""
from __future__ import annotations
import json, os, random, struct, subprocess, tempfile
from pathlib import Path
from itertools import combinations

ROOT = Path('research/research_record')
BIN = ROOT/'workspace/scripts/pair_prop_dfs'
OUT = ROOT/'workspace/data/domain_dfs_soundness/pair_prop_soundness_test.json'
MAGIC = b'E11WANG1'


def mask_words(points):
    words=[0,0,0,0]
    for p in points:
        words[p>>6] |= 1 << (p&63)
    return words


def write_rows(path: Path, rows):
    with path.open('wb') as f:
        f.write(MAGIC)
        f.write(struct.pack('<I', len(rows)))
        for cap, pts in rows:
            words=mask_words(pts)
            f.write(struct.pack('<BBHQQQQ', cap, 0, 0, *words))


def eval_support(supp, constraints, pair_rows, target):
    S=set(supp)
    for cap, pts in constraints:
        if len(S & set(pts)) > cap:
            return False
    # pair inequalities generated from all row pairs with threshold>0
    for i in range(len(pair_rows)):
        ci, Ri = pair_rows[i]
        Ri=set(Ri)
        for j in range(i+1,len(pair_rows)):
            cj, Rj = pair_rows[j]
            thr = target - ci - cj
            if thr <= 0:
                continue
            Rj=set(Rj)
            I = Ri & Rj
            O = set(range(1,256)) - (Ri | Rj)
            lhs = len(S & O) - len(S & I)
            if lhs < thr:
                return False
    return True


def brute(domain, force, constraints, pair_rows, target):
    force=tuple(sorted(force))
    fset=set(force)
    avail=[p for p in domain if p not in fset]
    if len(force)>target:
        return []
    sol=[]
    for comb in combinations(avail, target-len(force)):
        s=tuple(sorted(force+comb))
        if eval_support(s,constraints,pair_rows,target):
            sol.append(s)
    return sol


def run_case(tmpdir: Path, name: str, domain, force, constraints, pair_rows, target=4, timeout=5):
    cons_path=tmpdir/f'{name}_cons.bin'
    pair_path=tmpdir/f'{name}_pair.bin'
    out_path=tmpdir/f'{name}_out.json'
    write_rows(cons_path,constraints)
    write_rows(pair_path,pair_rows)
    exclude=[p for p in range(1,256) if p not in set(domain)]
    cmd=[str(BIN),'--constraints',str(cons_path),'--pair-rows',str(pair_path),'--target',str(target),'--timeout',str(timeout),'--output',str(out_path)]
    if force:
        cmd += ['--force', ','.join(map(str,sorted(force)))]
    if exclude:
        cmd += ['--exclude', ','.join(map(str,exclude))]
    cp=subprocess.run(cmd, text=True, capture_output=True, timeout=timeout+3)
    if cp.returncode != 0:
        raise RuntimeError(f'runner failed {cp.returncode}\nSTDOUT={cp.stdout}\nSTDERR={cp.stderr}')
    data=json.loads(out_path.read_text())
    r=data['results'][0]
    return r, cp.stdout, cp.stderr


def main():
    random.seed(18018)
    cases=[]
    with tempfile.TemporaryDirectory(dir=ROOT/'workspace/data/domain_dfs_soundness') as td:
        td=Path(td)
        # Positive mandatory propagation case.  With target=4 and two cap-1 rows
        # R={1,2,3}, S={1,2,4}, the signed pair inequality has threshold 2,
        # I={1,2}, and (within the restricted test domain) O={5,6}.
        # At the root the margin is tight, so the propagator must exclude 1,2
        # and mark 5,6 mandatory.  The unique valid support is {3,4,5,6}.
        domain=[1,2,3,4,5,6]
        force=[]
        cons=[(1,{1,2,3}),(1,{1,2,4})]
        pairs=list(cons)
        target=4
        b=brute(domain,tuple(force),cons,pairs,target)
        r,_,_=run_case(td,'positive_mandatory',domain,force,cons,pairs,target)
        cases.append({'name':'positive_mandatory','brute':len(b),'cpp':r['solutions'],'solutions_head':[list(x) for x in b[:5]],'pair_forces':r['pair_forces'],'pair_prunes':r['pair_prunes'],'complete':r['complete']})
        # Terminal-only rejection case. The maintained margin can stay nonnegative because O-points
        # remain in the domain, but selected support violates signed inequality.
        domain=[1,2,3,4,5,6]
        force=[]
        cons=[]
        pairs=[(1,{1,2,3,4}),(1,{1,2,3,5})]  # target=4 => threshold 2, I={1,2,3}, O={6,...}; support {1,2,3,4} violates.
        target=4
        b=brute(domain,tuple(force),cons,pairs,target)
        r,_,_=run_case(td,'terminal_reject',domain,force,cons,pairs,target)
        cases.append({'name':'terminal_reject','brute':len(b),'cpp':r['solutions'],'solutions_head':[list(x) for x in b[:5]],'pair_prunes':r['pair_prunes'],'complete':r['complete']})
        # Random small cases. Constraint rows and pair rows are separate; brute force evaluates both.
        mismatches=[]
        total_b=0; total_cpp=0; total_force=0; total_pair_prunes=0
        for t in range(120):
            n=random.randint(6,10)
            domain=list(range(1,n+1))
            target=random.randint(2,min(5,n))
            force=sorted(random.sample(domain, random.randint(0,min(2,target))))
            cons=[]
            for _ in range(random.randint(0,5)):
                pts=set(random.sample(domain, random.randint(1,n)))
                cap=random.randint(0,min(len(pts),target))
                cons.append((cap,pts))
            pair_rows=[]
            for _ in range(random.randint(2,6)):
                pts=set(random.sample(domain, random.randint(1,n)))
                cap=random.randint(0,min(len(pts),max(1,target-1)))
                pair_rows.append((cap,pts))
            b=brute(domain,tuple(force),cons,pair_rows,target)
            r,_,_=run_case(td,f'rand{t}',domain,force,cons,pair_rows,target)
            total_b += len(b); total_cpp += int(r['solutions']); total_force += int(r.get('pair_forces',0)); total_pair_prunes += int(r.get('pair_prunes',0))
            if (not r['complete']) or int(r['solutions']) != len(b):
                mismatches.append({'trial':t,'domain':domain,'target':target,'force':force,'constraints':[(c,sorted(p)) for c,p in cons],'pair_rows':[(c,sorted(p)) for c,p in pair_rows],'brute':len(b),'cpp':r})
                if len(mismatches)>=5:
                    break
        cases.append({'name':'random_suite','trials':120,'mismatches':mismatches[:5],'total_brute':total_b,'total_cpp':total_cpp,'total_pair_forces':total_force,'total_pair_prunes':total_pair_prunes})
    out={'schema':'s0908_pair_prop_soundness_test_v1','runner':str(BIN),'cases':cases,'status':'ok' if not cases[-1]['mismatches'] and all(c.get('brute',c.get('total_brute'))==c.get('cpp',c.get('total_cpp')) for c in cases[:-1]) else 'mismatch'}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
