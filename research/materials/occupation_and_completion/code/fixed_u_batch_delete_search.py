#!/usr/bin/env python3
"""Batch fixed-A-factor SAT tests for E11 rank-19 core candidates.

Starting from exact rank-21 flip-cpd schemes, delete two terms and keep only the
resulting 19 A-factor multiset.  For each unique multiset, solve the exact
fixed-U Brent equations with all B/C factors free.  This is substantially less
local than fixed-UV deletion or replacement: only the A factors are inherited;
V and W are completely reoptimized.

A SAT result is decoded and verified as an E11 rank-19 CPD, which would lift to
a full F2 rank-22 scheme by the independently checked core lift.
"""
from __future__ import annotations

import argparse, itertools, json, re, subprocess, time
from collections import Counter
from pathlib import Path

import numpy as np

# Import construction routines from sibling script.
import sys
SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0,str(SCRIPT_DIR))
from fixed_u_core_sat import build_cnf, verify_cpd, vec_from_mask  # noqa: E402


def load_core(path):
    return np.load(path).astype(np.uint8)&1


def row_terms(row,rank):
    vals=[int(x) for x in row.tolist()]
    return [tuple(vals[3*i:3*i+3]) for i in range(rank)]


def parse_model(stdout:str):
    vals={}
    for line in stdout.splitlines():
        if not line.startswith('v'):
            continue
        for tok in line.split()[1:]:
            lit=int(tok)
            if lit==0: continue
            vals[abs(lit)]=lit>0
    return vals


def decode_solution(core, us, maps, stdout):
    vals=parse_model(stdout)
    r=maps['r']; nv=maps['nv']; nw=maps['nw']
    vs=[]; ws=[]
    for t in range(r):
        v=0; w=0
        for b in range(nv):
            if vals.get(maps['v'][f'{t},{b}'],False): v |= 1<<b
        for c in range(nw):
            if vals.get(maps['w'][f'{t},{c}'],False): w |= 1<<c
        vs.append(v); ws.append(w)
    ok,diff=verify_cpd(core,us,vs,ws)
    return {'verified':ok,'diff_count':diff,'u_masks':list(map(int,us)),'v_masks':vs,'w_masks':ws}


def save_solution_npz(path, core, sol):
    r=len(sol['u_masks'])
    U=np.zeros((r,core.shape[0]),dtype=np.uint8)
    V=np.zeros((r,core.shape[1]),dtype=np.uint8)
    W=np.zeros((r,core.shape[2]),dtype=np.uint8)
    for i,(u,v,w) in enumerate(zip(sol['u_masks'],sol['v_masks'],sol['w_masks'])):
        U[i]=vec_from_mask(u,core.shape[0]); V[i]=vec_from_mask(v,core.shape[1]); W[i]=vec_from_mask(w,core.shape[2])
    path.parent.mkdir(parents=True,exist_ok=True)
    np.savez(path,U=U,V=V,W=W)


def run_solver(cnf_path, solver, timeout):
    try:
        proc=subprocess.run([solver,str(cnf_path)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=timeout)
        out=proc.stdout
        if 's UNSATISFIABLE' in out:
            status='UNSAT'
        elif 's SATISFIABLE' in out:
            status='SAT'
        else:
            status='UNKNOWN'
        return status,proc.returncode,out,proc.stderr
    except subprocess.TimeoutExpired as exc:
        return 'TIMEOUT',None,exc.stdout or '',exc.stderr or ''


def u_rank(us):
    basis={}
    for u in us:
        x=int(u)
        while x:
            p=x.bit_length()-1
            if p in basis: x^=basis[p]
            else: basis[p]=x; break
    return len(basis)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--core',default='data/restricted_cores/mask_001_E11_core.npy')
    ap.add_argument('--pool',default='data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy')
    ap.add_argument('--outdir',required=True)
    ap.add_argument('--json-out',required=True)
    ap.add_argument('--selection',choices=['same-w','diff-w','all'],default='same-w')
    ap.add_argument('--max-supports',type=int,default=100)
    ap.add_argument('--timeout',type=int,default=5)
    ap.add_argument('--solver',default='kissat')
    ap.add_argument('--keep-cnf',action='store_true')
    args=ap.parse_args()
    t0=time.time(); outdir=Path(args.outdir); outdir.mkdir(parents=True,exist_ok=True)
    core=load_core(args.core)
    arr=np.load(args.pool); rank21=arr.shape[1]//3
    seen=set(); candidates=[]
    pair_type_counter=Counter(); unique_by_type=Counter()
    for si,row in enumerate(arr):
        terms=row_terms(row,rank21)
        for i,j in itertools.combinations(range(rank21),2):
            same=terms[i][2]==terms[j][2]
            ptype='same-w' if same else 'diff-w'
            pair_type_counter[ptype]+=1
            if args.selection!='all' and args.selection!=ptype:
                continue
            us=[terms[k][0] for k in range(rank21) if k not in (i,j)]
            key=tuple(sorted(us))
            if key in seen: continue
            seen.add(key); unique_by_type[ptype]+=1
            candidates.append({'scheme_index':si,'deleted':[i,j],'pair_type':ptype,'u_masks':us,'u_sorted':key,'u_rank':u_rank(us)})
            if len(candidates)>=args.max_supports:
                break
        if len(candidates)>=args.max_supports: break
    print(f'loaded {len(arr)} schemes; pair_type_counter={dict(pair_type_counter)}; unique selected={len(candidates)} selection={args.selection}')
    records=[]; status_counter=Counter(); found=None
    for ci,cand in enumerate(candidates):
        cnf,maps=build_cnf(core,cand['u_masks'])
        cnf_path=outdir/f'cand_{ci:04d}.cnf'
        cnf.write(cnf_path,[f"scheme={cand['scheme_index']} deleted={cand['deleted']} pair_type={cand['pair_type']} u_rank={cand['u_rank']}"])
        st=time.time(); status,rc,stdout,stderr=run_solver(cnf_path,args.solver,args.timeout); elapsed=time.time()-st
        status_counter[status]+=1
        rec={k:cand[k] for k in ['scheme_index','deleted','pair_type','u_rank']}
        if isinstance(stdout, bytes):
            stdout = stdout.decode('utf-8','replace')
        if isinstance(stderr, bytes):
            stderr = stderr.decode('utf-8','replace')
        rec.update({'candidate_index':ci,'status':status,'returncode':rc,'elapsed_sec':elapsed,'vars':cnf.next-1,'clauses':len(cnf.clauses),
                    'stdout_tail':stdout[-1000:] if status!='SAT' else stdout[-2000:], 'stderr_tail':stderr[-500:]})
        print(f"{ci+1}/{len(candidates)} {status} {elapsed:.2f}s scheme={cand['scheme_index']} del={cand['deleted']} u_rank={cand['u_rank']}")
        if status=='SAT':
            sol=decode_solution(core,cand['u_masks'],maps,stdout)
            rec['solution']=sol
            if sol['verified']:
                solpath=outdir/f'cand_{ci:04d}_rank19_solution.npz'
                save_solution_npz(solpath,core,sol)
                rec['solution_npz']=str(solpath)
                found=rec
                records.append(rec)
                break
        records.append(rec)
        if not args.keep_cnf:
            try: cnf_path.unlink()
            except FileNotFoundError: pass
    result={'core':args.core,'pool':args.pool,'selection':args.selection,'max_supports':args.max_supports,
            'timeout_per_instance_sec':args.timeout,'candidates_built':len(candidates),'tested':len(records),
            'pair_type_counter_seen_until_selection_stop':dict(pair_type_counter),'unique_by_type':dict(unique_by_type),
            'status_counter':dict(status_counter),'found':found,'records':records,'elapsed_sec':time.time()-t0,
            'interpretation':'UNSAT records exclude exact rank-19 E11 CPDs with the corresponding fixed 19-term A-factor multiset, while allowing B and C factors to vary freely. This is a local A-support exclusion, not a global lower bound unless all A supports are exhausted.'}
    Path(args.json_out).parent.mkdir(parents=True,exist_ok=True)
    Path(args.json_out).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('summary', {k:result[k] for k in ['tested','status_counter','found','elapsed_sec']})
    print('wrote',args.json_out)

if __name__=='__main__':
    main()
