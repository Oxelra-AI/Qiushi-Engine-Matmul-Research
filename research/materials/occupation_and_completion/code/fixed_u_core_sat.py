#!/usr/bin/env python3
"""SAT/verification for an F2 core CPD with fixed A-side factors.

For fixed nonzero A masks u_t, an r-term CPD of a core T in F2^{m x 9 x 9}
amounts to finding v_t,w_t such that

    T[a,b,c] = XOR_t u_t[a] * v_t[b] * w_t[c].

This encoder introduces p_{t,b,c}=v_{t,b}&w_{t,c}; because u is fixed, no cube
variables are needed.  The resulting CNF is much smaller than the full Brent
encoding and is useful for testing A-support candidates from an orbit/capacity
search.  A SAT result is decoded and independently verified as a CPD.
"""
from __future__ import annotations

import argparse, itertools, json, re, subprocess, time
from pathlib import Path
from typing import Iterable

import numpy as np


def vec_from_mask(mask:int,n:int):
    return np.array([(int(mask)>>i)&1 for i in range(n)],dtype=np.uint8)


def load_core(path):
    return np.load(path).astype(np.uint8)&1


def row_terms(row,rank):
    vals=[int(x) for x in row.tolist()]
    return [tuple(vals[3*i:3*i+3]) for i in range(rank)]


def load_u_list(args):
    if args.source=='pool':
        arr=np.load(args.pool)
        rank=arr.shape[1]//3
        terms=row_terms(arr[args.row],rank)
        dels=set(args.delete or [])
        us=[u for i,(u,v,w) in enumerate(terms) if i not in dels]
        known=[(u,v,w) for i,(u,v,w) in enumerate(terms) if i not in dels]
        return us, known, {'source':'pool','pool':args.pool,'row':args.row,'original_rank':rank,'deleted':sorted(dels)}
    if args.source=='capacity':
        d=json.loads(Path(args.capacity_json).read_text())
        sol=d.get('final_solution')
        if sol is None and d.get('iterations'):
            for it in reversed(d['iterations']):
                if 'solution' in it:
                    sol=it['solution']; break
        if sol is None:
            raise ValueError('no solution/final_solution in capacity json')
        us=[]
        for k,v in sorted(((int(k),int(v)) for k,v in sol.items())):
            us += [k]*v
        return us, None, {'source':'capacity','capacity_json':args.capacity_json,'support_size':len(sol)}
    if args.source=='list':
        us=[int(x) for x in args.u_list.split(',') if x.strip()]
        return us, None, {'source':'list'}
    raise ValueError(args.source)


class CNF:
    def __init__(self):
        self.next=1; self.clauses=[]
    def new(self):
        v=self.next; self.next+=1; return v
    def add(self,lits):
        self.clauses.append([int(x) for x in lits])
    def and_var(self,a,b):
        p=self.new()
        self.add([-a,-b,p]); self.add([a,-p]); self.add([b,-p])
        return p
    def xor_eq(self,vars_list,target:int):
        xs=list(vars_list)
        if not xs:
            if target: self.add([])
            return
        if len(xs)==1:
            self.add([xs[0] if target else -xs[0]])
            return
        prev=xs[0]
        for i,curr in enumerate(xs[1:], start=1):
            if i < len(xs)-1:
                z=self.new()
                # z = prev XOR curr
                self.add([-prev,-curr,-z]); self.add([prev,curr,-z]); self.add([prev,-curr,z]); self.add([-prev,curr,z])
                prev=z
            else:
                if target:
                    self.add([-prev,-curr]); self.add([prev,curr])
                else:
                    self.add([-prev,curr]); self.add([prev,-curr])
    def write(self,path:Path,comments=None):
        path.parent.mkdir(parents=True,exist_ok=True)
        with path.open('w') as f:
            for c in comments or []:
                f.write('c '+c+'\n')
            f.write(f'p cnf {self.next-1} {len(self.clauses)}\n')
            for cl in self.clauses:
                f.write(' '.join(map(str,cl))+' 0\n')


def build_cnf(core, us):
    m,nv,nw=core.shape; r=len(us)
    cnf=CNF(); vvar={}; wvar={}; pvar={}
    for t in range(r):
        for b in range(nv): vvar[(t,b)]=cnf.new()
        for c in range(nw): wvar[(t,c)]=cnf.new()
    for t in range(r):
        for b in range(nv):
            for c in range(nw):
                pvar[(t,b,c)]=cnf.and_var(vvar[(t,b)],wvar[(t,c)])
    for a in range(m):
        active=[t for t,u in enumerate(us) if (int(u)>>a)&1]
        for b in range(nv):
            for c in range(nw):
                cnf.xor_eq([pvar[(t,b,c)] for t in active], int(core[a,b,c]))
    maps={'v':{f'{t},{b}':var for (t,b),var in vvar.items()},
          'w':{f'{t},{c}':var for (t,c),var in wvar.items()},
          'r':r,'m':m,'nv':nv,'nw':nw,'u_masks':list(map(int,us))}
    return cnf,maps


def verify_cpd(core, us, vs, ws):
    R=np.zeros_like(core,dtype=np.uint8)
    for u,v,w in zip(us,vs,ws):
        R ^= (vec_from_mask(u,core.shape[0]).reshape(-1,1,1)*vec_from_mask(v,core.shape[1]).reshape(1,-1,1)*vec_from_mask(w,core.shape[2]).reshape(1,1,-1)).astype(np.uint8)
    return bool(np.array_equal(R,core)), int(np.sum(R^core))


def verify_known(core, known):
    if known is None: return None
    us=[u for u,v,w in known]; vs=[v for u,v,w in known]; ws=[w for u,v,w in known]
    ok,diff=verify_cpd(core,us,vs,ws)
    return {'known_rank':len(known),'verified':ok,'diff_count':diff}


def parse_dimacs_model(stdout:str):
    vals=[]
    for line in stdout.splitlines():
        if line.startswith('v'):
            for tok in line.split()[1:]:
                try:
                    z=int(tok)
                except ValueError:
                    continue
                if z==0:
                    continue
                vals.append(z)
    return vals


def solve_cnf(cnf_path:Path, solver:str, timeout_sec:int):
    cmd=[solver,str(cnf_path)]
    t0=time.time()
    try:
        proc=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=timeout_sec)
        status='UNKNOWN'
        if 's UNSATISFIABLE' in proc.stdout or re.search(r'\bUNSATISFIABLE\b',proc.stdout): status='UNSAT'
        elif 's SATISFIABLE' in proc.stdout or re.search(r'\bSATISFIABLE\b',proc.stdout): status='SAT'
        model=parse_dimacs_model(proc.stdout) if status=='SAT' else None
        return {'solver':solver,'returncode':proc.returncode,'status':status,'elapsed_sec':time.time()-t0,
                'model_lit_count':None if model is None else len(model),'model':model,
                'stdout_tail':proc.stdout[-4000:],'stderr_tail':proc.stderr[-2000:]}
    except subprocess.TimeoutExpired as exc:
        return {'solver':solver,'returncode':None,'status':'TIMEOUT','elapsed_sec':time.time()-t0,
                'model_lit_count':None,'model':None,
                'stdout_tail':(exc.stdout or '')[-4000:] if isinstance(exc.stdout,str) else '',
                'stderr_tail':(exc.stderr or '')[-2000:] if isinstance(exc.stderr,str) else ''}


def save_core_npz(path:Path, us, vs, ws, dims):
    m,nv,nw=dims
    U=np.zeros((len(us),m),dtype=np.uint8)
    V=np.zeros((len(us),nv),dtype=np.uint8)
    W=np.zeros((len(us),nw),dtype=np.uint8)
    for t,(u,v,w) in enumerate(zip(us,vs,ws)):
        U[t]=vec_from_mask(u,m)
        V[t]=vec_from_mask(v,nv)
        W[t]=vec_from_mask(w,nw)
    path.parent.mkdir(parents=True,exist_ok=True)
    np.savez(path,U=U,V=V,W=W,u_masks=np.array(us,dtype=np.uint16),v_masks=np.array(vs,dtype=np.uint16),w_masks=np.array(ws,dtype=np.uint16))


def decode_model(maps, model_lits):
    pos={int(x) for x in model_lits if int(x)>0}
    r=maps['r']; nv=maps['nv']; nw=maps['nw']
    vs=[]; ws=[]
    for t in range(r):
        vm=0; wm=0
        for b in range(nv):
            if maps['v'][f'{t},{b}'] in pos:
                vm |= 1<<b
        for c in range(nw):
            if maps['w'][f'{t},{c}'] in pos:
                wm |= 1<<c
        vs.append(vm); ws.append(wm)
    return vs,ws


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--core',default='data/restricted_cores/mask_001_E11_core.npy')
    ap.add_argument('--source',choices=['pool','capacity','list'],required=True)
    ap.add_argument('--pool',default='data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy')
    ap.add_argument('--row',type=int,default=0)
    ap.add_argument('--delete',type=int,nargs='*')
    ap.add_argument('--capacity-json',default='data/core_capacity/core_capacity_E11_s19.json')
    ap.add_argument('--u-list',default='')
    ap.add_argument('--outdir',required=True)
    ap.add_argument('--name',default='fixed_u')
    ap.add_argument('--solve',action='store_true')
    ap.add_argument('--solver',default='kissat')
    ap.add_argument('--timeout',type=int,default=60)
    args=ap.parse_args()
    outdir=Path(args.outdir); outdir.mkdir(parents=True,exist_ok=True)
    core=load_core(args.core)
    us, known, src=load_u_list(args)
    cnf,maps=build_cnf(core,us)
    cnf_path=outdir/(args.name+'.cnf')
    cnf.write(cnf_path,[f'fixed-U core SAT source={src}',f'rank={len(us)} core={args.core}'])
    known_check=verify_known(core,known)
    result={'core':args.core,'source':src,'rank':len(us),'u_masks':list(map(int,us)),
            'u_rank':None,'cnf_path':str(cnf_path),'vars':cnf.next-1,'clauses':len(cnf.clauses),
            'known_check':known_check}
    # rank of U factors as columns of F2^m
    basis=[]
    for u in us:
        basis.append(int(u))
    # local rank function on m-bit columns
    B={}
    for u in basis:
        x=u
        while x:
            p=x.bit_length()-1
            if p in B: x^=B[p]
            else: B[p]=x; break
    result['u_rank']=len(B)
    if args.solve:
        result['solve']=solve_cnf(cnf_path,args.solver,args.timeout)
        if result['solve'].get('status')=='SAT' and result['solve'].get('model'):
            vs,ws=decode_model(maps,result['solve']['model'])
            ok,diff=verify_cpd(core,us,vs,ws)
            sol_npz=outdir/(args.name+'.solution.npz')
            save_core_npz(sol_npz,us,vs,ws,core.shape)
            result['decoded_solution']={'v_masks':vs,'w_masks':ws,'verified':ok,'diff_count':diff,'solution_npz':str(sol_npz)}
            # Do not bloat downstream JSON with the full solver assignment after decoding.
            result['solve']['model']=None
    (outdir/(args.name+'.json')).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:result[k] for k in ['rank','u_rank','vars','clauses','known_check']},indent=2))
    if 'solve' in result:
        print(json.dumps(result['solve'],indent=2)[:5000])
    print('wrote',outdir/(args.name+'.json'))

if __name__=='__main__':
    main()
