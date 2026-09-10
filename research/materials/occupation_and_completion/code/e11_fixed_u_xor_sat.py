#!/usr/bin/env python3
"""Fixed-A E11 core SAT with native XOR clauses for CryptoMiniSat.

For fixed A masks u_t, introduce B bits v_{t,b}, C bits w_{t,c}, and products
p_{t,b,c}=v_{t,b} & w_{t,c}.  Each Brent equation is the native XOR

    xor_{t: u_t[a]=1} p_{t,b,c} = T[a,b,c].

CryptoMiniSat can exploit Gaussian elimination on these XORs.  SAT models are
decoded and verified exactly over F2.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import time
from pathlib import Path

import numpy as np


def vec_from_mask(mask:int,n:int):
    return np.array([(int(mask)>>i)&1 for i in range(n)],dtype=np.uint8)


def parse_model(stdout:str):
    vals=[]
    for line in stdout.splitlines():
        if line.startswith('v'):
            for tok in line.split()[1:]:
                try: z=int(tok)
                except ValueError: continue
                if z: vals.append(z)
    return vals


def verify(core, us, vs, ws):
    R=np.zeros_like(core,dtype=np.uint8)
    for u,v,w in zip(us,vs,ws):
        R ^= (vec_from_mask(u,core.shape[0]).reshape(-1,1,1)*vec_from_mask(v,core.shape[1]).reshape(1,-1,1)*vec_from_mask(w,core.shape[2]).reshape(1,1,-1)).astype(np.uint8)
    diff=R^core
    return bool(not diff.any()), int(diff.sum())


def save_npz(path:Path, us, vs, ws, dims):
    U=np.zeros((len(us),dims[0]),dtype=np.uint8)
    V=np.zeros((len(us),dims[1]),dtype=np.uint8)
    W=np.zeros((len(us),dims[2]),dtype=np.uint8)
    for t,(u,v,w) in enumerate(zip(us,vs,ws)):
        U[t]=vec_from_mask(u,dims[0]); V[t]=vec_from_mask(v,dims[1]); W[t]=vec_from_mask(w,dims[2])
    np.savez(path,U=U,V=V,W=W,u_masks=np.array(us,dtype=np.uint16),v_masks=np.array(vs,dtype=np.uint16),w_masks=np.array(ws,dtype=np.uint16))


class XCNF:
    def __init__(self):
        self.next=1; self.cnf=[]; self.xors=[]
    def new(self):
        v=self.next; self.next+=1; return v
    def add(self,cl): self.cnf.append([int(x) for x in cl])
    def and_var(self,a,b):
        p=self.new()
        self.add([-a,-b,p]); self.add([a,-p]); self.add([b,-p])
        return p
    def add_xor(self,lits,rhs):
        ll=list(map(int,lits))
        rhs=int(rhs)&1
        # Empty Brent XORs occur if a fixed A-list does not cover an A-coordinate.
        # Encode 0=0 by adding nothing and 0=1 by an empty CNF clause.  The earlier
        # writer emitted `x 0` for both cases, which is not a reliable distinction.
        if not ll:
            if rhs:
                self.add([])
            return
        self.xors.append((ll, rhs))
    def write(self,path:Path,comments=None):
        path.parent.mkdir(parents=True,exist_ok=True)
        with path.open('w') as f:
            for c in comments or []: f.write('c '+c+'\n')
            f.write(f'p cnf {self.next-1} {len(self.cnf)+len(self.xors)}\n')
            for lits,rhs in self.xors:
                if not lits:
                    # add_xor handles empty equations by either adding no clause
                    # or adding a CNF contradiction, so empty XOR lines should not
                    # be emitted.  Keep a safe fallback for hand-built XCNF objects.
                    if rhs:
                        f.write('0\n')
                    continue
                # CryptoMiniSat DIMACS XOR: x lit... 0 means XOR(lits)=true;
                # negate first literal to encode XOR(lits)=false.
                ll=list(lits)
                if rhs==0:
                    ll[0] = -ll[0]
                f.write('x '+' '.join(map(str,ll))+' 0\n')
            for cl in self.cnf:
                f.write(' '.join(map(str,cl))+' 0\n')


def build(core, us):
    m,nv,nw=core.shape; r=len(us)
    F=XCNF(); vvar={}; wvar={}; pvar={}
    for t in range(r):
        for b in range(nv): vvar[(t,b)]=F.new()
        for c in range(nw): wvar[(t,c)]=F.new()
    for t in range(r):
        for b in range(nv):
            for c in range(nw):
                pvar[(t,b,c)]=F.and_var(vvar[(t,b)],wvar[(t,c)])
    for a in range(m):
        active=[t for t,u in enumerate(us) if (int(u)>>a)&1]
        for b in range(nv):
            for c in range(nw):
                F.add_xor([pvar[(t,b,c)] for t in active], int(core[a,b,c]))
    maps={'v':vvar,'w':wvar,'r':r,'nv':nv,'nw':nw}
    return F,maps


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--core',type=Path,default=Path('data/restricted_cores/mask_001_E11_core.npy'))
    ap.add_argument('--u-list',required=True)
    ap.add_argument('--outdir',type=Path,required=True)
    ap.add_argument('--name',default='fixed_u_xor')
    ap.add_argument('--solver',default='cryptominisat5')
    ap.add_argument('--timeout',type=int,default=120)
    ap.add_argument('--threads',type=int,default=4)
    ap.add_argument('--maxconfl',type=int,default=0)
    args=ap.parse_args()
    core=np.load(args.core).astype(np.uint8)&1
    us=[int(x) for x in args.u_list.split(',') if x.strip()]
    F,maps=build(core,us)
    args.outdir.mkdir(parents=True,exist_ok=True)
    cnf_path=args.outdir/(args.name+'.xor.cnf')
    F.write(cnf_path,[f'E11 fixed-U native XOR rank={len(us)}'])
    cmd=[args.solver,'--verb','0','-t',str(args.threads),'--maxtime',str(args.timeout)]
    if args.maxconfl>0:
        cmd += ['--maxconfl',str(args.maxconfl)]
    cmd.append(str(cnf_path))
    t0=time.time()
    proc=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=args.timeout+20)
    elapsed=time.time()-t0
    status='UNKNOWN'
    if re.search(r'\bUNSATISFIABLE\b',proc.stdout): status='UNSAT'
    elif re.search(r'\bSATISFIABLE\b',proc.stdout): status='SAT'
    result={'core':str(args.core),'rank':len(us),'u_masks':us,'vars':F.next-1,'and_clauses':len(F.cnf),'xor_clauses':len(F.xors),'cnf_path':str(cnf_path),
            'command':' '.join(cmd),'solver_status':status,'returncode':proc.returncode,'elapsed_sec':elapsed,'stdout_tail':proc.stdout[-4000:],'stderr_tail':proc.stderr[-2000:]}
    if status=='SAT':
        model=parse_model(proc.stdout); pos={x for x in model if x>0}
        vs=[]; ws=[]
        for t in range(len(us)):
            vm=0; wm=0
            for b in range(core.shape[1]):
                if maps['v'][(t,b)] in pos: vm|=1<<b
            for c in range(core.shape[2]):
                if maps['w'][(t,c)] in pos: wm|=1<<c
            vs.append(vm); ws.append(wm)
        ok,diff=verify(core,us,vs,ws)
        sol_path=args.outdir/(args.name+'.solution.npz')
        save_npz(sol_path,us,vs,ws,core.shape)
        result['decoded_solution']={'v_masks':vs,'w_masks':ws,'verified':ok,'diff_count':diff,'solution_npz':str(sol_path),'model_lit_count':len(model)}
    out=args.outdir/(args.name+'.json')
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:result[k] for k in ['rank','vars','and_clauses','xor_clauses','solver_status','returncode','elapsed_sec']},indent=2,sort_keys=True))
    if 'decoded_solution' in result: print(json.dumps(result['decoded_solution'],indent=2,sort_keys=True)[:2000])
    print(f'wrote {out}')

if __name__=='__main__': main()
