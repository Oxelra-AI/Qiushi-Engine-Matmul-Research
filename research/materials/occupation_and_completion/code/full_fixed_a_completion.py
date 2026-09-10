#!/usr/bin/env python3
"""Fixed-A Brent completion SAT for full T<3,3,3> over F2.

Given a full A-multiset of length r, solve for B/C masks v_t,w_t such that
    XOR_t a_t[s] v_t[b] w_t[c] = T[s,b,c]
for all 9*9*9 Brent equations.  SAT witnesses are reconstructed exactly.
UNSAT without a replayed proof is only local fixed-A evidence.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Sequence

import numpy as np

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from pivot_fixed_full_wang import parse_multiset_arg  # type: ignore


def build_t333() -> np.ndarray:
    T=np.zeros((9,9,9),dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j,3*j+k,3*i+k]=1
    return T


class CNF:
    def __init__(self):
        self.nv=0; self.clauses=[]
    def new_var(self):
        self.nv+=1; return self.nv
    def add(self,cl):
        self.clauses.append([int(x) for x in cl])
    def add_and2(self,z,x,y):
        self.add([-z,x]); self.add([-z,y]); self.add([-x,-y,z])
    def add_xor_eq(self, xs, rhs:int):
        xs=[int(x) for x in xs]
        rhs=int(rhs)&1
        if not xs:
            if rhs: self.add([])
            return
        if len(xs)==1:
            self.add([xs[0] if rhs else -xs[0]]); return
        def xor_clauses(a,b,c):
            self.add([-a,-b,-c]); self.add([a,b,-c]); self.add([a,-b,c]); self.add([-a,b,c])
        cur=xs[0]
        for x in xs[1:]:
            z=self.new_var(); xor_clauses(cur,x,z); cur=z
        self.add([cur if rhs else -cur])
    def write(self,path:Path,comments=None):
        with path.open('w') as f:
            if comments:
                for c in comments: f.write('c '+str(c).replace('\n',' ')+'\n')
            f.write(f'p cnf {self.nv} {len(self.clauses)}\n')
            for cl in self.clauses:
                f.write(' '.join(map(str,cl))+' 0\n')


def encode_fixed_a(A:Sequence[int], cnf_path:Path)->dict:
    T=build_t333(); r=len(A); F=CNF()
    V=[[F.new_var() for _ in range(9)] for _ in range(r)]
    W=[[F.new_var() for _ in range(9)] for _ in range(r)]
    P=[[[F.new_var() for _ in range(9)] for _ in range(9)] for _ in range(r)]
    for t in range(r):
        for b in range(9):
            for c in range(9):
                F.add_and2(P[t][b][c],V[t][b],W[t][c])
    xor_terms=0
    for s in range(9):
        active=[t for t,a in enumerate(A) if (int(a)>>s)&1]
        for b in range(9):
            for c in range(9):
                xs=[P[t][b][c] for t in active]
                xor_terms += len(xs)
                F.add_xor_eq(xs,int(T[s,b,c]))
    comments=[f'full T333 fixed-A over F2 rank={r}', 'A_multiset='+','.join(map(str,A))[:1000], f'xor_terms_total={xor_terms}']
    cnf_path.parent.mkdir(parents=True,exist_ok=True)
    F.write(cnf_path,comments)
    return {'rank':r,'cnf_vars':F.nv,'cnf_clauses':len(F.clauses),'base_vw_vars':2*r*9,'product_vars':r*81,'xor_terms_total':xor_terms,'cnf_path':str(cnf_path)}


def parse_solver_solution(stdout:str, r:int):
    vals={}
    for line in stdout.splitlines():
        if line.startswith('v '):
            for tok in line.split()[1:]:
                z=int(tok)
                if z: vals[abs(z)]= z>0
    if not vals: return None
    # Variable order: V then W then products. V ids 1..9r; W ids 9r+1..18r
    B=[]; C=[]
    for t in range(r):
        bmask=0; cmask=0
        for b in range(9):
            if vals.get(1+t*9+b,False): bmask|=1<<b
        off=9*r
        for c in range(9):
            if vals.get(1+off+t*9+c,False): cmask|=1<<c
        B.append(bmask); C.append(cmask)
    return B,C


def verify(A,B,C):
    T=build_t333(); R=np.zeros_like(T)
    for a,b,c in zip(A,B,C):
        for s in range(9):
            if not ((int(a)>>s)&1): continue
            for i in range(9):
                if not ((int(b)>>i)&1): continue
                for j in range(9):
                    if (int(c)>>j)&1: R[s,i,j]^=1
    return int(np.sum(R^T))


def solve(cnf:Path, timeout:int):
    t=time.time()
    proc=subprocess.run(['cadical',str(cnf)],capture_output=True,text=True,timeout=timeout+10)
    return proc,time.time()-t


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--multiset',required=True)
    ap.add_argument('--outdir',type=Path,required=True)
    ap.add_argument('--name',default='fixedA')
    ap.add_argument('--timeout',type=int,default=300)
    args=ap.parse_args()
    A=parse_multiset_arg(args.multiset)
    outdir=args.outdir; outdir.mkdir(parents=True,exist_ok=True)
    cnf=outdir/(args.name+'.cnf')
    info=encode_fixed_a(A,cnf)
    proc,elapsed=solve(cnf,args.timeout)
    sat=None
    if proc.returncode==10: sat=True
    elif proc.returncode==20: sat=False
    rec={'schema':'full_fixed_a_completion_v1','A_multiset':[int(x) for x in A],'A_size':len(A),'encoding':info,'solver':'cadical','returncode':int(proc.returncode),'sat':sat,'elapsed_sec':elapsed,'stdout_tail':'\n'.join(proc.stdout.splitlines()[-40:]),'stderr_tail':'\n'.join(proc.stderr.splitlines()[-40:])}
    if sat is True:
        sol=parse_solver_solution(proc.stdout,len(A))
        if sol is not None:
            B,C=sol; diff=verify(A,B,C)
            rec['verification_diff']=diff
            rec['B_masks']=[int(x) for x in B]; rec['C_masks']=[int(x) for x in C]
            if diff==0:
                wit=outdir/(args.name+'_witness.json')
                wit.write_text(json.dumps({'terms':[[int(a),int(b),int(c)] for a,b,c in zip(A,B,C)],'rank':len(A),'verified':True},indent=2,sort_keys=True)+'\n')
                rec['witness_path']=str(wit)
    out=outdir/(args.name+'_result.json')
    out.write_text(json.dumps(rec,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(out),'sat':sat,'returncode':proc.returncode,'elapsed_sec':elapsed,'vars':info['cnf_vars'],'clauses':info['cnf_clauses'],'verification_diff':rec.get('verification_diff')},indent=2,sort_keys=True))

if __name__=='__main__': main()
