#!/usr/bin/env python3
"""Exact Brent CNF for quotient tensors T333/span(p) over F2.

Variables: rank r terms (u in F2^8, v,w in F2^9).  Equations are
  XOR_t u_t[s] v_t[b] w_t[c] = Q_p[s,b,c]
where Q_p is the linear quotient of the A factor by span(p), using the same
projection convention as prepare_quotient_wang_binary.py.  Slice-capacity lower
bounds are rank(Q_p[s,:,:]) and are encoded by forbidding fewer active terms;
this is sound because a matrix slice of rank k requires at least k rank-one
summands among terms with u_t[s]=1. Term sorting by u is optional.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, os, sys
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from quotient_line_caps_and_controls import quotient_tensor, recon_quotient, vec, gf2_rank_mat

class CNF:
    def __init__(self):
        self.nv=0; self.clauses=[]; self.names={}; self.rev={}; self.comments=[]
    def new_var(self,name):
        self.nv+=1; self.names[name]=self.nv; self.rev[self.nv]=name; return self.nv
    def add(self,c):
        c=[int(x) for x in c]
        if not c: raise ValueError('empty clause')
        self.clauses.append(c)
    def unit(self,lit): self.add([lit])
    def and2(self,out,a,b):
        self.add([-out,a]); self.add([-out,b]); self.add([out,-a,-b])
    def xor2(self,out,a,b):
        self.add([-a,-b,-out]); self.add([-a,b,out]); self.add([a,-b,out]); self.add([a,b,-out])
    def xor_equals(self,xs,target,stem):
        target=int(target)&1
        if len(xs)==0:
            if target: raise ValueError('false empty XOR')
            return
        if len(xs)==1:
            self.unit(xs[0] if target else -xs[0]); return
        acc=self.new_var(f'{stem}.xor0'); self.xor2(acc,xs[0],xs[1])
        for i,x in enumerate(xs[2:],start=1):
            nxt=self.new_var(f'{stem}.xor{i}'); self.xor2(nxt,acc,x); acc=nxt
        self.unit(acc if target else -acc)
    def prefix_eq_step(self,out,prev,a,b):
        if prev is not None: self.add([-out,prev])
        self.add([-out,-a,b]); self.add([-out,a,-b])
        if prev is None:
            self.add([out,a,b]); self.add([out,-a,-b])
        else:
            self.add([-prev,a,b,out]); self.add([-prev,-a,-b,out])
    def write(self,path:Path):
        path.parent.mkdir(parents=True,exist_ok=True)
        with open(path,'w') as f:
            for c in self.comments: f.write(f'c {c}\n')
            f.write(f'p cnf {self.nv} {len(self.clauses)}\n')
            for cl in self.clauses: f.write(' '.join(map(str,cl))+' 0\n')
    def validate(self,A,max_bad=20):
        bad=[]
        for i,cl in enumerate(self.clauses):
            ok=False
            for lit in cl:
                val=A.get(abs(lit))
                if val is None: raise KeyError(f'missing var {abs(lit)} {self.rev.get(abs(lit))}')
                if (lit>0 and val) or (lit<0 and not val): ok=True; break
            if not ok:
                bad.append({'clause_index':i,'clause':cl,'names':[self.rev.get(abs(x),'?') for x in cl]})
                if len(bad)>=max_bad: break
        return {'ok':not bad,'num_clauses':len(self.clauses),'bad_head':bad}

class Encoder:
    def __init__(self, pivot:int, rank:int, sort_u:bool=True, capacity:bool=True, known_terms:Optional[List[Tuple[int,int,int]]]=None, known_units:bool=False):
        self.pivot=pivot; self.rank=rank; self.sort_u=sort_u; self.capacity=capacity; self.known_terms=known_terms; self.known_units=known_units
        self.tensor=quotient_tensor(pivot).astype(np.uint8)&1
        self.slice_ranks=[gf2_rank_mat(self.tensor[s]) for s in range(8)]
        self.F=CNF(); self.u=[]; self.v=[]; self.w=[]; self.uv={}; self.prod={}; self.layers=[]
    def make_base(self):
        for t in range(self.rank):
            self.u.append([self.F.new_var(f'u[{t},{s}]') for s in range(8)])
            self.v.append([self.F.new_var(f'v[{t},{b}]') for b in range(9)])
            self.w.append([self.F.new_var(f'w[{t},{c}]') for c in range(9)])
    def add_brent(self):
        self.layers.append('certified:quotient_Brent+Tseytin+XOR')
        for t in range(self.rank):
            for s in range(8):
                for b in range(9):
                    x=self.F.new_var(f'uv[{t},{s},{b}]'); self.uv[(t,s,b)]=x; self.F.and2(x,self.u[t][s],self.v[t][b])
        for s in range(8):
            for b in range(9):
                for c in range(9):
                    xs=[]
                    for t in range(self.rank):
                        x=self.F.new_var(f'p[{t},{s},{b},{c}]'); self.prod[(t,s,b,c)]=x; self.F.and2(x,self.uv[(t,s,b)],self.w[t][c]); xs.append(x)
                    self.F.xor_equals(xs,int(self.tensor[s,b,c]),f'eq[{s},{b},{c}]')
    def add_capacity(self):
        if not self.capacity: return
        self.layers.append('certified:slice_capacity_ge_matrix_rank')
        for s,k in enumerate(self.slice_ranks):
            vars_s=[self.u[t][s] for t in range(self.rank)]
            for j in range(k):
                for true_set in itertools.combinations(range(self.rank), j):
                    T=set(true_set); self.F.add([-var if t in T else var for t,var in enumerate(vars_s)])
    def add_sort(self):
        if not self.sort_u: return
        self.layers.append('certified:term_sort_u_integer_nondecreasing')
        for t in range(self.rank-1):
            prev=None
            for bit in range(7,-1,-1):
                a=self.u[t][bit]; b=self.u[t+1][bit]
                if prev is None: self.F.add([-a,b])
                else: self.F.add([-prev,-a,b])
                if bit>0:
                    nxt=self.F.new_var(f'lexeq_u[{t},{bit}]'); self.F.prefix_eq_step(nxt,prev,a,b); prev=nxt
    def add_units(self):
        if not self.known_units: return
        if self.known_terms is None or len(self.known_terms)!=self.rank: raise ValueError('known term mismatch')
        self.layers.append('control:known_base_units')
        terms=sorted(self.known_terms,key=lambda x:(x[0],x[1],x[2])) if self.sort_u else self.known_terms
        for t,(um,vm,wm) in enumerate(terms):
            for bit,var in enumerate(self.u[t]): self.F.unit(var if ((um>>bit)&1) else -var)
            for bit,var in enumerate(self.v[t]): self.F.unit(var if ((vm>>bit)&1) else -var)
            for bit,var in enumerate(self.w[t]): self.F.unit(var if ((wm>>bit)&1) else -var)
    def build(self):
        self.make_base(); self.add_brent(); self.add_capacity(); self.add_sort(); self.add_units()
        self.F.comments += [f'Quotient T333/span(p) CPD over F2, pivot={self.pivot}', f'rank={self.rank}', f'tensor_nnz={int(self.tensor.sum())}', f'slice_ranks={self.slice_ranks}', 'layers='+','.join(self.layers)]
        return self.F
    def assignment(self):
        if self.known_terms is None: raise ValueError('no known terms')
        terms=sorted(self.known_terms,key=lambda x:(x[0],x[1],x[2])) if self.sort_u else self.known_terms
        A={}
        for t,(um,vm,wm) in enumerate(terms):
            for bit,var in enumerate(self.u[t]): A[var]=(um>>bit)&1
            for bit,var in enumerate(self.v[t]): A[var]=(vm>>bit)&1
            for bit,var in enumerate(self.w[t]): A[var]=(wm>>bit)&1
        for key,var in self.uv.items():
            t,s,b=key; A[var]=A[self.u[t][s]] & A[self.v[t][b]]
        for key,var in self.prod.items():
            t,s,b,c=key; A[var]=A[self.uv[(t,s,b)]] & A[self.w[t][c]]
        # lexeq vars
        for vnum,name in sorted(self.F.rev.items()):
            if name.startswith('lexeq_u['):
                inside=name[len('lexeq_u['):-1]; t_s,bit_s=inside.split(','); t=int(t_s); bit=int(bit_s)
                A[vnum]=1 if all(A[self.u[t][j]]==A[self.u[t+1][j]] for j in range(7,bit-1,-1)) else 0
        # XOR chain vars
        groups={}
        for vnum,name in sorted(self.F.rev.items()):
            if name.startswith('eq[') and '.xor' in name:
                left,idx=name.split('.xor'); s,b,c=map(int,left[len('eq['):-1].split(',')); groups.setdefault((s,b,c),[]).append((int(idx),vnum))
        for (s,b,c),items in groups.items():
            vals=[A[self.prod[(t,s,b,c)]] for t in range(self.rank)]
            # recompute robustly sequentially
            amap=dict(items)
            acc=vals[0]^vals[1]
            A[amap[0]]=acc
            for idx in range(1,len(items)):
                acc ^= vals[idx+1]; A[amap[idx]]=acc
        return A

def sha(path:Path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for chunk in iter(lambda:f.read(1<<20),b''): h.update(chunk)
    return h.hexdigest()

def load_known_json(path:Path,pivot:int)->List[Tuple[int,int,int]]:
    d=json.loads(path.read_text())
    qlist=d.get('quotient_a_multiset') or d.get('q_multiset')
    # Need B/C factors too; rank2_quotient_rank22_control.json stores only q_multiset, not q terms.
    qterms=d.get('quotient_terms_full') or d.get('terms')
    if qterms is None:
        raise ValueError('known JSON lacks quotient_terms_full/terms')
    return [tuple(map(int,t)) for t in qterms]

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--pivot',type=int,required=True)
    ap.add_argument('--rank',type=int,default=19)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--meta',type=Path,default=None)
    ap.add_argument('--no-sort-u',action='store_true')
    ap.add_argument('--no-capacity',action='store_true')
    ap.add_argument('--known-json',type=Path,default=None)
    ap.add_argument('--known-units',action='store_true')
    ap.add_argument('--validate-known',action='store_true')
    args=ap.parse_args()
    known=None; recon_diff=None
    if args.known_json:
        known=load_known_json(args.known_json,args.pivot)
        if len(known)!=args.rank: raise ValueError(f'known len {len(known)} != rank {args.rank}')
    enc=Encoder(args.pivot,args.rank,sort_u=not args.no_sort_u,capacity=not args.no_capacity,known_terms=known,known_units=args.known_units)
    if known is not None:
        R=np.zeros((8,9,9),dtype=np.uint8)
        for q,b,c in known:
            R ^= (vec(q,8).reshape(8,1,1)*vec(b,9).reshape(1,9,1)*vec(c,9).reshape(1,1,9)).astype(np.uint8)
        recon_diff=int(np.count_nonzero(R!=enc.tensor))
        if recon_diff!=0: raise ValueError(f'known quotient terms diff {recon_diff}')
    F=enc.build(); known_validation=None
    if args.validate_known:
        A=enc.assignment(); known_validation=F.validate(A)
        if not known_validation['ok']:
            print(json.dumps(known_validation,indent=2)); raise SystemExit(1)
    F.write(args.out); digest=sha(args.out)
    meta={"status":"ok","problem":"quotient_core_cpd","pivot":args.pivot,"rank":args.rank,"tensor_shape":[8,9,9],"tensor_nnz":int(enc.tensor.sum()),"slice_ranks":enc.slice_ranks,"num_vars":F.nv,"num_clauses":len(F.clauses),"base_vars":args.rank*26,"sort_u":not args.no_sort_u,"capacity":not args.no_capacity,"layers":enc.layers,"cnf_path":str(args.out),"sha256":digest,"known_json":str(args.known_json) if args.known_json else None,"known_reconstruction_diff":recon_diff,"known_units":args.known_units,"known_validation":known_validation}
    mp=args.meta or args.out.with_suffix(args.out.suffix+'.meta.json'); mp.parent.mkdir(parents=True,exist_ok=True); mp.write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps({"status":"ok","cnf":str(args.out),"meta":str(mp),"vars":F.nv,"clauses":len(F.clauses),"slice_ranks":enc.slice_ranks,"known_validation_ok":None if known_validation is None else known_validation['ok']},indent=2,sort_keys=True))

if __name__=='__main__': main()
