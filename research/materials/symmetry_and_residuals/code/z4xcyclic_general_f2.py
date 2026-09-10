#!/usr/bin/env python3
"""
analysis: broader F2 SAT for fixed-a0 Z4-inner x cyclic-outer equivariant decompositions.

The acting group H=<tau> is cyclic of order 12, where
    tau(A,B,C) = (g B, g C, g A),  g(X)=a0 X a0^{-1} over F2.
A nominal orbit of length d in {1,2,3,4,6,12} is represented by a vector triple
fixed by tau^d, and contributes tau^r(rep) for r=0..d-1.  Allowing larger
stabilizer/zero representatives only enlarges the encoded <=rank family.

This covers the fixed single-inner-element H-equivariant F2 family, not arbitrary
three-sided Z4xZ3 equivariance and not characteristic zero.
"""
from __future__ import annotations
import argparse, itertools, json, subprocess, time
from pathlib import Path

import z4_cyclic_sat_f2 as base

SCRIPT_DIR=Path(__file__).resolve().parent
WS=SCRIPT_DIR.parent
OUT=WS/'data'/'z4xcyclic_general_f2'


def eye(n): return [[1 if i==j else 0 for j in range(n)] for i in range(n)]

def matmul2(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(len(B))) & 1 for j in range(len(B[0]))] for i in range(len(A))]

def mat_add_I(M):
    n=len(M); return [[M[i][j] ^ (1 if i==j else 0) for j in range(n)] for i in range(n)]

def tau_matrix27(G):
    # tau(A,B,C)=(G B, G C, G A), concatenated A|B|C.
    T=[[0]*27 for _ in range(27)]
    # output A block from input B block
    for i in range(9):
        for j in range(9):
            T[i][9+j]=G[i][j]
            T[9+i][18+j]=G[i][j]
            T[18+i][j]=G[i][j]
    return T

def mat_vec_expr(enc,M,vec):
    out=[]
    for i in range(len(M)):
        out.append(enc.lin_var([vec[j] for j in range(len(vec)) if M[i][j] and vec[j]!=0]))
    return out

def split_triple(vec27):
    return vec27[:9],vec27[9:18],vec27[18:27]

def param_from_basis(enc,basis):
    ps=enc.new_vars(len(basis))
    coords=[]
    for i in range(27):
        coords.append(enc.lin_var([ps[j] for j,b in enumerate(basis) if b[i]&1]))
    return coords,ps

def build_group_data():
    A=[[0,0,1],[1,0,1],[0,1,1]]
    G=base.conj_matrix_mod2(A)
    Tau=tau_matrix27(G)
    Tp=[eye(27)]
    for _ in range(12):
        Tp.append(matmul2(Tp[-1],Tau))
    assert Tp[12]==eye(27)
    dims={}
    bases={}
    for d in [1,2,3,4,6,12]:
        B=base.nullspace2(mat_add_I(Tp[d]))  # char2: tau^d - I = tau^d + I
        bases[d]=B; dims[d]=len(B)
    return Tau,Tp,bases,dims

def encode(pattern,sym_break=True):
    T333=base.build_T333(); reps=base.cyclic_orbit_reps()
    Tau,Tp,bases,dims=build_group_data()
    enc=base.CMSEncoder()
    orbit_terms=[]; rep_exprs_by_d={d:[] for d in [1,2,3,4,6,12]}; param_dims=[]
    for d in pattern:
        if d not in bases: raise ValueError(d)
        rep,ps=param_from_basis(enc,bases[d])
        rep_exprs_by_d[d].append(rep); param_dims.append(len(ps))
        for r in range(d):
            tr=mat_vec_expr(enc,Tp[r],rep)
            orbit_terms.append(split_triple(tr))
    if sym_break:
        for d,vecs in rep_exprs_by_d.items():
            for i in range(len(vecs)-1):
                enc.add_lex_le(vecs[i],vecs[i+1])
    for (i,j,k) in reps:
        terms=[]
        for U,V,W in orbit_terms:
            p=enc.AND3(U[i],V[j],W[k])
            if p: terms.append(p)
        enc.xor_terms(terms,T333[i][j][k])
    vmap={'pattern':pattern,'orbit_terms':orbit_terms,'dims':dims,'param_dims':param_dims}
    return enc,vmap

def run_cms(path,timeout):
    t0=time.time()
    try:
        r=subprocess.run(['cryptominisat5','--verb','0',str(path)],capture_output=True,text=True,timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT',{},time.time()-t0,'',''
    assign={}
    if r.returncode==10:
        for line in r.stdout.splitlines():
            if line.startswith('v '):
                for tok in line[2:].split():
                    lit=int(tok)
                    if lit==0: break
                    assign[abs(lit)]=lit>0
        return 'SAT',assign,time.time()-t0,r.stdout,r.stderr
    if r.returncode==20:
        return 'UNSAT',{},time.time()-t0,r.stdout,r.stderr
    return f'RC{r.returncode}',{},time.time()-t0,r.stdout,r.stderr

def direct_verify(assign,pattern):
    enc,vmap=encode(pattern,sym_break=True)
    T=base.build_T333()
    terms=[tuple(base.eval_vec(assign,x) for x in triple) for triple in vmap['orbit_terms']]
    errs=[]
    for i,j,k in itertools.product(range(9),repeat=3):
        val=0
        for U,V,W in terms:
            val ^= (U[i]&V[j]&W[k])
        if val!=T[i][j][k]: errs.append((i,j,k,val,T[i][j][k]))
    # Compute actual nonzero term count and unique rank-one terms as rough diagnostics.
    nz=sum(1 for U,V,W in terms if any(U) and any(V) and any(W))
    unique=len({tuple(U+V+W) for U,V,W in terms if any(U) and any(V) and any(W)})
    return {'brent_errors':len(errs),'brent_error_examples':errs[:5],'nominal_terms':sum(pattern),'nonzero_full_triples':nz,'unique_nonzero_triples':unique,
            'terms':terms}

def parse_patterns(s):
    if s=='probe':
        return [[12,6,4],[12,6,3,1],[12,6,2,2],[12,4,3,3],[12,4,3,2,1],[12,4,4,2],[12,4,4,1,1]]
    if s=='bilr23': return [[12,4,4,2,1]]
    out=[]
    for part in s.split(';'):
        if part.strip(): out.append([int(x) for x in part.split(',')])
    return out

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--patterns',default='probe')
    ap.add_argument('--timeout',type=int,default=300)
    args=ap.parse_args()
    OUT.mkdir(parents=True,exist_ok=True)
    _,_,_,dims=build_group_data()
    print('fixed-space dims by nominal orbit length',dims)
    pats=parse_patterns(args.patterns)
    results=[]
    for pat in pats:
        tag='p'+'_'.join(map(str,pat))
        print('\n',tag,pat)
        t0=time.time(); enc,vmap=encode(pat,sym_break=True); enc_sec=time.time()-t0
        cnf=OUT/f'z4xcyc_general_{tag}.cnf'; enc.write(cnf)
        print('  vars',enc.nv,'reg',len(enc.reg),'xor',len(enc.xors),'lin',len(enc.lin_cache),'param_dims',vmap['param_dims'],'enc',round(enc_sec,3))
        status,assign,sec,stdout,stderr=run_cms(cnf,args.timeout)
        print(' ',status,round(sec,2),'s')
        rec={'pattern':pat,'tag':tag,'vars':enc.nv,'regular_clauses':len(enc.reg),'xor_clauses':len(enc.xors),
             'linear_aux_vars':len(enc.lin_cache),'param_dims':vmap['param_dims'],'status':status,'solve_sec':round(sec,3),'cnf':str(cnf)}
        if status=='SAT':
            chk=direct_verify(assign,pat); rec['check']=chk
            rec['true_vars']=[v for v,b in sorted(assign.items()) if b][:2000]
            print('  check', {k:v for k,v in chk.items() if k!='terms'})
        if stdout.strip(): rec['solver_stdout_tail']=stdout[-1000:]
        if stderr.strip(): rec['solver_stderr_tail']=stderr[-1000:]
        results.append(rec)
        (OUT/'z4xcyclic_general_results_partial.json').write_text(json.dumps({'dims':dims,'results':results},indent=2)+'\n')
    out=OUT/'z4xcyclic_general_results.json'
    out.write_text(json.dumps({'field':'F2','tau':'(A,B,C)->(gB,gC,gA), g=a0 conjugation mod2','fixed_dims':dims,'results':results},indent=2)+'\n')
    print('Saved',out)
if __name__=='__main__': main()
