#!/usr/bin/env python3
"""
analysis: F_2 exact SAT for the Z4-inner x cyclic-outer subfamily around BILR.

This is not the full rank-22 problem. It tests the additional equivariant ansatz
suggested by the BILR Z4 x Z3 rank-23 construction: one free cyclic triple whose
four inner Z4 conjugates give m=4, plus ten cyclic-fixed cubes arranged in Z4
orbits.  The equations are the cyclic representatives of T_<3,3,3> over F_2,
encoded with CryptoMiniSat native XOR clauses.

Orbit-size patterns are lists of cube orbit lengths in {1,2,4}; a length-d cube
orbit contributes sum_{k=0}^{d-1} (g^k l)^3.  Variables for length-1 and length-2
representatives are restricted to Fix(g) and Fix(g^2) respectively.  Degenerate
orbits are allowed; any SAT solution is still a valid <=22-term expression in the
encoded finite-field family after direct Brent verification.
"""
from __future__ import annotations
import argparse, itertools, json, subprocess, time
from pathlib import Path
from typing import Dict, List, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / 'data' / 'z4_cyclic_f2'

N = 9


def matmul2(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(len(B))) & 1 for j in range(len(B[0]))] for i in range(len(A))]


def inv3_mod2(A):
    n=3
    aug=[row[:] + [1 if i==j else 0 for j in range(n)] for i,row in enumerate([r[:] for r in A])]
    r=0
    for c in range(n):
        piv=None
        for i in range(r,n):
            if aug[i][c] & 1:
                piv=i; break
        if piv is None:
            raise ValueError('singular')
        aug[r],aug[piv]=aug[piv],aug[r]
        for i in range(n):
            if i!=r and (aug[i][c]&1):
                aug[i]=[x^y for x,y in zip(aug[i],aug[r])]
        r+=1
    return [row[n:] for row in aug]


def conj_matrix_mod2(A):
    """9x9 matrix for X -> A X A^{-1}, row-major flattening."""
    Ai=inv3_mod2(A)
    G=[[0]*9 for _ in range(9)]
    for p in range(3):
        for q in range(3):
            # basis E_pq
            for i in range(3):
                for j in range(3):
                    val=(A[i][p] & Ai[q][j])
                    if val:
                        G[3*i+j][3*p+q] ^= 1
    return G


def mat_vec2(G,x):
    return [sum(G[i][j]*x[j] for j in range(len(x))) & 1 for i in range(len(G))]


def rank_rref2(A):
    A=[row[:] for row in A]
    m=len(A); n=len(A[0]) if m else 0
    pivots=[]; r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if A[i][c]&1:
                piv=i; break
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]
        for i in range(m):
            if i!=r and (A[i][c]&1):
                A[i]=[x^y for x,y in zip(A[i],A[r])]
        pivots.append(c); r+=1
        if r==m: break
    return r,pivots,A


def nullspace2(A):
    if not A:
        return [[1 if i==j else 0 for i in range(0)] for j in range(0)]
    m=len(A); n=len(A[0])
    r,pivots,R=rank_rref2(A)
    pivset=set(pivots)
    free=[j for j in range(n) if j not in pivset]
    basis=[]
    for f in free:
        x=[0]*n; x[f]=1
        for row,p in enumerate(pivots):
            # pivot variable + sum R[row][free]*free = 0
            if R[row][f]&1:
                x[p]=1
        basis.append(x)
    return basis


def add2(A,B): return [[A[i][j]^B[i][j] for j in range(len(A[0]))] for i in range(len(A))]

def eye(n): return [[1 if i==j else 0 for j in range(n)] for i in range(n)]


def cyclic_orbit_reps():
    seen=set(); reps=[]
    for i,j,k in itertools.product(range(9), repeat=3):
        if (i,j,k) in seen: continue
        orb=set(); t=(i,j,k)
        while t not in orb:
            orb.add(t); t=(t[1],t[2],t[0])
        reps.append(min(orb)); seen |= orb
    reps.sort(); return reps


def build_T333():
    T=[[[0]*9 for _ in range(9)] for _ in range(9)]
    for a,b,c in itertools.product(range(3), repeat=3):
        T[3*a+b][3*b+c][3*c+a] ^= 1
    return T


class CMSEncoder:
    def __init__(self):
        self.nv=0; self.reg=[]; self.xors=[]
        self.lin_cache={}
    def new_var(self):
        self.nv+=1; return self.nv
    def new_vars(self,n): return [self.new_var() for _ in range(n)]
    def _cl(self,*lits): self.reg.append(tuple(lits))
    def add_xor(self, terms, target):
        terms=list(dict.fromkeys([t for t in terms if t != 0]))
        # If a variable appears twice it cancels; dict.fromkeys is not enough for repeated terms.
        # This method is used after lin_var cancellation, and top-level product vars are distinct.
        self.xors.append((target&1, terms))
    def xor_terms(self, terms, target=0):
        # cancel repeated variables over F2
        parity={}
        for t in terms:
            if t==0: continue
            parity[t]=parity.get(t,0)^1
        terms=[t for t,b in sorted(parity.items()) if b]
        self.xors.append((target&1, terms))
    def lin_var(self, terms):
        # linear XOR of positive variables, no constant
        parity={}
        for t in terms:
            if t==0: continue
            parity[t]=parity.get(t,0)^1
        terms=tuple(t for t,b in sorted(parity.items()) if b)
        if not terms:
            return 0
        if len(terms)==1:
            return terms[0]
        if terms in self.lin_cache:
            return self.lin_cache[terms]
        y=self.new_var(); self.lin_cache[terms]=y
        self.xor_terms([y]+list(terms), 0)
        return y
    def AND2(self,a,b):
        if a==0 or b==0: return 0
        if a==b: return a
        p=self.new_var()
        self._cl(-a,-b,p); self._cl(a,-p); self._cl(b,-p)
        return p
    def AND3(self,a,b,c):
        if a==0 or b==0 or c==0: return 0
        if a==b==c: return a
        return self.AND2(self.AND2(a,b),c)
    def add_lex_le(self,a,b):
        # a,b contain positive variables or zero constants.  Handle constants by materializing if needed.
        n=len(a); eq=None
        def lit_zero_var(val):
            if val!=0: return val
            z=self.new_var(); self._cl(-z); return z
        a=[lit_zero_var(x) for x in a]; b=[lit_zero_var(x) for x in b]
        for j in range(n):
            if eq is None: self._cl(-a[j], b[j])
            else: self._cl(-eq, -a[j], b[j])
            if j<n-1:
                eq_j=self.new_var()
                if eq is None:
                    self._cl(-eq_j, -a[j], b[j]); self._cl(-eq_j, a[j], -b[j])
                    self._cl(-a[j], -b[j], eq_j); self._cl(a[j], b[j], eq_j)
                else:
                    self._cl(-eq_j, eq); self._cl(-eq_j, -a[j], b[j]); self._cl(-eq_j, a[j], -b[j])
                    self._cl(-eq, -a[j], -b[j], eq_j); self._cl(-eq, a[j], b[j], eq_j)
                eq=eq_j
    def write(self,path):
        clauses=len(self.reg)+len(self.xors)
        with open(path,'w') as f:
            f.write(f'p cnf {self.nv} {clauses}\n')
            for cl in self.reg:
                f.write(' '.join(map(str,cl))+' 0\n')
            for target,terms in self.xors:
                terms=list(terms)
                if not terms:
                    if target: f.write('0\n')
                    continue
                lits=terms[:]
                # CryptoMiniSat XOR clauses are equations XOR(literals)=1.
                # If target is 0, negate one literal so (not x1) xor x2 ... = 1 <=> x1 xor x2 ... = 0.
                if target==0:
                    lits[0] = -lits[0]
                f.write('x '+' '.join(map(str,lits))+' 0\n')


def transform_exprs(Gpow, vec):
    # vec is list of 9 encoder variable ids/0 constants; return Gpow*vec linear expressions as lists of ids
    out=[]
    for i in range(9):
        terms=[]
        for j in range(9):
            if Gpow[i][j] and vec[j]!=0:
                terms.append(vec[j])
        out.append(terms)
    return out


def realize_transform(enc, Gpow, vec):
    return [enc.lin_var(terms) for terms in transform_exprs(Gpow, vec)]


def param_vec(enc, basis, prefix):
    params=enc.new_vars(len(basis))
    coords=[]
    for i in range(9):
        coords.append(enc.lin_var([params[j] for j,b in enumerate(basis) if b[i]&1]))
    return coords, params


def encode(pattern, sym_break=True, require_nonzero=False):
    T=build_T333(); reps=cyclic_orbit_reps()
    # BILR a0 modulo 2: [[0,0,-1],[1,0,-1],[0,1,-1]]
    A=[[0,0,1],[1,0,1],[0,1,1]]
    G=conj_matrix_mod2(A)
    Gp=[eye(9)]
    for _ in range(3): Gp.append(matmul2(Gp[-1],G))
    assert Gp[4-0-1]  # placate lint
    assert matmul2(Gp[3],G)==eye(9)
    G2=Gp[2]
    fix1=nullspace2(add2(G,eye(9)))
    fix2=nullspace2(add2(G2,eye(9)))

    enc=CMSEncoder()
    # one base free triple; inner orbit k=0..3 and outer cyclic give m=4 free orbits, 12 terms
    Avars=enc.new_vars(9); Bvars=enc.new_vars(9); Cvars=enc.new_vars(9)
    free_terms=[]
    for k in range(4):
        Ak=realize_transform(enc,Gp[k],Avars)
        Bk=realize_transform(enc,Gp[k],Bvars)
        Ck=realize_transform(enc,Gp[k],Cvars)
        free_terms.append((Ak,Bk,Ck))
        free_terms.append((Bk,Ck,Ak))
        free_terms.append((Ck,Ak,Bk))

    cube_terms=[]; cube_param_dims=[]
    # group equal lengths for optional lex among representatives of same type
    reps_by_len={1:[],2:[],4:[]}
    for idx,d in enumerate(pattern):
        if d==1:
            v,params=param_vec(enc,fix1,f'c{idx}')
            cube_param_dims.append(len(params)); reps_by_len[1].append(v)
            cube_terms.append(v)
        elif d==2:
            v,params=param_vec(enc,fix2,f'c{idx}')
            cube_param_dims.append(len(params)); reps_by_len[2].append(v)
            cube_terms.append(v)
            cube_terms.append(realize_transform(enc,G,v))
        elif d==4:
            v=enc.new_vars(9); cube_param_dims.append(9); reps_by_len[4].append(v)
            for k in range(4): cube_terms.append(realize_transform(enc,Gp[k],v))
        else:
            raise ValueError(pattern)
    assert len(cube_terms)==sum(pattern), (len(cube_terms), pattern)

    if sym_break:
        # lex order representatives inside same orbit-size class. Do not order transformed orbit terms.
        for d,vecs in reps_by_len.items():
            for i in range(len(vecs)-1): enc.add_lex_le(vecs[i],vecs[i+1])
        # Nonzero orbit representatives are useful for exact-pattern probes, but must be OFF
        # when an UNSAT result is meant to exclude <=10 cube slots (lower-rank padding by zeros).
        if require_nonzero:
            for d,vecs in reps_by_len.items():
                for v in vecs:
                    nz=[x for x in v if x!=0]
                    if nz: enc._cl(*nz)
            enc._cl(*Avars); enc._cl(*Bvars); enc._cl(*Cvars)

    for (i,j,k) in reps:
        terms=[]
        for u in cube_terms:
            p=enc.AND3(u[i],u[j],u[k])
            if p: terms.append(p)
        for U,V,W in free_terms:
            p=enc.AND3(U[i],V[j],W[k])
            if p: terms.append(p)
        enc.xor_terms(terms, T[i][j][k])

    vmap={'A':Avars,'B':Bvars,'C':Cvars,'pattern':pattern,'G':G,'fix1_basis':fix1,'fix2_basis':fix2,
          'cube_param_dims':cube_param_dims,'cube_terms':cube_terms,'free_terms':free_terms}
    return enc,vmap


def run_cms(path, timeout):
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


def eval_lin(assign, terms):
    z=0
    for t in terms:
        z ^= int(assign.get(t,False))
    return z


def verify_from_assign(assign, enc, pattern):
    # Reconstruct by re-encoding with stable variable allocation; use variable ids in returned expressions.
    # Simpler: evaluate the top-level tensor directly from decoded A/B/C and cube reps using vmap is omitted here.
    # This function is not used for UNSAT evidence; SAT records include assignment and are checked by a separate direct path below.
    return None


def eval_vec(assign, vec_expr):
    return [int(assign.get(x, False)) if x != 0 else 0 for x in vec_expr]


def direct_verify_record(assign, pattern, require_nonzero=False):
    # Rebuild the same expression numerically from the SAT assignment and verify all 729 Brent equations.
    enc,vmap=encode(pattern, sym_break=True, require_nonzero=require_nonzero)
    # Note: variable numbering is deterministic, so assignment from the solved CNF matches this encoding.
    T=build_T333()
    cube_vecs=[eval_vec(assign,u) for u in vmap['cube_terms']]
    free=[tuple(eval_vec(assign,x) for x in triple) for triple in vmap['free_terms']]

    brent_errors=[]
    for i,j,k in itertools.product(range(9), repeat=3):
        val=0
        for u in cube_vecs:
            val ^= (u[i] & u[j] & u[k])
        for U,V,W in free:
            val ^= (U[i] & V[j] & W[k])
        if val != T[i][j][k]:
            brent_errors.append((i,j,k,val,T[i][j][k]))

    xor_bad=0
    for target,terms in enc.xors:
        lhs=0
        for t in terms:
            lhs ^= int(assign.get(t,False))
        if lhs != target:
            xor_bad += 1

    missing_vars=[v for v in range(1,enc.nv+1) if v not in assign]
    return {'brent_errors':len(brent_errors),'brent_error_examples':brent_errors[:5],
            'xor_equation_mismatches':xor_bad,'assigned_vars':len(assign),'encoder_vars':enc.nv,
            'missing_encoder_vars':len(missing_vars),'missing_encoder_var_examples':missing_vars[:10],
            'A':eval_vec(assign,vmap['A']),'B':eval_vec(assign,vmap['B']),'C':eval_vec(assign,vmap['C']),
            'cube_vecs':cube_vecs,'free_terms':free}


def parse_patterns(s):
    if s=='selected':
        return [[4,4,2],[4,4,1,1],[4,2,2,1,1]]
    def partitions(total):
        out=[]
        def rec(rem,last,cur):
            if rem==0:
                out.append(cur[:]); return
            for d in [4,2,1]:
                if d<=rem and d<=last:
                    cur.append(d); rec(rem-d,d,cur); cur.pop()
        rec(total,4,[]); return out
    if s=='all':
        return partitions(10)
    if s=='upto10':
        out=[]
        for total in range(0,11):
            if total==0: out.append([])
            else: out.extend(partitions(total))
        return out
    out=[]
    for part in s.split(';'):
        if part.strip(): out.append([int(x) for x in part.split(',')])
    return out


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--patterns',default='selected',help="selected | all | semicolon-separated e.g. '4,4,2;4,4,1,1'")
    ap.add_argument('--timeout',type=int,default=600)
    ap.add_argument('--no-sym-break',action='store_true')
    ap.add_argument('--require-nonzero',action='store_true',
                    help='for exact-pattern probes require each cube orbit representative and A,B,C nonzero; do not use for <=rank exclusions')
    args=ap.parse_args()
    OUT.mkdir(parents=True,exist_ok=True)
    patterns=parse_patterns(args.patterns)
    mode='nonzero' if args.require_nonzero else 'padded'
    print('Z4 x cyclic F2 SAT patterns',patterns,'mode',mode)
    results=[]
    for pat in patterns:
        tag='p'+'_'.join(map(str,pat)) if pat else 'p0'
        filetag=f'{mode}_{tag}'
        t0=time.time(); enc,vmap=encode(pat, sym_break=not args.no_sym_break, require_nonzero=args.require_nonzero); enc_sec=time.time()-t0
        cnf=OUT/f'z4_cyclic_{filetag}.cnf'; enc.write(cnf)
        print(f'\n{tag}: pattern={pat} vars={enc.nv} reg={len(enc.reg)} xor={len(enc.xors)} lin_cache={len(enc.lin_cache)} enc={enc_sec:.2f}s')
        status,assign,sec,stdout,stderr=run_cms(cnf,args.timeout)
        print(f'{tag}: {status} {sec:.2f}s')
        rec={'pattern':pat,'tag':tag,'vars':enc.nv,'regular_clauses':len(enc.reg),'xor_clauses':len(enc.xors),
             'linear_aux_vars':len(enc.lin_cache),'encode_sec':round(enc_sec,3),'status':status,'solve_sec':round(sec,3),
             'cnf':str(cnf)}
        if status=='SAT':
            chk=direct_verify_record(assign,pat,require_nonzero=args.require_nonzero)
            rec['check']=chk
            # Save a compact positive witness. A full reconstruction script can replay variable ids deterministically.
            rec['true_vars']=[v for v,b in sorted(assign.items()) if b][:2000]
            print('  check',chk)
        if stdout.strip(): rec['solver_stdout_tail']=stdout[-1000:]
        if stderr.strip(): rec['solver_stderr_tail']=stderr[-1000:]
        results.append(rec)
        (OUT/f'z4_cyclic_f2_results_{mode}_partial.json').write_text(json.dumps({'results':results},indent=2)+'\n')
    out=OUT/f'z4_cyclic_f2_results_{mode}.json'
    out.write_text(json.dumps({'field':'F2','inner_action':'conjugation by BILR a0 modulo 2','patterns_tested':patterns,
                               'require_nonzero':args.require_nonzero,'sym_break':not args.no_sym_break,
                               'results':results},indent=2)+'\n')
    print('\nSaved',out)

if __name__=='__main__':
    main()
