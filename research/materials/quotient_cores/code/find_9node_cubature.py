#!/usr/bin/env python3
"""Try to construct an explicit 9-node rational trace-moment cubature certificate."""
import json, itertools
from pathlib import Path
import sympy as sp

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'moment_cubature'
OUT.mkdir(parents=True, exist_ok=True)

off=[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]
G=sp.zeros(8,8)
for a,(i,j) in enumerate(off):
    for b,(k,l) in enumerate(off):
        G[a,b]=1 if j==k and i==l else 0
G[6,6]=2; G[6,7]=-1; G[7,6]=-1; G[7,7]=2
weights=[sp.Integer(1)]*6+[sp.Integer(-1)]*3
W=sp.diag(*weights)
wvec=sp.Matrix(weights)
H=[]
for i in range(8):
    y=[sp.Integer(0)]*9
    y[i]=1
    y[8]=weights[i]
    H.append(sp.Matrix(y))
H=sp.Matrix.hstack(*H)
GH=H.T*W*H
assert wvec.T*H == sp.zeros(1,8)
assert GH.det()==G.det()==-3

def diagonalize(A):
    A=sp.Matrix(A); n=A.rows; bil=lambda x,y: sp.factor((x.T*A*y)[0])
    sub=[sp.eye(n).col(i) for i in range(n)]
    out=[]; diag=[]
    while sub:
        chosen=None
        for v in sub:
            if bil(v,v)!=0:
                chosen=sp.Matrix(v); break
        if chosen is None:
            for i in range(len(sub)):
                for j in range(i+1,len(sub)):
                    if bil(sub[i],sub[j])!=0:
                        chosen=sub[i]+sub[j]; break
                if chosen is not None: break
        if chosen is None: raise RuntimeError('no nonisotropic vector')
        d=bil(chosen,chosen); out.append(chosen); diag.append(d)
        B=sp.Matrix.hstack(*sub)
        row=sp.Matrix([[bil(chosen,sub[j]) for j in range(len(sub))]])
        sub=[B*z for z in row.nullspace()]
    T=sp.Matrix.hstack(*out)
    D=T.T*A*T
    return T,D

TG,DG=diagonalize(G)
target=[sp.factor(DG[i,i]) for i in range(8)]

def find_vec(A, basis, d, max_bound=5):
    B=sp.Matrix.hstack(*basis)
    Gram=B.T*A*B
    k=len(basis)
    # try sparse +/- single and pair combos before full product
    for i in range(k):
        for c in range(-max_bound,max_bound+1):
            if c==0: continue
            vec=[0]*k; vec[i]=c; cv=sp.Matrix(vec)
            if (cv.T*Gram*cv)[0]==d: return B*cv, tuple(vec)
    for i in range(k):
        for j in range(i+1,k):
            for ci in range(-max_bound,max_bound+1):
                for cj in range(-max_bound,max_bound+1):
                    if ci==0 and cj==0: continue
                    vec=[0]*k; vec[i]=ci; vec[j]=cj; cv=sp.Matrix(vec)
                    if (cv.T*Gram*cv)[0]==d: return B*cv, tuple(vec)
    for bound in range(1,max_bound+1):
        vals=range(-bound,bound+1)
        count=0
        for coeff in itertools.product(vals, repeat=k):
            if all(c==0 for c in coeff): continue
            if max(abs(c) for c in coeff)!=bound: continue
            cv=sp.Matrix(coeff)
            if (cv.T*Gram*cv)[0]==d:
                return B*cv, tuple(coeff)
            count+=1
    return None,None

A=GH
bil=lambda x,y: sp.factor((x.T*A*y)[0])
sub=[sp.eye(8).col(i) for i in range(8)]
out=[]; coeffs=[]; success=True
for idx,d in enumerate(target):
    v,c=find_vec(A,sub,d,max_bound=4)
    if v is None:
        success=False; break
    out.append(v); coeffs.append(c)
    B=sp.Matrix.hstack(*sub)
    row=sp.Matrix([[bil(v,sub[j]) for j in range(len(sub))]])
    sub=[B*z for z in row.nullspace()]

result={'success':success,'target_diag':[str(x) for x in target], 'coeffs':[list(map(str,c)) for c in coeffs]}
if success:
    TH=sp.Matrix.hstack(*out)
    assert TH.T*GH*TH == DG
    C=TH*TG.inv()
    assert C.T*GH*C == G
    B9=H*C
    assert wvec.T*B9 == sp.zeros(1,8)
    assert B9.T*W*B9 == G
    result.update({
        'weights':[int(w) for w in weights],
        'mu_rows':[[str(sp.factor(B9[i,j])) for j in range(8)] for i in range(9)],
        'sum_w':str(sum(weights)),
        'rank':int(B9.rank()),
        'check_linear_zero': bool(wvec.T*B9 == sp.zeros(1,8)),
        'check_quadratic_K': bool(B9.T*W*B9 == G),
    })
else:
    result['failed_at']=len(out)

out_path=OUT/'nine_node_moment_cubature_search.json'
with open(out_path,'w') as f: json.dump(result,f,indent=2)
print(json.dumps({'out':str(out_path),'success':success,'failed_at':result.get('failed_at'),'rank':result.get('rank')},indent=2))
