#!/usr/bin/env python3
"""Corrected Kuranishi variety analysis with proper factor-of-2.

Finds the solution space of the quadratic system and characterizes
unobstructed deformation directions.
"""
import numpy as np, json
from pathlib import Path
from scipy.optimize import minimize

def parse_qmm(path):
    dims=None;rank=None;terms=[]
    cur=None
    for raw in Path(path).read_text().splitlines():
        line=raw.strip()
        if not line or line.startswith('#'): continue
        p=line.split()
        if p[0]=='dimensions': dims=tuple(map(int,p[1:4]))
        elif p[0]=='rank': rank=int(p[1])
        elif p[0]=='term':
            if cur: terms.append(cur)
            cur={'index':int(p[1])}
        elif p[0] in ('u','v','w'): cur[p[0]]=[int(x) for x in p[1:]]
    if cur: terms.append(cur)
    return {'dimensions':dims,'rank':rank,'terms':terms}

def build_all(scheme_path):
    S=parse_qmm(scheme_path); terms=S['terms']; r=S['rank']; n=9
    J=np.zeros((729,27*r))
    for i,t in enumerate(terms):
        u,v,w=[np.array(t[k],dtype=float) for k in 'uvw']
        for a in range(9):
            for b in range(9):
                for c in range(9):
                    row=a*81+b*9+c
                    J[row,27*i+a]+=v[b]*w[c]; J[row,27*i+9+b]+=u[a]*w[c]; J[row,27*i+18+c]+=u[a]*v[b]
    U_j,S_j,Vt_j=np.linalg.svd(J,full_matrices=True)
    jrank=int(np.sum(S_j>1e-10))
    kernel=Vt_j[jrank:].T; left_null=U_j[:,jrank:]
    # Symmetry
    sym_vecs=[]
    for i,t in enumerate(terms):
        u,v,w=[np.array(t[k],dtype=float) for k in 'uvw']
        d1=np.zeros(27*r);d1[27*i:27*i+9]=u;d1[27*i+18:27*i+27]=-w
        d2=np.zeros(27*r);d2[27*i+9:27*i+18]=v;d2[27*i+18:27*i+27]=-w
        sym_vecs.extend([d1,d2])
    for jj in range(3):
        for kk in range(3):
            E=np.zeros((3,3));E[jj,kk]=1.0
            for gt in range(3):
                sv=np.zeros(27*r)
                for i,t in enumerate(terms):
                    U=np.array(t['u']).reshape(3,3).astype(float)
                    V=np.array(t['v']).reshape(3,3).astype(float)
                    W=np.array(t['w']).reshape(3,3).astype(float)
                    if gt==0: sv[27*i:27*i+9]+=(E@U).flatten();sv[27*i+18:27*i+27]+=(E@W).flatten()
                    elif gt==1: sv[27*i:27*i+9]+=-(U@E).flatten();sv[27*i+9:27*i+18]+=(E@V).flatten()
                    else: sv[27*i+9:27*i+18]+=-(V@E).flatten();sv[27*i+18:27*i+27]+=-(W@E).flatten()
                sym_vecs.append(sv)
    sym_vecs=np.array(sym_vecs)
    sym_proj=kernel.T@sym_vecs.T
    sym_rank=int(np.linalg.matrix_rank(sym_proj,tol=1e-10))
    res_dim=kernel.shape[1]-sym_rank
    U_c,_,_=np.linalg.svd(sym_proj,full_matrices=True)
    res_dirs=kernel@U_c[:,sym_rank:]
    return terms, r, jrank, kernel, left_null, res_dirs, res_dim

def Q_bilinear(terms, d1, d2):
    Qv=np.zeros(729)
    for i,t in enumerate(terms):
        u,v,w=[np.array(t[k],dtype=float) for k in 'uvw']
        du1,dv1,dw1=d1[27*i:27*i+9],d1[27*i+9:27*i+18],d1[27*i+18:27*i+27]
        du2,dv2,dw2=d2[27*i:27*i+9],d2[27*i+9:27*i+18],d2[27*i+18:27*i+27]
        for a in range(9):
            for b in range(9):
                for c in range(9):
                    idx=a*81+b*9+c
                    Qv[idx]+=0.5*(du1[a]*dv2[b]*w[c]+du2[a]*dv1[b]*w[c])
                    Qv[idx]+=0.5*(du1[a]*v[b]*dw2[c]+du2[a]*v[b]*dw1[c])
                    Qv[idx]+=0.5*(u[a]*dv1[b]*dw2[c]+u[a]*dv2[b]*dw1[c])
    return Qv

def main():
    scheme='data/cn122_r23_reproduce/scheme.qmm'
    terms, r, jrank, kernel, left_null, res_dirs, m = build_all(scheme)
    coker=left_null.shape[1]
    print(f'J rank={jrank}, ker={kernel.shape[1]}, coker={coker}, residual={m}')
    
    # Build G[ell,j,k]
    print('Computing Kuranishi bilinear form G...')
    G=np.zeros((coker,m,m))
    for j in range(m):
        for k in range(j,m):
            Qjk=Q_bilinear(terms,res_dirs[:,j],res_dirs[:,k])
            proj=left_null.T@Qjk; G[:,j,k]=proj; G[:,k,j]=proj
    
    # Effective equations
    G_flat=G.reshape(coker,m*m)
    U_G,S_G,_=np.linalg.svd(G_flat,full_matrices=False)
    eff_eqs=int(np.sum(S_G>1e-10))
    print(f'Effective quadratic equations: {eff_eqs} in {m} variables')
    
    # Reduced system H[i,j,k]
    H=np.zeros((eff_eqs,m,m))
    for i in range(eff_eqs):
        H[i]=np.einsum('l,ljk->jk',U_G[:,i],G)
    
    # Multi-start search
    def loss_H(x):
        vals=np.einsum('ijk,j,k->i',H,x,x)
        return 0.5*np.sum(vals**2)
    def grad_H(x):
        vals=np.einsum('ijk,j,k->i',H,x,x)
        dfdx=2*np.einsum('isk,k->is',H,x)
        return dfdx.T@vals
    
    solutions=[]
    for trial in range(1000):
        np.random.seed(trial*31+7)
        x0=np.random.randn(m);x0/=np.linalg.norm(x0)
        res=minimize(loss_H,x0,jac=grad_H,method='L-BFGS-B',
                     options={'maxiter':3000,'ftol':1e-30,'gtol':1e-20})
        if res.fun<1e-20:
            x_sol=res.x/np.linalg.norm(res.x)
            is_new=True
            for prev in solutions:
                if abs(np.dot(x_sol,prev))>0.999 or abs(np.dot(x_sol,-prev))>0.999: 
                    is_new=False; break
            if is_new: solutions.append(x_sol)
    
    print(f'\nFound {len(solutions)} distinct unobstructed directions')
    
    if len(solutions)>0:
        x0=solutions[0]
        Jac_f=2*np.einsum('ijk,k->ij',H,x0)
        jac_rank=int(np.linalg.matrix_rank(Jac_f,tol=1e-10))
        local_dim=m-jac_rank
        print(f'Local Jacobian rank at solution: {jac_rank}/{eff_eqs}')
        print(f'Local solution variety dim: >= {local_dim}')
        
        print('\nVerification (first 10):')
        for idx,x_sol in enumerate(solutions[:10]):
            d=res_dirs@x_sol
            Q_dd=Q_bilinear(terms,d,d)*2  # ×2 because Q_bilinear is symmetrized
            proj_coker=left_null.T@Q_dd
            norm_proj=np.linalg.norm(proj_coker)
            norm_Q=np.linalg.norm(Q_dd)
            rel=norm_proj/max(norm_Q,1e-15)
            print(f'  sol {idx}: |Q|={norm_Q:.4e} |proj/coker|={norm_proj:.4e} rel={rel:.2e}')
    
    results={
        'scheme':'cn122','residual_dim':m,'effective_equations':eff_eqs,
        'n_unobstructed_found':len(solutions),
        'local_solution_dim':int(local_dim) if solutions else None,
    }
    print(f'\n{json.dumps(results,indent=2)}')
    Path('data/cn122_r23_reproduce/corrected_obstruction.json').write_text(
        json.dumps(results,indent=2)+'\n')

if __name__=='__main__':
    main()
