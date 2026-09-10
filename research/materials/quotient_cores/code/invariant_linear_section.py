#!/usr/bin/env python3
"""
analysis: exact finite-field linear-section solver for finite-symmetry exterior
rank-four ansaetze for the Cartan trivector omega in Lambda^3(sl_3).

The analysis Sage script was unnecessary for the abelian orbit ansatz.  If a finite
abelian group H acts on sl_3 and the four exterior planes form one H-orbit, then

    sum_{h in H} Lambda^3(Ad h)(s * p) = omega/3

is equivalent to prescribing the H-invariant Pluecker coordinates of the plane P
up to one common scale.  In an eigenbasis this is a linear section of G(3,8):
the invariant Pluecker coordinates of P must be proportional to those of omega.

This script does exact modular arithmetic, chooses Pluecker charts, uses all linear
relations first, and then brute-forces only the remaining small-dimensional system.
It is a search / positive-control instrument, not a characteristic-zero theorem.
"""
from __future__ import annotations
import argparse, itertools, json, math, time
from pathlib import Path

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "exterior_linear_sections"
OUT.mkdir(parents=True, exist_ok=True)

TRIPLES = list(itertools.combinations(range(8), 3))
TIDX = {t:i for i,t in enumerate(TRIPLES)}

# ---------------------------------------------------------------------------
# Small modular linear algebra

def inv_mod(a, p):
    a %= p
    if a == 0:
        raise ZeroDivisionError
    return pow(a, p-2, p)

def mat_zero(m,n): return [[0]*n for _ in range(m)]
def mat_eye(n):
    A = mat_zero(n,n)
    for i in range(n): A[i][i]=1
    return A

def mat_mul(A,B,p):
    m=len(A); k=len(A[0]); n=len(B[0])
    C=mat_zero(m,n)
    for i in range(m):
        Ai=A[i]
        for a in range(k):
            if Ai[a] % p:
                ca=Ai[a]%p; Ba=B[a]
                for j in range(n): C[i][j]=(C[i][j]+ca*Ba[j])%p
    return C

def mat_vec(A,x,p):
    return [sum((A[i][j]%p)*(x[j]%p) for j in range(len(x)))%p for i in range(len(A))]

def mat_trans(A): return [list(row) for row in zip(*A)]

def mat_pow(A,e,p):
    R=mat_eye(len(A)); B=[row[:] for row in A]
    while e:
        if e&1: R=mat_mul(R,B,p)
        B=mat_mul(B,B,p); e//=2
    return R

def rref_mod(A, p):
    A=[[(x%p) for x in row] for row in A]
    m=len(A); n=len(A[0]) if m else 0
    piv=[]; r=0
    for c in range(n):
        pivrow=None
        for i in range(r,m):
            if A[i][c]%p:
                pivrow=i; break
        if pivrow is None: continue
        A[r],A[pivrow]=A[pivrow],A[r]
        iv=inv_mod(A[r][c],p)
        A[r]=[(x*iv)%p for x in A[r]]
        for i in range(m):
            if i!=r and A[i][c]%p:
                f=A[i][c]%p
                A[i]=[(A[i][j]-f*A[r][j])%p for j in range(n)]
        piv.append(c); r+=1
        if r==m: break
    return A,piv

def rank_mod(A,p): return len(rref_mod(A,p)[1])

def nullspace_mod(A,p):
    if not A: return []
    R,piv=rref_mod(A,p)
    m=len(R); n=len(R[0])
    pivset=set(piv)
    free=[j for j in range(n) if j not in pivset]
    basis=[]
    for f in free:
        x=[0]*n; x[f]=1
        for row,c in enumerate(piv):
            x[c]=(-R[row][f])%p
        basis.append(x)
    return basis

def solve_square(A,b,p):
    n=len(A)
    Aug=[A[i][:]+[b[i]%p] for i in range(n)]
    R,piv=rref_mod(Aug,p)
    if len(piv)<n or any(c>=n for c in piv[:n]):
        raise ValueError("singular square solve")
    return [R[i][n]%p for i in range(n)]

def mat_inv(A,p):
    n=len(A)
    Aug=[A[i][:]+[1 if i==j else 0 for j in range(n)] for i in range(n)]
    R,piv=rref_mod(Aug,p)
    if piv[:n] != list(range(n)):
        raise ValueError("singular inverse")
    return [row[n:] for row in R]

# ---------------------------------------------------------------------------
# sl3 and exterior linear algebra

def m3(A): return [[x for x in A[0:3]],[x for x in A[3:6]],[x for x in A[6:9]]]
def m3_flat(M): return [M[i][j] for i in range(3) for j in range(3)]
def m3_mul(A,B,p):
    return [[sum(A[i][k]*B[k][j] for k in range(3))%p for j in range(3)] for i in range(3)]
def m3_inv(A,p):
    return m3(mat_inv([row[:] for row in A],p)[0]+mat_inv([row[:] for row in A],p)[1]+mat_inv([row[:] for row in A],p)[2])

def sl3_basis_mats(p):
    mats=[]
    for i,j in [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]:
        M=[[0]*3 for _ in range(3)]; M[i][j]=1; mats.append(M)
    mats.append([[1%p,0,0],[0,(-1)%p,0],[0,0,0]])
    mats.append([[0,0,0],[0,1%p,0],[0,0,(-1)%p]])
    return mats

def sl_coords(M,p):
    # basis E01,E02,E10,E12,E20,E21,H0=E00-E11,H1=E11-E22
    tr=(M[0][0]+M[1][1]+M[2][2])%p
    assert tr == 0
    return [M[0][1]%p,M[0][2]%p,M[1][0]%p,M[1][2]%p,M[2][0]%p,M[2][1]%p,M[0][0]%p,(-M[2][2])%p]

def ad_matrix(g,p):
    gi=m3(mat_inv(g,p)[0]+mat_inv(g,p)[1]+mat_inv(g,p)[2])
    cols=[]
    for E in sl3_basis_mats(p):
        cols.append(sl_coords(m3_mul(m3_mul(g,E,p),gi,p),p))
    # columns are images in old basis
    return mat_trans(cols)

def det3_num(cols, rows, p):
    a,b,c=rows
    M=[[cols[0][a],cols[1][a],cols[2][a]], [cols[0][b],cols[1][b],cols[2][b]], [cols[0][c],cols[1][c],cols[2][c]]]
    val=(M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])
         -M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
         +M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))
    return val%p

def wedge3_cols(cols,p):
    return [det3_num(cols,t,p) for t in TRIPLES]

def lambda3_matrix(E,p):
    cols=[]
    # E is old-coords rows x new-coords cols.
    Ecols=[[E[i][j]%p for i in range(8)] for j in range(8)]
    for tri in TRIPLES:
        cols.append(wedge3_cols([Ecols[tri[0]],Ecols[tri[1]],Ecols[tri[2]]],p))
    return mat_trans(cols)  # old wedge coords = L * new wedge coords

def target_old(p):
    v=[0]*56
    for t,c in { (0,2,6):1, (0,3,4):1, (1,2,5):-1, (1,4,6):1, (1,4,7):1, (3,5,7):1}.items():
        v[TIDX[t]]=c%p
    return v

def simultaneous_eigenbasis(gens, family, p):
    # Return E whose columns are old-basis eigenvectors, and character labels.
    if family.startswith('c4'):
        ii=None
        for a in range(1,p):
            if (a*a+1)%p==0: ii=a; break
        if ii is None: raise ValueError("need p=1 mod 4 for C4 eigenbasis")
        lambdas=[1%p,ii%p,(-1)%p,(-ii)%p]
        labels=[0,1,2,3]
        eig=[]; weights=[]
        A=gens[0]
        I=mat_eye(8)
        for lab,lam in zip(labels,lambdas):
            M=[[(A[i][j] - (lam if i==j else 0))%p for j in range(8)] for i in range(8)]
            ns=nullspace_mod(M,p)
            for v in ns:
                eig.append(v); weights.append(lab)
        E=mat_trans(eig)
        if rank_mod(E,p)!=8: raise ValueError(f"C4 eigenbasis rank {rank_mod(E,p)}")
        return E, weights
    if family=='klein_diag':
        lambdas=[1%p,(-1)%p]
        eig=[]; weights=[]
        I=mat_eye(8)
        for lam1 in lambdas:
            for lam2 in lambdas:
                rows=[]
                for A,lam in [(gens[0],lam1),(gens[1],lam2)]:
                    rows.extend([[(A[i][j] - (lam if i==j else 0))%p for j in range(8)] for i in range(8)])
                ns=nullspace_mod(rows,p)
                for v in ns:
                    eig.append(v); weights.append((0 if lam1==1%p else 1, 0 if lam2==1%p else 1))
        E=mat_trans(eig)
        if rank_mod(E,p)!=8: raise ValueError(f"Klein eigenbasis rank {rank_mod(E,p)}")
        return E, weights
    raise ValueError(family)

def invariant_triples(weights, family):
    inv=[]
    for t in TRIPLES:
        if family.startswith('c4'):
            ok=(sum(weights[i] for i in t)%4)==0
        else:
            ok=((sum(weights[i][0] for i in t)%2)==0 and (sum(weights[i][1] for i in t)%2)==0)
        if ok: inv.append(t)
    return inv

def group_ad_generators(family,p):
    if family=='c4_regular':
        g=[[0,0,(-1)%p],[1,0,(-1)%p],[0,1,(-1)%p]]
        return [ad_matrix(g,p)], [g]
    if family=='c4_2plus1':
        ii=None
        for a in range(1,p):
            if (a*a+1)%p==0: ii=a; break
        if ii is None: raise ValueError("need p=1 mod 4")
        g=[[1,0,0],[0,1,0],[0,0,ii]]
        return [ad_matrix(g,p)], [g]
    if family=='klein_diag':
        g1=[[(-1)%p,0,0],[0,1,0],[0,0,1]]
        g2=[[1,0,0],[0,(-1)%p,0],[0,0,1]]
        return [ad_matrix(g1,p),ad_matrix(g2,p)], [g1,g2]
    raise ValueError(family)

# ---------------------------------------------------------------------------
# Sparse polynomial arithmetic over F_p, used only up to degree 3.

def poly_trim(A,p): return {m:c%p for m,c in A.items() if c%p}
def poly_const(c,n,p): return {tuple([0]*n): c%p} if c%p else {}
def poly_var(i,n):
    e=[0]*n; e[i]=1; return {tuple(e):1}
def poly_add(A,B,p):
    C=A.copy()
    for m,c in B.items(): C[m]=(C.get(m,0)+c)%p
    return poly_trim(C,p)
def poly_neg(A,p): return {m:(-c)%p for m,c in A.items() if c%p}
def poly_sub(A,B,p): return poly_add(A,poly_neg(B,p),p)
def poly_mul(A,B,p):
    if not A or not B: return {}
    C={}
    for ma,ca in A.items():
        for mb,cb in B.items():
            m=tuple(x+y for x,y in zip(ma,mb))
            C[m]=(C.get(m,0)+ca*cb)%p
    return poly_trim(C,p)
def poly_scalar(A,s,p): return {m:(c*s)%p for m,c in A.items() if (c*s)%p}
def poly_degree(A): return max((sum(m) for m in A), default=-1)
def poly_det3(M,p,n):
    # 3 x 3 matrix of polynomials
    term1=poly_mul(M[0][0], poly_sub(poly_mul(M[1][1],M[2][2],p), poly_mul(M[1][2],M[2][1],p), p), p)
    term2=poly_mul(M[0][1], poly_sub(poly_mul(M[1][0],M[2][2],p), poly_mul(M[1][2],M[2][0],p), p), p)
    term3=poly_mul(M[0][2], poly_sub(poly_mul(M[1][0],M[2][1],p), poly_mul(M[1][1],M[2][0],p), p), p)
    return poly_add(poly_sub(term1,term2,p),term3,p)

def chart_plucker_polys(pivot,p):
    n=15
    nonpiv=[j for j in range(8) if j not in pivot]
    var_index={(r,c): idx for idx,(c,r) in enumerate((c,r) for c in nonpiv for r in range(3))}
    B=[[{} for _ in range(8)] for __ in range(3)]
    for r,c in enumerate(pivot): B[r][c]=poly_const(1,n,p)
    for c in nonpiv:
        for r in range(3): B[r][c]=poly_var(var_index[(r,c)],n)
    polys=[]
    for tri in TRIPLES:
        M=[[B[r][c] for c in tri] for r in range(3)]
        polys.append(poly_det3(M,p,n))
    return polys, nonpiv

def linear_row(poly,n,p):
    # c0 + sum a_i x_i; return (coeffs, rhs) for sum a_i x_i = -c0, or None.
    if poly_degree(poly)>1: return None
    coeff=[0]*n; const=0
    for m,c in poly.items():
        d=sum(m)
        if d==0: const=(const+c)%p
        elif d==1:
            coeff[m.index(1)]=(coeff[m.index(1)]+c)%p
        else: return None
    return coeff, (-const)%p

def substitute_affine(poly, exprs, p):
    # exprs: old var -> polynomial in new variables.
    nnew=len(next(iter(exprs[0].keys()))) if exprs and exprs[0] else 0
    out={}
    for mon,c in poly.items():
        cur=poly_const(c,nnew,p)
        for i,e in enumerate(mon):
            for _ in range(e):
                cur=poly_mul(cur,exprs[i],p)
        out=poly_add(out,cur,p)
    return out

def solve_by_linear_then_bruteforce(equations,p,max_free=4,max_points=50):
    n=len(next(iter(equations[0].keys()))) if equations and equations[0] else 0
    # Iterate linear elimination because substitution can turn equations linear.
    history=[]
    eqs=[poly_trim(e,p) for e in equations if e]
    total_subs=[]
    current_n=n
    # We maintain equations only in current variables.
    while True:
        rows=[]
        for e in eqs:
            lr=linear_row(e,current_n,p)
            if lr is not None:
                rows.append(lr[0]+[lr[1]])
        if not rows:
            break
        R,piv=rref_mod(rows,p)
        # inconsistency: zero coeffs, nonzero rhs.
        inconsistent=False
        for row in R:
            if all(x%p==0 for x in row[:current_n]) and row[current_n]%p:
                inconsistent=True
        rank=len([c for c in piv if c<current_n])
        free=[j for j in range(current_n) if j not in set(c for c in piv if c<current_n)]
        history.append({'variables_before':current_n,'linear_rows':len(rows),'linear_rank':rank,'free_after_linear':len(free),'inconsistent':inconsistent})
        if inconsistent:
            return {'inconsistent':True,'history':history}
        if rank==0:
            break
        # Build expressions old vars -> new free vars.
        nfree=len(free)
        free_pos={old:i for i,old in enumerate(free)}
        exprs=[]
        pivot_rows={c:i for i,c in enumerate(piv) if c<current_n}
        for old in range(current_n):
            if old in free_pos:
                exprs.append(poly_var(free_pos[old],nfree))
            else:
                row=R[pivot_rows[old]]
                expr=poly_const(row[current_n],nfree,p)  # x_piv = rhs - sum row[f] x_f
                for oldf in free:
                    coef=(-row[oldf])%p
                    if coef:
                        expr=poly_add(expr,poly_scalar(poly_var(free_pos[oldf],nfree),coef,p),p)
                exprs.append(expr)
        neweqs=[]
        changed=False
        for e in eqs:
            se=substitute_affine(e,exprs,p)
            if se:
                neweqs.append(se)
            if se != e: changed=True
        eqs=neweqs
        current_n=nfree
        if not changed or rank==0:
            break
    degrees={}
    for e in eqs: degrees[poly_degree(e)]=degrees.get(poly_degree(e),0)+1
    rec={'inconsistent':False,'history':history,'remaining_variables':current_n,'remaining_equations':len(eqs),'remaining_degree_histogram':{str(k):v for k,v in sorted(degrees.items())}}
    if current_n <= max_free:
        pts=[]; count=0
        for vals in itertools.product(range(p), repeat=current_n):
            ok=True
            for e in eqs:
                s=0
                for mon,c in e.items():
                    term=c
                    for val,powr in zip(vals,mon):
                        if powr: term=(term*pow(val,powr,p))%p
                    s=(s+term)%p
                if s%p:
                    ok=False; break
            if ok:
                count+=1
                if len(pts)<max_points: pts.append(list(vals))
        rec['Fp_solution_count_after_elimination']=count
        rec['Fp_solution_examples_free_coords']=pts
    else:
        rec['bruteforce_skipped']='remaining variable count exceeds max_free'
    return rec

# ---------------------------------------------------------------------------
# Family experiments

def bilr_first_plane_old(p):
    # From analysis ballard_cyclic_analysis_v2, first free-orbit representative in old sl3 basis.
    return [[0,0,0,1,0,0,0,0], [0,0,0,0,(-1)%p,1,0,0], [0,0,0,(-1)%p,0,1,0,1]]

def transform_plane_to_new(old_cols,E_inv,p):
    return [mat_vec(E_inv,col,p) for col in old_cols]

def proportional_mismatches(pvec,tvec,inv_indices,p):
    # Find scale from first nonzero target coordinate with pvec nonzero if possible.
    scale=None
    for idx in inv_indices:
        if tvec[idx]%p and pvec[idx]%p:
            scale=(pvec[idx]*inv_mod(tvec[idx],p))%p
            break
    if scale is None:
        return None, len(inv_indices), []
    bad=[]
    for idx in inv_indices:
        if (pvec[idx]-scale*tvec[idx])%p:
            bad.append((TRIPLES[idx],pvec[idx]%p,tvec[idx]%p))
    return scale,len(bad),bad[:10]

def chart_score(pivot,inv_triples,target_new,pvec=None):
    # Number of invariant equations degree-1 in this pivot chart; a Pluecker coord is degree 3-|tri cap pivot|.
    invset=set(inv_triples)
    score=0
    nonzero_target = target_new[TIDX[pivot]] != 0
    if not nonzero_target:
        return (-999,0,False,False)
    p_nonzero=True if pvec is None else (pvec[TIDX[pivot]] != 0)
    for tri in inv_triples:
        if tri==pivot: continue
        deg=3-len(set(tri).intersection(pivot))
        if deg<=1: score+=1
    return (score, sum(1 for tri in inv_triples if tri!=pivot), nonzero_target, p_nonzero)

def run_family(family,p,max_charts,max_free):
    t0=time.time()
    gens3_ad, gens3 = group_ad_generators(family,p)
    E,weights=simultaneous_eigenbasis(gens3_ad,family,p)
    Einv=mat_inv(E,p)
    L=lambda3_matrix(E,p)
    target_new=solve_square(L,target_old(p),p)
    inv_tr=invariant_triples(weights,family)
    inv_idx=[TIDX[t] for t in inv_tr]
    noninv_nonzero=sum(1 for i,c in enumerate(target_new) if c%p and i not in set(inv_idx))
    target_inv_nonzero=sum(1 for i in inv_idx if target_new[i]%p)
    weight_counts={str(w):weights.count(w) for w in sorted(set(weights), key=str)}
    # Positive-control data only for c4_regular.
    bilr_check=None; pvec=None
    if family=='c4_regular':
        old=bilr_first_plane_old(p)
        new=transform_plane_to_new(old,Einv,p)
        pvec=wedge3_cols(new,p)
        scale,bad_count,bad=proportional_mismatches(pvec,target_new,inv_idx,p)
        bilr_check={'scale_p_over_target_on_invariants':scale,'mismatch_count':bad_count,'mismatch_examples':bad}
    # Pick target-nonzero pivots, requiring BILR nonzero for positive-control family.
    scored=[]
    for pivot in TRIPLES:
        sc,total,tnz,pnz=chart_score(pivot,inv_tr,target_new,pvec)
        if tnz and pnz:
            scored.append((sc,pivot))
    scored=sorted(scored, key=lambda x:(-x[0],x[1]))
    records=[]
    for sc,pivot in scored[:max_charts]:
        polys,nonpiv=chart_plucker_polys(pivot,p)
        tp=target_new[TIDX[pivot]]%p
        equations=[]
        for tri in inv_tr:
            idx=TIDX[tri]
            if tri==pivot: continue
            # target_pivot * p_tri - target_tri * p_pivot(=1) = 0 in this chart.
            eq=poly_sub(poly_scalar(polys[idx],tp,p), poly_const(target_new[idx]%p,15,p), p)
            if eq: equations.append(eq)
        # Do not constrain non-invariant Pluecker coordinates; they disappear under the orbit sum.
        rec={'pivot':list(pivot),'linear_degree1_equation_score':sc,'pivot_target':tp,'pivot_bilr_plucker':None if pvec is None else pvec[TIDX[pivot]]%p}
        rec.update(solve_by_linear_then_bruteforce(equations,p,max_free=max_free))
        records.append(rec)
    return {
        'family':family,'prime':p,'elapsed_sec':round(time.time()-t0,3),
        'weight_counts':weight_counts,
        'weights_in_eigenbasis': [str(w) for w in weights],
        'invariant_triple_count':len(inv_tr),
        'invariant_triples':[list(t) for t in inv_tr],
        'target_nonzero_in_noninvariant_coords':noninv_nonzero,
        'target_nonzero_in_invariant_coords':target_inv_nonzero,
        'target_invariant_coordinates': {str(TRIPLES[i]):target_new[i] for i in inv_idx if target_new[i]%p},
        'bilr_positive_control': bilr_check,
        'chart_records':records,
        'interpretation':'Exact modular linear-section computation for one-H-orbit exterior planes. Solutions/findings are finite-field model evidence; absence in selected charts is not a global characteristic-zero exclusion.'
    }

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--prime',type=int,default=5)
    ap.add_argument('--families',default='c4_regular,klein_diag,c4_2plus1')
    ap.add_argument('--max-charts',type=int,default=6)
    ap.add_argument('--max-free',type=int,default=4)
    ap.add_argument('--out',default=None)
    args=ap.parse_args()
    out={'prime':args.prime,'families':[], 'scope':'finite-symmetry exterior linear sections for the Cartan trivector'}
    for fam in [x.strip() for x in args.families.split(',') if x.strip()]:
        print(f'=== family {fam} over F_{args.prime} ===', flush=True)
        rec=run_family(fam,args.prime,args.max_charts,args.max_free)
        out['families'].append(rec)
        print(json.dumps({
            'family':fam,
            'weight_counts':rec['weight_counts'],
            'invariant_triple_count':rec['invariant_triple_count'],
            'target_noninv_nonzero':rec['target_nonzero_in_noninvariant_coords'],
            'bilr':rec['bilr_positive_control'],
            'charts':rec['chart_records'][:2],
        }, indent=2, sort_keys=True), flush=True)
    outpath=Path(args.out) if args.out else OUT / f'invariant_linear_sections_p{args.prime}.json'
    outpath.parent.mkdir(parents=True,exist_ok=True)
    outpath.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('SAVED',outpath)

if __name__=='__main__':
    main()
