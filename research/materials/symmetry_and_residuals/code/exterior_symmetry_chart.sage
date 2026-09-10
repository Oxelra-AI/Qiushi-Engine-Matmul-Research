# analysis: finite-symmetry exterior chart solver for the Cartan trivector
# Run with: sage -python? No, this is Sage syntax; use `sage file.sage --args ...`.
from sage.all import *
import itertools, json, time, argparse
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--prime', type=int, default=5)
parser.add_argument('--family', choices=['c4_regular','c4_2plus1','klein_diag'], default='c4_regular')
parser.add_argument('--charts', default='bilr', help='bilr, all, or comma-separated triple like 3,4,5')
parser.add_argument('--max-charts', type=int, default=56)
parser.add_argument('--out', default=None)
args = parser.parse_args()

p = args.prime
F = GF(p)

TRIPLES = list(itertools.combinations(range(8),3))
TIDX = {t:i for i,t in enumerate(TRIPLES)}

# sl3 basis: E01,E02,E10,E12,E20,E21,H1=E00-E11,H2=E11-E22
def mat_zero():
    return Matrix(F,3,3,[0]*9)
BAS=[]
for (i,j) in [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]:
    M=mat_zero(); M[i,j]=F(1); BAS.append(M)
M=mat_zero(); M[0,0]=F(1); M[1,1]=F(-1); BAS.append(M)
M=mat_zero(); M[1,1]=F(1); M[2,2]=F(-1); BAS.append(M)

def sl_coords(M):
    # coordinates in the above basis; requires trace zero.
    assert M.trace() == 0
    return vector(F,[M[0,1],M[0,2],M[1,0],M[1,2],M[2,0],M[2,1],M[0,0],-M[2,2]])

def ad_matrix(g):
    gi = g.inverse()
    cols=[]
    for E in BAS:
        cols.append(sl_coords(g*E*gi))
    return Matrix(F,8,8,cols).transpose()  # columns are images

def det3_cols(u,v,w,a,b,c):
    return Matrix(F,3,3,[[u[a],v[a],w[a]],[u[b],v[b],w[b]],[u[c],v[c],w[c]]]).det()

def wedge3_vecs(u,v,w):
    return vector(F,[det3_cols(u,v,w,a,b,c) for (a,b,c) in TRIPLES])

def lambda3_matrix(A):
    cols=[]
    for (i,j,k) in TRIPLES:
        cols.append(wedge3_vecs(A.column(i), A.column(j), A.column(k)))
    return Matrix(F,56,56,cols).transpose()

def cartan_target():
    # omega/3 in analysis normalization: coefficients +/-1.
    v = vector(F,[0]*56)
    for t,c in { (0,2,6):1, (0,3,4):1, (1,2,5):-1, (1,4,6):1, (1,4,7):1, (3,5,7):1}.items():
        v[TIDX[t]] = F(c)
    return v

def group_matrices(family):
    if family == 'c4_regular':
        g = Matrix(F,3,3,[0,0,-1, 1,0,-1, 0,1,-1])  # BILR a0, order 4 in PGL/GL
        return [g**k for k in range(4)]
    if family == 'c4_2plus1':
        # Need sqrt(-1) in F; for p=5 or 13 use an element of order 4.
        ii = None
        for a in F:
            if a*a == F(-1) and a != 0:
                ii = a; break
        if ii is None:
            raise ValueError('field has no element with square -1; choose p=1 mod 4')
        g = diagonal_matrix(F,[1,1,ii])
        return [g**k for k in range(4)]
    if family == 'klein_diag':
        g1 = diagonal_matrix(F,[-1,1,1])
        g2 = diagonal_matrix(F,[1,-1,1])
        return [identity_matrix(F,3), g1, g2, g1*g2]
    raise ValueError(family)

def parse_charts(ch):
    if ch == 'bilr':
        return [(3,4,5)]
    if ch == 'all':
        return list(itertools.combinations(range(8),3))[:args.max_charts]
    parts = tuple(int(x) for x in ch.split(','))
    assert len(parts)==3
    return [parts]

def solve_chart(S, target, pivot):
    nonpiv=[j for j in range(8) if j not in pivot]
    names=['s']+[f'x_{r}_{c}' for c in nonpiv for r in range(3)]
    R=PolynomialRing(F,names,order='degrevlex')
    gens=R.gens(); s=gens[0]
    var_iter=iter(gens[1:])
    B=Matrix(R,3,8,[0]*24)
    for r,c in enumerate(pivot):
        B[r,c]=R(1)
    for c in nonpiv:
        for r in range(3):
            B[r,c]=next(var_iter)
    pl=[]
    for tri in TRIPLES:
        pl.append(B.matrix_from_columns(tri).det())
    plv=vector(R,pl)
    # Convert S,target into R constants.
    eq=[]
    for i in range(56):
        e = sum(R(S[i,j])*plv[j] for j in range(56))*s - R(target[i])
        if e != 0:
            eq.append(e)
    I=R.ideal(eq)
    t0=time.time()
    rec={'pivot':list(pivot),'variables':len(names),'equations':len(eq)}
    try:
        # Singular will reveal empty ideals quickly in many charts. Dimension of -1 means empty.
        dim=I.dimension()
        rec['dimension']=int(dim)
        rec['contains_one']=bool(I.is_one())
        rec['elapsed_dim_sec']=round(time.time()-t0,3)
        if dim >= 0:
            # Compute a small Groebner signature only when not immediately empty.
            gb=I.groebner_basis()
            rec['groebner_len']=len(gb)
            rec['groebner_degrees_first20']=[int(g.total_degree()) for g in gb[:20]]
            rec['elapsed_total_sec']=round(time.time()-t0,3)
            # For zero-dimensional ideals over small finite fields, count rational points.
            if dim == 0 and p <= 13:
                try:
                    pts=I.variety(ring=F)
                    rec['F_p_point_count']=len(pts)
                    rec['point_examples']=[{str(k):int(v) for k,v in pt.items()} for pt in pts[:3]]
                except Exception as e:
                    rec['variety_error']=str(e)[:300]
    except Exception as e:
        rec['error']=repr(e)
        rec['elapsed_error_sec']=round(time.time()-t0,3)
    return rec

Gs = group_matrices(args.family)
Ad_mats=[ad_matrix(g) for g in Gs]
Lams=[lambda3_matrix(A) for A in Ad_mats]
S=sum(Lams, Matrix(F,56,56,[0]*(56*56)))
target=cartan_target()
# invariant-space sanity
Sinv_rank=S.rank()
aug_rank=Matrix(F,56,57, list(S.columns())+[target]).rank()
records=[]
for pivot in parse_charts(args.charts):
    print(f'family={args.family} p={p} pivot={pivot}', flush=True)
    records.append(solve_chart(S,target,pivot))
    print(json.dumps(records[-1], sort_keys=True), flush=True)

out={
    'prime':p,
    'family':args.family,
    'charts_arg':args.charts,
    'group_size':len(Gs),
    'group_matrices':[[[int(x) for x in row] for row in g] for g in Gs],
    'sum_operator_rank':int(Sinv_rank),
    'target_in_image':bool(aug_rank==Sinv_rank),
    'records':records,
    'normalization':'target is omega/3 with six coefficients +/-1 in the analysis sl3 basis; equation is sum_{h in H} Lambda^3(Ad h)(s*p_chart)=target.',
}
if args.out is None:
    outpath=Path(f'data/exterior_fiber/{args.family}_p{p}_{args.charts.replace(",","-")}.json')
else:
    outpath=Path(args.out)
outpath.parent.mkdir(parents=True,exist_ok=True)
outpath.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print('SAVED',outpath)
