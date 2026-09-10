#!/usr/bin/env python3
"""Exact F2 occupation search induced by Wang single-factor restriction table.

Given lower bounds L(S) for A-side restriction subspace orbits S <= F2^9, a
rank-r decomposition can place at most r-L(S) first factors inside S.  Equiv.,
for a multiset P of r projective A-factors, if some span S of selected points
has |P∩S| + L(S) >= r+1 then rank r is impossible.

For r=20, Wang's table has L(full)=20, so rank-20 contradiction would require
a 20-point projective multiset P such that every subspace S satisfies
|P∩S| <= 20-L(S).  This script searches for such escaping sets using the exact
certificate profile.  For r=20, one-dimensional L=19 rows force multiplicity <=1,
so it suffices to search 20-subsets of the 511 nonzero vectors.

The certificate profile stores only orbit representatives, so this script
computes the orbit closure under GL3(left) x GL3(right) over F2 for subspaces
of F2^(3x3) and assigns each generated subspace the representative's L.
"""
from __future__ import annotations
import argparse, json, random, time
from pathlib import Path
from itertools import combinations

ALL_POINTS=list(range(1,512))


def gf2_rank(rows):
    rows=[r for r in rows if r]
    rank=0
    # high-pivot RREF convention not needed for rank
    for bit in range(8,-1,-1):
        piv=None
        for i in range(rank,len(rows)):
            if (rows[i]>>bit)&1:
                piv=i; break
        if piv is None: continue
        rows[rank],rows[piv]=rows[piv],rows[rank]
        for i in range(len(rows)):
            if i!=rank and ((rows[i]>>bit)&1):
                rows[i] ^= rows[rank]
        rank += 1
    return rank


def rref_key(rows):
    """Canonical row space key over F2 with highest-bit pivots.

    The previous incremental attempt could drop dimension after group actions.
    This version is the ordinary Gauss-Jordan algorithm: at pivot bit b, choose
    a row among the not-yet-pivot rows, normalize (trivial over F2), eliminate
    bit b from every other row, and continue downward.
    """
    A=[r for r in rows if r]
    out=[]
    for bit in range(8,-1,-1):
        piv=None
        for i in range(len(A)):
            if (A[i]>>bit)&1:
                piv=i; break
        if piv is None:
            continue
        row=A.pop(piv)
        # Eliminate this pivot from all remaining rows and all earlier pivot rows.
        A=[(x ^ row) if ((x>>bit)&1) else x for x in A]
        out=[(x ^ row) if ((x>>bit)&1) else x for x in out]
        A=[x for x in A if x]
        out.append(row)
    # Deterministic order by pivot/highest bit.
    return tuple(sorted(out, reverse=True))


def span_points(key):
    pts=[0]
    for b in key:
        pts += [x^b for x in pts]
    return [x for x in pts if x]


def mat_mul(A,B):
    # row-major 3x3 over F2, packed bits
    out=0
    for i in range(3):
        for j in range(3):
            s=0
            for k in range(3):
                s ^= ((A>>(3*i+k))&1) & ((B>>(3*k+j))&1)
            if s: out |= 1<<(3*i+j)
    return out


def mat_transpose(A):
    out=0
    for i in range(3):
        for j in range(3):
            if (A>>(3*i+j))&1: out |= 1<<(3*j+i)
    return out


def mat_det(A):
    rows=[sum(((A>>(3*i+j))&1)<<j for j in range(3)) for i in range(3)]
    # rank over F2 for 3-bit rows
    return 1 if gf2_rank(rows)==3 else 0


def gl3():
    return [A for A in range(512) if mat_det(A)]


def mat_transpose9(x):
    out=0
    for i in range(3):
        for j in range(3):
            if (x>>(3*i+j))&1:
                out |= 1<<(3*j+i)
    return out


def act(g,h,x,transpose_flag=0):
    # A-side symmetry for cubic matrix multiplication restrictions:
    # X -> L X R and X -> L X^T R.  Over GL(3,2), inverse/right-dual choices
    # range over the same GL set, so this is enough to close the certificate
    # representatives under the projective group used by Wang.
    if transpose_flag:
        x=mat_transpose9(x)
    return mat_mul(mat_mul(g,x),h)


def inverse_map(GL):
    inv={}
    I=(1<<0)|(1<<4)|(1<<8)
    for A in GL:
        for B in GL:
            if mat_mul(A,B)==I and mat_mul(B,A)==I:
                inv[A]=B; break
        if A not in inv: raise RuntimeError('no inverse')
    return inv


def load_profile(path:Path):
    prof=json.loads(path.read_text())
    reps=[]
    for item in prof['dimension_1_orbits']+prof['dimension_2_orbits']:
        reps.append((tuple(item['constraint_values']), int(item['rank_lower_bound']), item['index']))
    # Include all orbits from profile? For occupancy search, low-dimensional constraints dominate.
    # We will load every orbit by scanning compact fields recursively if available in JSON first_orbits/top not enough.
    # cert_profile has not stored all orbits, so caller may provide --cert to parse all reps.
    return prof, reps


def parse_cert_all_reps(cert:Path):
    import ast, re
    text=cert.read_text(errors='replace')
    reps=[]
    for block in text.split('constrained_tensors {')[1:]:
        block=block.split('\n}\n',1)[0]
        mi=re.search(r'\n\s*index:\s*(\d+)', '\n'+block)
        ml=re.search(r'\n\s*rank_lower_bound:\s*(-?\d+)', '\n'+block)
        mc=re.search(r'\n\s*constraints:\s*(".*")', '\n'+block)
        idx=int(mi.group(1)) if mi else -1
        lb=int(ml.group(1)) if ml else -1
        vals=[]
        if mc:
            b=ast.literal_eval(mc.group(1)).encode('latin1')
            vals=[b[i] | (b[i+1]<<8) for i in range(0,len(b),2)]
        reps.append((tuple(vals),lb,idx))
    return reps


def build_bound_map(reps, max_dim:int, verbose=False):
    GL=gl3()
    actions=[]
    for g in GL:
        for h in GL:
            for tflag in (0,1):
                actions.append((g,h,tflag))
    bmap={}
    orbit_meta={}
    t0=time.time()
    for vals,lb,idx in reps:
        key0=rref_key(vals)
        d=len(key0)
        if d>max_dim: continue
        seen=set()
        for g,h,tflag in actions:
            key=rref_key([act(g,h,x,tflag) for x in key0])
            if len(key)!=d:
                raise RuntimeError('dimension changed')
            seen.add(key)
        for key in seen:
            old=bmap.get(key)
            if old is not None and old!=lb:
                # Equal subspace must have equal bound; if not, keep max and report later.
                bmap[key]=max(old,lb)
            else:
                bmap[key]=lb
            orbit_meta[key]=(idx,lb)
        if verbose:
            print({'rep_index':idx,'dim':d,'lb':lb,'orbit_size':len(seen),'map_size':len(bmap),'elapsed':time.time()-t0})
    return bmap, orbit_meta


def greedy_escape(bmap, r:int, restarts:int, seed:int, max_dim:int):
    rng=random.Random(seed)
    # constraints: for each mapped subspace S, cap = r - L(S). We use all generated subspaces up to max_dim.
    subspaces_by_point={p:[] for p in ALL_POINTS}
    caps={}
    for key,lb in bmap.items():
        cap=r-lb
        if cap < 0: return None, {'impossible':'full bound exceeds r'}
        caps[key]=cap
        for p in span_points(key):
            if p in subspaces_by_point: subspaces_by_point[p].append(key)
    best=[]
    for restart in range(restarts):
        pts=ALL_POINTS[:]
        rng.shuffle(pts)
        chosen=[]; counts={}
        while len(chosen)<r:
            candidates=[]
            for p in pts:
                if p in chosen: continue
                ok=True; tight=0; score=0
                for key in subspaces_by_point[p]:
                    c=counts.get(key,0)
                    if c+1>caps[key]: ok=False; break
                    if c+1==caps[key]: tight+=1
                    score += c
                if ok:
                    candidates.append((tight,score,rng.random(),p))
            if not candidates: break
            # Prefer points causing fewer tight low-dim caps and less overlap.
            candidates.sort()
            p=candidates[0][3]
            chosen.append(p)
            for key in subspaces_by_point[p]: counts[key]=counts.get(key,0)+1
        if len(chosen)>len(best): best=chosen[:]
        if len(chosen)==r:
            return chosen, {'restart':restart,'best_size':len(best)}
    return None, {'best_size':len(best),'best':best}


def violation_stats(points, bmap, r):
    pointset=set(points)
    viol=[]; tight=[]
    for key,lb in bmap.items():
        cnt=sum(1 for p in span_points(key) if p in pointset)
        margin=(r-lb)-cnt
        rec={'key':key,'dim':len(key),'lb':lb,'count':cnt,'cap':r-lb,'margin':margin}
        if margin<0: viol.append(rec)
        elif margin==0: tight.append(rec)
    return viol, tight


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--profile', type=Path, default=Path('data/wang_f2_lb20/cert_profile.json'))
    ap.add_argument('--cert', type=Path, default=Path('data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt'))
    ap.add_argument('--max-dim', type=int, default=3)
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--restarts', type=int, default=200)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--json-out', type=Path)
    ap.add_argument('--verbose', action='store_true')
    args=ap.parse_args()
    reps=parse_cert_all_reps(args.cert)
    reps=[r for r in reps if len(r[0])<=args.max_dim]
    bmap,meta=build_bound_map(reps,args.max_dim,verbose=args.verbose)
    chosen,info=greedy_escape(bmap,args.rank,args.restarts,args.seed,args.max_dim)
    out={'rank':args.rank,'max_dim':args.max_dim,'rep_count_used':len(reps),'mapped_subspace_count':len(bmap),'search_info':info,'escape_found':chosen is not None,'escape_points':chosen}
    if chosen:
        viol,tight=violation_stats(chosen,bmap,args.rank)
        out['violations']=len(viol); out['tight_count']=len(tight); out['tight_by_dim']={}
        for rec in tight:
            out['tight_by_dim'][str(rec['dim'])]=out['tight_by_dim'].get(str(rec['dim']),0)+1
    text=json.dumps(out,indent=2,sort_keys=True)
    print(text)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True,exist_ok=True)
        args.json_out.write_text(text+'\n')

if __name__=='__main__': main()
