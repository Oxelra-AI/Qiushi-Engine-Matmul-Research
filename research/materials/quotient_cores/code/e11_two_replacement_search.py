#!/usr/bin/env python3
"""Exact quotient-guided two-replacement search around E11 rank-21 near misses.

Starting from rank-21 CPDs of the E11 core, take a deficiency-one 19-term near
miss obtained by deleting an equal-W pair.  Then for each pair of remaining
terms remove them, giving a 17-column base B.  We ask whether two arbitrary
rank-one 8x9 columns x,y can make L_E11 subset span(B,x,y).

This is not brute force over x,y.  For each base B we reduce all rank-one
columns modulo span(B), compute the target quotient Q = L/(L∩B), and solve the
small exact GF(2) condition Q <= span(rx,ry) using unique quotient residues.
If a hit is found, W factors are recovered by linear solve and the CPD is
verified exactly over F2.
"""
from __future__ import annotations
import argparse, itertools, json, time
from pathlib import Path
from collections import defaultdict
import numpy as np


def outer_mask(u:int,v:int,nv:int=9)->int:
    x=0
    uu=int(u)
    while uu:
        lb=uu & -uu; a=lb.bit_length()-1; uu^=lb
        vv=int(v)
        while vv:
            lbv=vv & -vv; b=lbv.bit_length()-1; vv^=lbv
            x ^= 1<<(a*nv+b)
    return x


def rank_ints(vecs):
    basis={}
    for vv in vecs:
        v=int(vv)
        while v:
            p=v.bit_length()-1
            if p in basis: v ^= basis[p]
            else: basis[p]=v; break
    return len(basis)


def echelon_basis(vecs):
    basis={}
    for vv in vecs:
        v=int(vv)
        while v:
            p=v.bit_length()-1
            if p in basis: v ^= basis[p]
            else: basis[p]=v; break
    return basis


def reduce_by_basis(v:int,basis:dict[int,int])->int:
    """Canonical remainder after reducing by the triangular high-pivot basis."""
    v=int(v)
    for p in sorted(basis.keys(), reverse=True):
        if (v>>p)&1:
            v ^= basis[p]
    return v


def quotient_basis(residues):
    basis={}; out=[]
    for rr in residues:
        v=int(rr)
        while v:
            p=v.bit_length()-1
            if p in basis: v^=basis[p]
            else:
                basis[p]=v; out.append(rr); break
    return out


def span_nonzero(qbasis):
    out=[]
    d=len(qbasis)
    for mask in range(1,1<<d):
        v=0
        for i,q in enumerate(qbasis):
            if (mask>>i)&1: v^=int(q)
        out.append(v)
    return out


def targets_from_core(path):
    T=np.load(path).astype(np.uint8)&1
    m,nv,nw=T.shape
    targets=[]
    for c in range(nw):
        x=0
        for a in range(m):
            for b in range(nv):
                if int(T[a,b,c]): x |= 1<<(a*nv+b)
        targets.append(x)
    return targets,m,nv,nw


def verify_terms(terms, targets, nv=9):
    recon=[0]*len(targets)
    for u,v,w in terms:
        col=outer_mask(u,v,nv)
        for c in range(len(targets)):
            if (int(w)>>c)&1: recon[c]^=col
    return recon==list(targets)


def solve_coeffs(cols, target, nbits):
    R=len(cols); rows=[]
    for bit in range(nbits):
        row=0
        for j,c in enumerate(cols):
            if (int(c)>>bit)&1: row |= 1<<j
        if (int(target)>>bit)&1: row |= 1<<R
        rows.append(row)
    pivots=[]; prow=0
    for col in range(R):
        piv=None
        for rr in range(prow,len(rows)):
            if (rows[rr]>>col)&1: piv=rr; break
        if piv is None: continue
        rows[prow],rows[piv]=rows[piv],rows[prow]
        for rr in range(len(rows)):
            if rr!=prow and ((rows[rr]>>col)&1): rows[rr]^=rows[prow]
        pivots.append(col); prow+=1
    for row in rows:
        if (row & ((1<<R)-1))==0 and ((row>>R)&1): return None
    sol=0
    for i,col in enumerate(pivots):
        if (rows[i]>>R)&1: sol |= 1<<col
    return sol


def reconstruct_w(uv_cols, targets, nbits):
    sols=[]
    for t in targets:
        sol=solve_coeffs(uv_cols,t,nbits)
        if sol is None: return None
        sols.append(sol)
    w=[]
    for i in range(len(uv_cols)):
        mask=0
        for c,sol in enumerate(sols):
            if (sol>>i)&1: mask |= 1<<c
        w.append(mask)
    return w


def save_npz(path, terms, targets, m=8,nv=9,nw=9):
    U=np.zeros((len(terms),m),dtype=np.uint8)
    V=np.zeros((len(terms),nv),dtype=np.uint8)
    W=np.zeros((len(terms),nw),dtype=np.uint8)
    for i,(u,v,w) in enumerate(terms):
        for a in range(m): U[i,a]=(int(u)>>a)&1
        for b in range(nv): V[i,b]=(int(v)>>b)&1
        for c in range(nw): W[i,c]=(int(w)>>c)&1
    np.savez(path,U=U,V=V,W=W)
    return {'npz':str(path),'U':U.tolist(),'V':V.tolist(),'W':W.tolist(),'verified':verify_terms(terms,targets,nv)}


def deficiency(cols,targets):
    rk=rank_ints(cols); rks=rank_ints(list(cols)+list(targets)); return rks-rk,rk,rks


def all_rankone_pool(m=8,nv=9):
    return [(outer_mask(u,v,nv),u,v) for u in range(1,1<<m) for v in range(1,1<<nv)]


def find_pair_for_q(qbasis, residue_to_cands):
    """Find residues r1,r2 in the rank-one residue set with span(qbasis)<=span(r1,r2)."""
    d=len(qbasis)
    if d==0:
        # any two candidates work; choose first nonempty residues
        vals=list(residue_to_cands.keys())
        if len(vals)>=1: return (vals[0], vals[0])
        return None
    if d==1:
        q=int(qbasis[0])
        if q in residue_to_cands:
            # second candidate can be any available residue (including same); final verification will check.
            return (q, next(iter(residue_to_cands.keys())))
        # Need r1+r2=q.
        for r in residue_to_cands.keys():
            s=int(r)^q
            if s in residue_to_cands:
                return (int(r),s)
        return None
    if d==2:
        elems=span_nonzero(qbasis)  # three nonzero elements in Q-subspace
        avail=[e for e in elems if e in residue_to_cands]
        if len(set(avail))>=2:
            return (avail[0], avail[1])
        return None
    return None


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--core',default='data/restricted_cores/mask_001_E11_core.npy')
    ap.add_argument('--pool',default='data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy')
    ap.add_argument('--structure',default='data/e11_rank21_pool_structure.json')
    ap.add_argument('--max-nearmisses',type=int,default=200)
    ap.add_argument('--max-bases',type=int,default=0,help='0 means unlimited')
    ap.add_argument('--json-out',required=True)
    ap.add_argument('--solution-out',default='data/e11_rank19_two_replacement_candidate.npz')
    args=ap.parse_args()
    targets,m,nv,nw=targets_from_core(args.core); nbits=m*nv
    arr=np.load(args.pool)
    structure=json.load(open(args.structure))
    examples=structure.get('deficiency_one_examples',[])[:args.max_nearmisses]
    pool=all_rankone_pool(m,nv)
    print(f'target rank {rank_ints(targets)}, schemes={arr.shape[0]}, near-miss examples={len(examples)}, rankone pool={len(pool)}')
    start=time.time(); logs=[]; qdim_counter=defaultdict(int); bases_tested=0
    for ei,ex in enumerate(examples):
        si=ex['scheme_index']; deleted=set(ex['deleted'])
        row=arr[si]; vals=[int(x) for x in row.tolist()]
        terms21=[tuple(vals[3*i:3*i+3]) for i in range(21)]
        if not verify_terms(terms21,targets,nv):
            logs.append({'example':ei,'scheme_index':si,'error':'scheme_not_verified'}); continue
        seed_terms=[terms21[i] for i in range(21) if i not in deleted]
        seed_uv=[outer_mask(u,v,nv) for u,v,w in seed_terms]
        seed_def=deficiency(seed_uv,targets)
        if seed_def[0]!=1:
            logs.append({'example':ei,'scheme_index':si,'error':'seed_not_def1','seed_def':seed_def}); continue
        for rem2 in itertools.combinations(range(19),2):
            base_terms=[seed_terms[k] for k in range(19) if k not in rem2]
            base_cols=[outer_mask(u,v,nv) for u,v,w in base_terms]
            base_basis=echelon_basis(base_cols)
            target_res=[reduce_by_basis(t,base_basis) for t in targets]
            qbasis=quotient_basis(target_res)
            d=len(qbasis); qdim_counter[d]+=1; bases_tested+=1
            if d<=2:
                residue_to_cands={}
                # Store first few candidates per residue.  Include zero residues too for d=0/1.
                for col,u,v in pool:
                    r=reduce_by_basis(col,base_basis)
                    if r not in residue_to_cands:
                        residue_to_cands[r]=[(u,v,col)]
                    elif len(residue_to_cands[r])<3:
                        residue_to_cands[r].append((u,v,col))
                pair=find_pair_for_q(qbasis,residue_to_cands)
                if pair is not None:
                    r1,r2=pair
                    for cand1 in residue_to_cands[r1]:
                        for cand2 in residue_to_cands[r2]:
                            terms19=list(base_terms)+[(cand1[0],cand1[1],0),(cand2[0],cand2[1],0)]
                            cols=[outer_mask(u,v,nv) for u,v,w in terms19]
                            if deficiency(cols,targets)[0]!=0:
                                continue
                            wm=reconstruct_w(cols,targets,nbits)
                            if wm is None:
                                continue
                            terms19=[(u,v,wm[i]) for i,(u,v,_) in enumerate(terms19)]
                            ok=verify_terms(terms19,targets,nv)
                            sol=save_npz(Path(args.solution_out),terms19,targets,m,nv,nw)
                            out={'status':'found','example_index':ei,'source_example':ex,'removed_from_seed':list(rem2),
                                 'target_quotient_dim':d,'qbasis':qbasis,'residue_pair':[r1,r2],
                                 'candidate_pair':[{'u':cand1[0],'v':cand1[1],'residue':r1},{'u':cand2[0],'v':cand2[1],'residue':r2}],
                                 'verified':ok,'solution':sol,'bases_tested':bases_tested,'qdim_counter':dict(qdim_counter),
                                 'elapsed':time.time()-start}
                            Path(args.json_out).write_text(json.dumps(out,indent=2)+'\n')
                            print('FOUND',json.dumps({k:out[k] for k in ['example_index','removed_from_seed','target_quotient_dim','verified','bases_tested','elapsed']},indent=2))
                            return
            if args.max_bases and bases_tested>=args.max_bases:
                out={'status':'not_found_limited','bases_tested':bases_tested,'examples_scanned':ei+1,
                     'qdim_counter':dict(qdim_counter),'logs':logs[:50],'elapsed':time.time()-start,
                     'interpretation':'No two-replacement rank-19 E11 CPD was found in the bounded exact quotient search; this covers the listed near-miss bases only.'}
                Path(args.json_out).write_text(json.dumps(out,indent=2)+'\n')
                print('LIMIT wrote',args.json_out,json.dumps({'bases_tested':bases_tested,'qdim_counter':dict(qdim_counter),'elapsed':time.time()-start}))
                return
        if (ei+1)%10==0:
            print(f'processed {ei+1}/{len(examples)} examples bases={bases_tested} qdim={dict(qdim_counter)} elapsed={time.time()-start:.1f}s')
    out={'status':'not_found','bases_tested':bases_tested,'examples_scanned':len(examples),
         'qdim_counter':dict(qdim_counter),'logs':logs[:100],'elapsed':time.time()-start,
         'interpretation':'No rank-19 E11 CPD was found by replacing two surviving columns around the recorded deficiency-one rank-21 near-miss examples. This is not a lower bound.'}
    Path(args.json_out).write_text(json.dumps(out,indent=2)+'\n')
    print('NOT FOUND wrote',args.json_out,json.dumps({'bases_tested':bases_tested,'qdim_counter':dict(qdim_counter),'elapsed':time.time()-start}))

if __name__=='__main__': main()
