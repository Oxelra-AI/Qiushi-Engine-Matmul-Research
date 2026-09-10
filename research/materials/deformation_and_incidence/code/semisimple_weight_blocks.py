#!/usr/bin/env python3
r"""Semisimple termwise-aligned stabilizer strata for T_{333}.

If a noncentral stabilizer element lies in the term-scaling tangent of a
minimal decomposition, each factor vector is an eigenvector of the difference
operators
    U: P^T X - X Q^T,    V: Q^T Y - Y R^T,    W: R^T Z - P Z
after putting the semisimple P,Q,R in diagonal form.  The matrix units split
by weights
    alpha = p_a - q_b, beta = q_b - r_c, gamma = r_c - p_a.
A termwise-aligned decomposition splits across weight triples with
alpha+beta+gamma=0.  For each realized weight triple the corresponding block
of T333 is a small coordinate tensor; the number of aligned rank-one terms in
that block is at least the maximum of its three flattening ranks.  The sum of
these block lower bounds is a rigorous necessary lower bound for that weight
pattern.

This script enumerates sorted integer eigenvalue triples in a small box to
identify which repeated-difference flats survive this first flattening test.
It is a pilot for a later exact hyperplane-arrangement enumeration; absence in
the box is not a proof of absence over characteristic zero.
"""
from __future__ import annotations
import argparse, json, itertools, time
from pathlib import Path
from collections import defaultdict, Counter
import numpy as np


def rank_int(M: np.ndarray) -> int:
    # Exact enough for 0/1 incidence matrices of tiny size: use rational-free row reduction over Q via Fractions would be slower.
    # For these 0/1 matrices, verify over two large primes and take common rank.
    def rank_mod(A, p):
        A=np.array(A%p,dtype=np.int64,copy=True); m,n=A.shape; row=0
        for col in range(n):
            if row>=m: break
            nz=np.nonzero(A[row:,col])[0]
            if len(nz)==0: continue
            piv=row+int(nz[0])
            if piv!=row: A[[row,piv]]=A[[piv,row]]
            inv=pow(int(A[row,col]),p-2,p)
            A[row]=(A[row]*inv)%p
            fac=A[:,col].copy(); fac[row]=0
            rows=np.nonzero(fac)[0]
            if len(rows): A[rows]=(A[rows]-fac[rows,None]*A[row])%p
            row+=1
        return row
    return rank_mod(M, 1000003)


def block_lower_bound(support):
    # support triples are (a,b,c) where U index=(a,b), V=(b,c), W=(a,c).
    if not support:
        return 0, (0,0,0), (0,0,0), 0
    Uids=sorted(set((a,b) for a,b,c in support))
    Vids=sorted(set((b,c) for a,b,c in support))
    Wids=sorted(set((a,c) for a,b,c in support))
    u_index={x:i for i,x in enumerate(Uids)}
    v_index={x:i for i,x in enumerate(Vids)}
    w_index={x:i for i,x in enumerate(Wids)}
    # U | VW
    MU=np.zeros((len(Uids), len(Vids)*len(Wids)), dtype=np.int64)
    MV=np.zeros((len(Vids), len(Uids)*len(Wids)), dtype=np.int64)
    MW=np.zeros((len(Wids), len(Uids)*len(Vids)), dtype=np.int64)
    for a,b,c in support:
        ui=u_index[(a,b)]; vi=v_index[(b,c)]; wi=w_index[(a,c)]
        MU[ui, vi*len(Wids)+wi]=1
        MV[vi, ui*len(Wids)+wi]=1
        MW[wi, ui*len(Vids)+vi]=1
    ranks=(rank_int(MU), rank_int(MV), rank_int(MW))
    return max(ranks), ranks, (len(Uids),len(Vids),len(Wids)), len(support)


def analyze_pattern(pvals, qvals, rvals):
    blocks=defaultdict(list)
    for a in range(3):
        for b in range(3):
            for c in range(3):
                alpha=pvals[a]-qvals[b]
                beta=qvals[b]-rvals[c]
                gamma=rvals[c]-pvals[a]
                assert alpha+beta+gamma==0
                blocks[(alpha,beta,gamma)].append((a,b,c))
    block_infos=[]; lb_sum=0
    for key,supp in blocks.items():
        lb,ranks,dims,nnz=block_lower_bound(supp)
        lb_sum+=lb
        block_infos.append({'weight':list(key),'support_size':nnz,'dims':list(dims),'flattening_ranks':list(ranks),'lb':lb})
    block_infos.sort(key=lambda x:(-x['support_size'], x['weight']))
    # A central element has all three difference operators scalar zero after common scalar quotient: all p,q,r constants with same differences scalar.
    # For termwise intersection beyond central, we only need nonconstant pattern in at least one of p,q,r modulo common scalar.
    noncentral = not (len(set(pvals))==1 and len(set(qvals))==1 and len(set(rvals))==1)
    return {'p':list(pvals),'q':list(qvals),'r':list(rvals),'noncentral':noncentral,'num_blocks':len(block_infos),'lb_sum':lb_sum,'blocks':block_infos}


def pattern_signature(rec):
    return tuple(sorted((tuple(b['dims']), tuple(b['flattening_ranks']), b['support_size'], b['lb']) for b in rec['blocks']))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--max-value',type=int,default=4,help='enumerate sorted triples from {0,...,max_value}')
    ap.add_argument('--keep',type=int,default=40)
    ap.add_argument('--out',default='data/semisimple_weight_blocks/weight_block_pilot.json')
    args=ap.parse_args()
    t0=time.time()
    triples=list(itertools.combinations_with_replacement(range(args.max_value+1),3))
    hist=Counter(); sig_best={}; best=[]; total=0; noncentral_total=0
    for pvals in triples:
        for qvals in triples:
            for rvals in triples:
                total+=1
                rec=analyze_pattern(pvals,qvals,rvals)
                if not rec['noncentral']:
                    continue
                noncentral_total+=1
                hist[rec['lb_sum']]+=1
                sig=pattern_signature(rec)
                if sig not in sig_best or rec['lb_sum']<sig_best[sig]['lb_sum']:
                    sig_best[sig]=rec
                if rec['lb_sum']<=22:
                    # keep compact hard cases; omit full block list if too many later
                    best.append(rec)
    best.sort(key=lambda r:(r['lb_sum'], r['num_blocks'], r['p'], r['q'], r['r']))
    # representative signatures with small lb
    sig_reps=sorted(sig_best.values(), key=lambda r:(r['lb_sum'], r['num_blocks'], r['p'], r['q'], r['r']))[:args.keep]
    result={
        'purpose':'Pilot enumeration of semisimple repeated-difference weight-block lower bounds for termwise-aligned nontransverse stabilizer strata.',
        'max_value':args.max_value,
        'sorted_triples_count':len(triples),
        'total_patterns_tested':total,
        'noncentral_patterns_tested':noncentral_total,
        'lb_sum_histogram':{str(k):v for k,v in sorted(hist.items())},
        'patterns_with_flattening_lb_le22_count':len(best),
        'min_lb_sum':min(hist) if hist else None,
        'max_lb_sum':max(hist) if hist else None,
        'hard_cases_first':best[:args.keep],
        'distinct_block_signature_count':len(sig_best),
        'signature_representatives_first':sig_reps,
        'interpretation':'Each lb_sum is a rigorous lower bound for a fixed semisimple weight pattern. Patterns with lb_sum>=23 are excluded for rank 22 inside the termwise-aligned stratum. Patterns with lb_sum<=22 need sharper block-rank computation or exact arrangement enumeration; the small-box enumeration is not a complete characteristic-zero flat enumeration.',
        'elapsed_sec':time.time()-t0,
    }
    out=Path(args.out); out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2,sort_keys=True,default=int)+'\n')
    print(f'tested {noncentral_total} noncentral sorted eigenvalue triples; min lb {result["min_lb_sum"]}; <=22 cases {len(best)}; distinct signatures {len(sig_best)}')
    print(f'wrote {out}')

if __name__=='__main__':
    main()
