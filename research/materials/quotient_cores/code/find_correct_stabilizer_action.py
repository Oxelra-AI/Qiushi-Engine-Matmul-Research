#!/usr/bin/env python3
"""Test infinitesimal GL3^3 action conventions against the cn122 Jacobian.

The coefficient vectors in a rank-one tensor decomposition are linear forms,
so the true stabilizer action is contragredient to variable transformations.
This script enumerates transpose/sign variants for A,B,C-side formulas and
reports rank(JD).  A correct Lie algebra stabilizer span should have image rank
0, except for the scalar direction that scales the tensor rather than fixing it
if the action includes the full isotropy rather than the stabilizer.
"""
from __future__ import annotations
from pathlib import Path
import itertools, argparse, json
from exact_modular_tangent import parse_qmm, build_j_rows, rank_mod, matmul3_left, matmul3_right, image_rows


def transpose(M):
    return [M[3*j+i] for i in range(3) for j in range(3)]


def left(E,M): return matmul3_left(E,M)
def right(M,E): return matmul3_right(M,E)

def neg(v,p): return [(-x)%p for x in v]
def add(dst, off, vec, sign, p):
    for a,x in enumerate(vec): dst[off+a]=(dst[off+a]+sign*x)%p

# For a matrix coefficient U, possible infinitesimal actions of a Lie basis X:
# name -> vector.  The correct dual action of A -> P A Q^{-1} on coefficient
# matrix U is U -> P^{-T} U Q^T, infinitesimally dP: -P^T? and dQ: U Q^T.
# We enumerate common left/right/transposed/sign variants.
def variant_apply(side, E, M, p):
    ET=transpose(E)
    variants={
        'L_E': left(E,M), 'L_ET': left(ET,M), 'R_E': right(M,E), 'R_ET': right(M,ET),
        '-L_E': neg(left(E,M),p), '-L_ET': neg(left(ET,M),p), '-R_E': neg(right(M,E),p), '-R_ET': neg(right(M,ET),p),
    }
    return variants[side]


def build_action(terms,p,labels):
    # labels dict entries: P_on_U, P_on_W, Q_on_U, Q_on_V, R_on_V, R_on_W.
    r=len(terms)
    pvecs=[[0]*(27*r) for _ in range(9)]
    qvecs=[[0]*(27*r) for _ in range(9)]
    rvecs=[[0]*(27*r) for _ in range(9)]
    for it,t in enumerate(terms):
        U=[x%p for x in t['u']]; V=[x%p for x in t['v']]; W=[x%p for x in t['w']]
        for j in range(3):
            for k in range(3):
                idx=3*j+k; E=[0]*9; E[idx]=1
                add(pvecs[idx],27*it,variant_apply(labels['P_on_U'],E,U,p),1,p)
                add(pvecs[idx],27*it+18,variant_apply(labels['P_on_W'],E,W,p),1,p)
                add(qvecs[idx],27*it,variant_apply(labels['Q_on_U'],E,U,p),1,p)
                add(qvecs[idx],27*it+9,variant_apply(labels['Q_on_V'],E,V,p),1,p)
                add(rvecs[idx],27*it+9,variant_apply(labels['R_on_V'],E,V,p),1,p)
                add(rvecs[idx],27*it+18,variant_apply(labels['R_on_W'],E,W,p),1,p)
    return [[x%p for x in row] for row in (pvecs+qvecs+rvecs)]

# Search over two derived plausible trilinear-dual conventions plus broad paired variants.
CANDIDATES=[]
# primal trace A->P A Q^-1, B->Q B R^-1, C->R C P^-1; coefficient dual:
# U->P^-T U Q^T, V->Q^-T V R^T, W->R^-T W P^T.
CANDIDATES.append({'name':'dual_trace','P_on_U':'-L_ET','Q_on_U':'R_ET','Q_on_V':'-L_ET','R_on_V':'R_ET','R_on_W':'-L_ET','P_on_W':'R_ET'})
# output convention C/output->P C R^-1; coefficient dual W->P^-T W R^T.
CANDIDATES.append({'name':'dual_output','P_on_U':'-L_ET','Q_on_U':'R_ET','Q_on_V':'-L_ET','R_on_V':'R_ET','P_on_W':'-L_ET','R_on_W':'R_ET'})
# Peer primal formulas, no dual
CANDIDATES.append({'name':'peer_primal_output','P_on_U':'L_E','Q_on_U':'-R_E','Q_on_V':'L_E','R_on_V':'-R_E','P_on_W':'L_E','R_on_W':'-R_E'})
CANDIDATES.append({'name':'peer_primal_trace','P_on_U':'L_E','Q_on_U':'-R_E','Q_on_V':'L_E','R_on_V':'-R_E','R_on_W':'L_E','P_on_W':'-R_E'})


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('scheme',type=Path); ap.add_argument('--p',type=int,default=101); ap.add_argument('--json-out',type=Path)
    args=ap.parse_args(); S=parse_qmm(args.scheme); J=build_j_rows(S['terms'],args.p)
    out=[]
    for cand in CANDIDATES:
        labels={k:v for k,v in cand.items() if k!='name'}
        D=build_action(S['terms'],args.p,labels)
        rr=rank_mod(D,args.p); ir=rank_mod(image_rows(J,D,args.p),args.p)
        out.append({'name':cand['name'],'span_rank':rr,'image_rank_under_J':ir,'kernel_intersection_dim':rr-ir,'labels':labels})
        print(out[-1])
    txt=json.dumps(out,indent=2,sort_keys=True)
    if args.json_out: args.json_out.parent.mkdir(parents=True,exist_ok=True); args.json_out.write_text(txt+'\n')

if __name__=='__main__': main()
