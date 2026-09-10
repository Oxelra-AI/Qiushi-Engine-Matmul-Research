#!/usr/bin/env python3
"""Tight-contraction row/column-space obstruction for E11 S-level lifts.

For a fixed S and fixed residual A assignment, any contraction phi whose cover
count equals the minimum matrix rank m_phi must be written as exactly m_phi
rank-one matrices and must land on a minimum-rank element of R_phi+S.  Therefore
each participating rank-one matrix b*c lies in the product of the column and row
spaces of at least one minimum-rank element of that contraction coset.  This file
checks the resulting necessary restrictions, seeking a readable reason for the
fast S-level UNSATs.
"""
from __future__ import annotations
import argparse, json, sys, time
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np

SCRIPTS=Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0,str(SCRIPTS))
import e11_s_coset_rank_sat as sc  # noqa: E402


def row_basis_mask(rows):
    return sc.rref_basis([int(r) for r in rows], nbits=9)


def col_rows_from_rows(rows):
    cols=[]
    for c in range(9):
        v=0
        for b in range(9):
            if (rows[b]>>c)&1:
                v |= 1<<b
        cols.append(v)
    return cols


def span_set(basis):
    out={0}
    for v in basis:
        out |= {x^int(v) for x in list(out)}
    return out


def min_matrices(base_mask, S_basis):
    cur=int(base_mask)
    best=sc.gf2_rank_rows(sc.rows_from_mask81(cur)); mins=[cur]
    n=len(S_basis)
    for step in range(1,1<<n):
        j=(step & -step).bit_length()-1
        cur ^= S_basis[j]
        r=sc.gf2_rank_rows(sc.rows_from_mask81(cur))
        if r<best:
            best=r; mins=[cur]
        elif r==best:
            mins.append(cur)
    return best, mins


def matrix_mask_from_np(M):
    out=0
    for b in range(9):
        row=0
        for c in range(9):
            if int(M[b,c])&1:
                row |= 1<<c
        out |= row << (9*b)
    return out


def analyze(prefix, pool_path, S_index, cover):
    pool=np.load(pool_path)
    S_list=sorted({sc.scheme_s_basis(s) for s in pool})
    S=S_list[S_index]
    _,_,_,Rcoords=sc.quotient_base_residual(prefix)
    Rphi={}
    for phi in range(1,16):
        M=np.zeros((9,9),dtype=np.uint8)
        for k in range(4):
            if (phi>>k)&1: M ^= Rcoords[k]
        Rphi[phi]=matrix_mask_from_np(M)
    m={}; mininfo={}
    for phi in range(1,16):
        best, mins=min_matrices(Rphi[phi], S)
        m[phi]=best
        spaces=[]
        b_union=set(); c_union=set(); bc_pairs=set()
        for mat in mins:
            rows=sc.rows_from_mask81(mat)
            cb=row_basis_mask(col_rows_from_rows(rows))
            rb=row_basis_mask(rows)
            bs=span_set(cb); cs=span_set(rb)
            b_union |= bs; c_union |= cs
            for b in bs:
                if b==0: continue
                for c in cs:
                    if c==0: continue
                    bc_pairs.add((b,c))
            spaces.append({'matrix_hex':hex(mat),'col_basis':[int(x) for x in cb],'row_basis':[int(x) for x in rb],'col_dim':len(cb),'row_dim':len(rb)})
        mininfo[phi]={'m':best,'min_count':len(mins),'spaces_head':spaces[:10],'b_union_count_nonzero':len([x for x in b_union if x]),'c_union_count_nonzero':len([x for x in c_union if x]),'bc_pair_union_count':len(bc_pairs),'b_union':sorted([int(x) for x in b_union if x]),'c_union':sorted([int(x) for x in c_union if x])}
    cov={phi:sum(1 for a in cover if ((phi&a).bit_count()&1)) for phi in range(1,16)}
    tight=[phi for phi in range(1,16) if cov[phi]==m[phi]]
    term_recs=[]; impossible=[]
    for ti,a in enumerate(cover):
        phis=[phi for phi in tight if (phi&a).bit_count()&1]
        allowed_b=set(range(1,512)); allowed_c=set(range(1,512))
        for phi in phis:
            allowed_b &= set(mininfo[phi]['b_union'])
            allowed_c &= set(mininfo[phi]['c_union'])
        rec={'term':ti,'a':int(a),'tight_phis':phis,'allowed_b_count':len(allowed_b),'allowed_c_count':len(allowed_c),'allowed_b_head':sorted(allowed_b)[:30],'allowed_c_head':sorted(allowed_c)[:30]}
        if not allowed_b or not allowed_c:
            impossible.append(rec)
        term_recs.append(rec)
    return {'S_index':S_index,'S_hash':sc.basis_hash(S),'cover':cover,'m_by_phi':{str(k):int(v) for k,v in m.items()},'coverage_by_phi':{str(k):int(v) for k,v in cov.items()},'tight_phis':tight,'mininfo':{str(k):v for k,v in mininfo.items()},'term_space_restrictions':term_recs,'terms_with_empty_space':impossible,'space_obstruction_found':bool(impossible)}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--prefix', required=True)
    ap.add_argument('--pool', type=Path, required=True)
    ap.add_argument('--S-index', type=int, default=0)
    ap.add_argument('--cover', required=True)
    ap.add_argument('--out', type=Path, required=True)
    args=ap.parse_args(); t0=time.time()
    prefix=[int(x) for x in args.prefix.split(',') if x.strip()]
    cover=[int(x) for x in args.cover.split(',') if x.strip()]
    result=analyze(prefix,args.pool,args.S_index,cover)
    result['purpose']='tight contraction row/column-space necessary restrictions for one S and cover'
    result['field']='F2'; result['prefix']=prefix; result['pool']=str(args.pool); result['elapsed_sec']=time.time()-t0
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True,default=int)+'\n')
    print(json.dumps({'S_index':result['S_index'],'tight_phis':result['tight_phis'],'space_obstruction_found':result['space_obstruction_found'],'terms_with_empty_space':len(result['terms_with_empty_space']),'term_counts':[(r['term'],r['a'],r['allowed_b_count'],r['allowed_c_count']) for r in result['term_space_restrictions']]},indent=2,sort_keys=True))
    print('wrote',args.out)

if __name__=='__main__': main()
