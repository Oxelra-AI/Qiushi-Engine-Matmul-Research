#!/usr/bin/env python3
"""analysis: export transported lift-bit relation rows from the 12-point obstruction.

The analysis support cut |S cap A|<=11 is the existential projection of full
Wang lift-bit inequalities on a 12-point set.  To preserve the actual coupling,
this script transports the small CP-minimal 33-row witness family found in
obstruction_structure under the pivot-17 tensor stabilizer, and exports
those full lift-bit inequalities over all quotient points p=1..255:

    sum_{p: s(p) in W} y0_p + sum_{p: s(p)+q in W} y1_p <= cap20(W),
    y0_p + y1_p = x_p.

These rows are valid A-side restrictions for any full rank-20 support with pivot
17.  They are not quotient Wang rows, and they are not final proof evidence by
themselves; they are a compact relational search asset.
"""
from __future__ import annotations
import hashlib, json, sys, time
from collections import Counter
from pathlib import Path
from typing import Iterable
import numpy as np

ROOT=Path('research/research_record')
STRUCT=ROOT/'workspace/data/quotient_lift/obstruction_structure.json'
OUTDIR=ROOT/'workspace/data/quotient_lift/transport'
OUTDIR.mkdir(parents=True,exist_ok=True)
OUT=OUTDIR/'rank2_lift_relation_rows_from_cut33.json'
PIVOT=17
S04=Path('scripts')
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import rref_basis, pack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore


def sha_file(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''):
            h.update(c)
    return h.hexdigest()

def sha_obj(obj)->str:
    return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def bits_to_mat(mask:int)->np.ndarray:
    return np.array([[(mask>>(3*i+j))&1 for j in range(3)] for i in range(3)],dtype=np.uint8)

def mat_to_bits(M)->int:
    x=0
    for i in range(3):
        for j in range(3):
            if int(M[i,j])&1: x|=1<<(3*i+j)
    return x

def gf2_rank(M)->int:
    A=(np.asarray(M,dtype=np.uint8)&1).copy(); m,n=A.shape; r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if A[i,c]: piv=i; break
        if piv is None: continue
        if piv!=r: A[[r,piv]]=A[[piv,r]]
        for i in range(m):
            if i!=r and A[i,c]: A[i]^=A[r]
        r+=1
        if r==m: break
    return int(r)

def gf2_inv(M):
    A=(np.asarray(M,dtype=np.uint8)&1).copy(); n=A.shape[0]
    aug=np.concatenate([A,np.eye(n,dtype=np.uint8)],axis=1); r=0
    for c in range(n):
        piv=None
        for i in range(r,n):
            if aug[i,c]: piv=i; break
        if piv is None: raise ValueError('singular')
        if piv!=r: aug[[r,piv]]=aug[[piv,r]]
        for i in range(n):
            if i!=r and aug[i,c]: aug[i]^=aug[r]
        r+=1
    return aug[:,n:]&1

def gl3():
    out=[]
    for mask in range(1<<9):
        M=bits_to_mat(mask)
        if gf2_rank(M)==3: out.append((mask,M))
    return out

def full_action(P,QinvT,a:int)->int:
    return mat_to_bits((P.T @ bits_to_mat(a) @ QinvT)&1)

def section_lift(p:int,pivot:int=PIVOT)->int:
    h=pivot.bit_length()-1
    return (p & ((1<<h)-1)) | ((p>>h)<<(h+1))

def reduce(x:int,basis:Iterable[int])->int:
    y=int(x)
    for b in rref_basis([int(z) for z in basis],n=9):
        hb=int(b).bit_length()-1
        if (y>>hb)&1: y^=int(b)
    return y

def inspan(x:int,basis:Iterable[int])->bool:
    return reduce(x,basis)==0

def build_stabilizer():
    G=gl3(); qmat=bits_to_mat(PIVOT); out=[]
    for Pmask,P in G:
        for Qmask,Q in G:
            QinvT=gf2_inv(Q).T & 1
            if mat_to_bits((P.T @ qmat @ QinvT)&1)==PIVOT:
                out.append({'Pmask':Pmask,'Qmask':Qmask,'QinvTmask':mat_to_bits(QinvT),'P':P,'QinvT':QinvT})
    return out

def mask_hex(points):
    m=0
    for p in points: m|=1<<p
    return hex(m)

def main():
    t0=time.time(); struct_data=json.loads(STRUCT.read_text())
    chosen=struct_data['chosen_constraint_cover']
    print(f'base chosen constraints {len(chosen)}', flush=True)
    print('Loading LUT...', flush=True); lut,_=load_lut(Path(struct_data['source_lut']))
    print('Building stabilizer...', flush=True); stab=build_stabilizer(); print(len(stab), flush=True)
    best={}  # key=(zmask_hex,omask_hex,cap) -> source rec; also basis key
    basis_seen={}
    for gi,g in enumerate(stab):
        for base_idx,c in enumerate(chosen):
            tbasis=rref_basis([full_action(g['P'],g['QinvT'],int(b)) for b in c['source_basis9']],n=9)
            bkey=int(pack_basis(tbasis)); lb=int(lut[bkey]); cap=20-lb
            if cap!=int(c['cap']):
                raise AssertionError(('cap changed',base_idx,gi,cap,c['cap']))
            if inspan(PIVOT,tbasis):
                raise AssertionError('transported non-q row contains pivot')
            zpts=[]; opts=[]
            for p in range(1,256):
                a0=section_lift(p); a1=a0^PIVOT
                b0=inspan(a0,tbasis); b1=inspan(a1,tbasis)
                if b0 and b1: raise AssertionError('non-q row contains both lifts')
                if b0: zpts.append(p)
                elif b1: opts.append(p)
            zmask=sum(1<<p for p in zpts); omask=sum(1<<p for p in opts)
            key=(zmask,omask,cap)
            if key not in best:
                best[key]={'cap':cap,'source_lb':lb,'source_dim':len(tbasis),'source_basis9':[int(x) for x in tbasis],'eps0_points':zpts,'eps1_points':opts,'eps0_mask_hex':hex(zmask),'eps1_mask_hex':hex(omask),'base_constraint_id':int(c['cid']),'base_constraint_active':int(c['active']),'base_constraint_cap':int(c['cap']),'transport_element_index':gi,'Pmask':int(g['Pmask']),'Qmask':int(g['Qmask']),'QinvTmask':int(g['QinvTmask'])}
            basis_seen.setdefault(bkey,0); basis_seen[bkey]+=1
    rows=list(best.values())
    rows.sort(key=lambda r:(r['cap'], len(r['eps0_points'])+len(r['eps1_points']), r['source_dim'], r['eps0_mask_hex'], r['eps1_mask_hex']))
    cap_hist=Counter(r['cap'] for r in rows); dim_hist=Counter(r['source_dim'] for r in rows); active_hist=Counter(len(r['eps0_points'])+len(r['eps1_points']) for r in rows)
    out={'schema':'s0908_rank2_lift_relation_rows_from_cut33_v1','source_structure':str(STRUCT),'source_structure_sha256':sha_file(STRUCT),'source_lut':struct_data['source_lut'],'source_lut_sha256':struct_data['source_lut_sha256'],'pivot_name':'rank2','pivot':PIVOT,'stabilizer_size':len(stab),'base_constraint_cover_size':len(chosen),'unique_relation_row_count':len(rows),'unique_basis_count':len(basis_seen),'cap_hist':dict(sorted((int(k),int(v)) for k,v in cap_hist.items())),'source_dim_hist':dict(sorted((int(k),int(v)) for k,v in dim_hist.items())),'full_active_point_count_hist':dict(sorted((int(k),int(v)) for k,v in active_hist.items())),'relation_rows':rows,'relation_rows_sha256':sha_obj(rows),'semantics':'For each row: sum_{p in eps0_points} y0_p + sum_{p in eps1_points} y1_p <= cap, with y0_p+y1_p=x_p, is valid for rank2 pivot 17 full A-side lift supports.','elapsed_sec':time.time()-t0}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:out[k] for k in ['unique_relation_row_count','unique_basis_count','cap_hist','source_dim_hist','full_active_point_count_hist','relation_rows_sha256','elapsed_sec']},indent=2,sort_keys=True), flush=True)
    print('saved',OUT, flush=True)

if __name__=='__main__': main()
