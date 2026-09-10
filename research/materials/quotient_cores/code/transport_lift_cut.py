#!/usr/bin/env python3
"""analysis: transport the certified rank-2 lift-bit cut by the actual pivot stabilizer.

The base cut A from analysis is a pivot-17 quotient-coordinate statement
    |S \cap A| <= 11.
It was certified by explicit violated full Wang rows for every assignment of lift
bits on A.  This script transports the cut by the tensor stabilizer elements
(P,Q) with P^T q Q^{-T}=q, not by arbitrary GL(8) relabelings.

For each stabilizer element g, using the fixed high-pivot section s, compute
    g(s(p)) = s(gbar(p)) + delta_g(p) q.
Thus lift bits transform as eps'_{gbar(p)} = eps_p + delta_g(p).  The checker in
this script validates transported witnesses against the pinned Wang LUT and
exports the unique transported cut rows in the native E11WANG1 bit-p format.
"""
from __future__ import annotations
import hashlib, json, struct, sys, time
from collections import Counter
from pathlib import Path
from typing import Iterable

import numpy as np

ROOT = Path('research/research_record')
S04 = Path('scripts')
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, pack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

CERT_PATH = ROOT/'workspace/data/quotient_lift/lift_cut_assignment_certificate.json'
QBIN = ROOT/'workspace/data/quotient_dfs/rank2_cap5_n19.bin'
PAIR_ROWS = ROOT/'workspace/data/quotient_dfs/rank2_cap7_first32.bin'
OUTDIR = ROOT/'workspace/data/quotient_lift/transport'
OUTDIR.mkdir(parents=True, exist_ok=True)
OUT_MANIFEST = OUTDIR/'rank2_lift_cut_stabilizer_transport.json'
ROWBIN = OUTDIR/'rank2_lift_cut_transport_rows.bin'
MERGED = OUTDIR/'rank2_cap5_plus_lift_cut_transport.bin'
MAGIC=b'E11WANG1'
PIVOT=17


def sha_file(path: Path) -> str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20), b''):
            h.update(c)
    return h.hexdigest()


def sha_obj(obj) -> str:
    return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def bits_to_mat(mask:int)->np.ndarray:
    return np.array([[(mask>>(3*i+j))&1 for j in range(3)] for i in range(3)],dtype=np.uint8)


def mat_to_bits(M)->int:
    x=0
    for i in range(3):
        for j in range(3):
            if int(M[i,j])&1:
                x |= 1<<(3*i+j)
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
    aug=np.concatenate([A,np.eye(n,dtype=np.uint8)],axis=1)
    r=0
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
        if gf2_rank(M)==3:
            out.append((mask,M))
    return out


def full_action(P:np.ndarray, QinvT:np.ndarray, a:int)->int:
    A=bits_to_mat(a)
    B=(P.T @ A @ QinvT)&1
    return mat_to_bits(B)


def quotient_project(a:int,pivot:int=PIVOT)->int:
    if a==0 or a==pivot:
        return 0
    h=pivot.bit_length()-1
    if (a>>h)&1:
        a ^= pivot
    low=a & ((1<<h)-1)
    high=(a>>(h+1))<<h
    return low|high


def section_lift(p:int,pivot:int=PIVOT)->int:
    h=pivot.bit_length()-1
    return (p & ((1<<h)-1)) | ((p>>h)<<(h+1))


def reduce(x:int,basis:Iterable[int])->int:
    y=x
    for b in rref_basis([int(z) for z in basis], n=9):
        hb=int(b).bit_length()-1
        if (y>>hb)&1:
            y ^= int(b)
    return y


def inspan(x:int,basis:Iterable[int])->bool:
    return reduce(x,basis)==0


def read_rows_payload(path:Path):
    b=path.read_bytes(); assert b[:8]==MAGIC, path
    n=struct.unpack('<I', b[8:12])[0]
    return n,b[12:]


def write_rows(path:Path, rows:list[tuple[int,int,int]]):
    # rows are (cap, dim_marker, native mask with bit p for point p)
    with path.open('wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I',len(rows)))
        for cap,dim,mask in rows:
            f.write(struct.pack('<BBH', int(cap), int(dim), 0))
            for i in range(4):
                f.write(struct.pack('<Q', (int(mask)>>(64*i)) & ((1<<64)-1)))


def append_merge(src:Path, extra:Path, out:Path):
    n,payload=read_rows_payload(src); m,epayload=read_rows_payload(extra)
    blob=bytearray(); blob.extend(MAGIC); blob.extend(struct.pack('<I',n+m)); blob.extend(payload); blob.extend(epayload)
    out.write_bytes(bytes(blob))
    return n,m,n+m


def load_base_certificate():
    data=json.loads(CERT_PATH.read_text())
    assert data['pivot']==PIVOT and data['all_assignments_certified']
    A=[int(x) for x in data['cut_points']]
    cert={int(rec['assignment_int']):rec for rec in data['certificate']}
    assert len(cert)==(1<<len(A))
    assert sha_obj(data['certificate'])==data['certificate_sha256']
    return data,A,cert


def build_stabilizer():
    G=gl3(); qmat=bits_to_mat(PIVOT); stab=[]
    for Pmask,P in G:
        for Qmask,Q in G:
            QinvT=gf2_inv(Q).T & 1
            image=(P.T @ qmat @ QinvT)&1
            if mat_to_bits(image)==PIVOT:
                stab.append({'Pmask':Pmask,'Qmask':Qmask,'P':P,'QinvT':QinvT,'QinvTmask':mat_to_bits(QinvT)})
    return stab


def action_data_for_element(g, A:list[int]):
    P,QinvT=g['P'],g['QinvT']
    perm={}
    delta={}
    for p in range(1,256):
        x=full_action(P,QinvT,section_lift(p))
        gp=quotient_project(x)
        if gp==0:
            raise AssertionError(('bad quotient image zero',p,x))
        s=section_lift(gp)
        if x==s:
            d=0
        elif x==(s^PIVOT):
            d=1
        else:
            raise AssertionError(('image not in section coset',p,gp,x,s))
        perm[p]=gp; delta[p]=d
    if sorted(perm.values())!=list(range(1,256)):
        raise AssertionError('quotient action is not a permutation')
    cut_unsorted=[perm[p] for p in A]
    if len(set(cut_unsorted))!=len(A):
        raise AssertionError('cut image collision')
    return perm,delta,cut_unsorted,sorted(cut_unsorted)


def verify_transport_cut(data,A,cert,g,perm,delta,cut_sorted,lut) -> dict:
    # For every assignment on sorted transported points, pull it back to the base
    # assignment using eps'_g(p)=eps_p+delta(p), transform the base witness row,
    # and check direct occupation violation.
    idx_new={p:i for i,p in enumerate(cut_sorted)}
    transformed_sources=set(); dim_hist=Counter(); cap_hist=Counter(); active_hist=Counter(); excess_hist=Counter()
    sample=[]
    for assn_new in range(1<<len(A)):
        assn_base=0
        for i,p in enumerate(A):
            p2=perm[p]
            bnew=(assn_new>>idx_new[p2])&1
            bbase=bnew ^ int(delta[p])
            assn_base |= bbase<<i
        rec=cert[assn_base]
        base_basis=[int(x) for x in rec['source_basis9']]
        tbasis=[full_action(g['P'],g['QinvT'],b) for b in base_basis]
        rbasis=rref_basis(tbasis,n=9)
        key=int(pack_basis(rbasis))
        lb=int(lut[key]); cap=20-lb
        assert lb==int(rec['source_lb']) and cap==int(rec['cap'])
        assert not inspan(PIVOT, rbasis)
        occ=0; eps0=[]; eps1=[]
        for p2 in cut_sorted:
            b=(assn_new>>idx_new[p2])&1
            a0=section_lift(p2); a1=a0^PIVOT
            m0=inspan(a0,rbasis); m1=inspan(a1,rbasis)
            assert not (m0 and m1)
            if m0: eps0.append(p2)
            if m1: eps1.append(p2)
            if b==0 and m0: occ+=1
            if b==1 and m1: occ+=1
        assert occ>cap, (assn_new, assn_base, occ, cap, rbasis, rec)
        transformed_sources.add(tuple(rbasis)); dim_hist[len(rbasis)]+=1; cap_hist[cap]+=1; active_hist[len(eps0)+len(eps1)]+=1; excess_hist[occ-cap]+=1
        if len(sample)<4:
            sample.append({'assignment_new':assn_new,'assignment_base':assn_base,'basis9':[int(x) for x in rbasis],'cap':cap,'occ':occ,'eps0_points':eps0,'eps1_points':eps1})
    return {'assignments_checked':1<<len(A),'distinct_transformed_sources_used':len(transformed_sources),'dim_hist':dict(sorted((int(k),int(v)) for k,v in dim_hist.items())),'cap_hist':dict(sorted((int(k),int(v)) for k,v in cap_hist.items())),'active_hist':dict(sorted((int(k),int(v)) for k,v in active_hist.items())),'excess_hist':dict(sorted((int(k),int(v)) for k,v in excess_hist.items())),'sample_witnesses':sample}


def main():
    t0=time.time()
    base_data,A,cert=load_base_certificate()
    print('Loading LUT...', flush=True)
    lut,_=load_lut(Path(base_data['source_lut']))
    print('Building pivot stabilizer...', flush=True)
    stab=build_stabilizer()
    print(f'stabilizer size {len(stab)}', flush=True)
    unique={}; elements=[]; delta_weight_hist=Counter(); cut_orbit_rep_hist=Counter()
    for gi,g in enumerate(stab):
        perm,delta,cut_unsorted,cut_sorted=action_data_for_element(g,A)
        mask=sum(1<<p for p in cut_sorted)
        dvec=[int(delta[p]) for p in A]
        delta_weight_hist[sum(dvec)]+=1
        elements.append({'element_index':gi,'Pmask':int(g['Pmask']),'Qmask':int(g['Qmask']),'QinvTmask':int(g['QinvTmask']),'base_cut_image_unsorted':cut_unsorted,'cut_points':cut_sorted,'cut_mask_hex':hex(mask),'delta_on_base_cut':dvec})
        if mask not in unique:
            unique[mask]={'representative_element_index':gi,'cut_points':cut_sorted,'cut_mask_hex':hex(mask),'delta_on_base_cut':dvec,'Pmask':int(g['Pmask']),'Qmask':int(g['Qmask']),'QinvTmask':int(g['QinvTmask'])}
        cut_orbit_rep_hist[min(cut_sorted)]+=1
    print(f'unique transported cuts {len(unique)}', flush=True)
    # Validate one representative transport for each unique cut.
    validation=[]
    for j,(mask,rec) in enumerate(sorted(unique.items(), key=lambda kv: kv[1]['cut_points'])):
        gi=rec['representative_element_index']; g=stab[gi]
        perm,delta,_,cut_sorted=action_data_for_element(g,A)
        val=verify_transport_cut(base_data,A,cert,g,perm,delta,cut_sorted,lut)
        validation.append({'cut_index':j, **rec, **val})
        if (j+1)%10==0 or j+1==len(unique):
            print(f'  validated {j+1}/{len(unique)} cuts', flush=True)
    rows=[]
    for mask,rec in sorted(unique.items(), key=lambda kv: kv[1]['cut_points']):
        rows.append((len(A)-1, 0, int(mask)))
    write_rows(ROWBIN, rows)
    qn,cn,mn=append_merge(QBIN, ROWBIN, MERGED)
    out={'schema':'s0908_rank2_lift_cut_stabilizer_transport_v1','base_certificate':str(CERT_PATH),'base_certificate_sha256':sha_file(CERT_PATH),'base_certificate_internal_sha256':base_data['certificate_sha256'],'source_lut':base_data['source_lut'],'source_lut_sha256':base_data['source_lut_sha256'],'pivot_name':'rank2','pivot':PIVOT,'section':'high pivot bit removed, same as analysis quotient/orbit convention','stabilizer_size':len(stab),'base_cut_points':A,'base_rhs':len(A)-1,'all_stabilizer_elements':elements,'unique_cut_count':len(unique),'delta_weight_hist':dict(sorted((int(k),int(v)) for k,v in delta_weight_hist.items())),'min_point_hist_over_elements':dict(sorted((int(k),int(v)) for k,v in cut_orbit_rep_hist.items())),'unique_cuts':validation,'row_binary':str(ROWBIN),'row_binary_sha256':sha_file(ROWBIN),'merged_with_rank2_cap5_binary':str(MERGED),'merged_binary_sha256':sha_file(MERGED),'source_quotient_binary':str(QBIN),'source_quotient_binary_sha256':sha_file(QBIN),'source_quotient_rows':qn,'transport_cut_rows':cn,'merged_rows':mn,'pair_rows_for_dfs_context':str(PAIR_ROWS),'pair_rows_sha256':sha_file(PAIR_ROWS),'elapsed_sec':time.time()-t0}
    OUT_MANIFEST.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','stabilizer_size':len(stab),'unique_cut_count':len(unique),'row_binary_sha256':out['row_binary_sha256'],'merged_rows':mn,'merged_sha256':out['merged_binary_sha256'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True), flush=True)
    print('saved', OUT_MANIFEST, flush=True)

if __name__=='__main__':
    main()
