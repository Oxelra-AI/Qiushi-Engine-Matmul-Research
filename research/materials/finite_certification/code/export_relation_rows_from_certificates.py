#!/usr/bin/env python3
"""analysis: export rank-2 lift-bit relation rows from obstruction certificates.

Inputs are all-assignment lift certificates for minimized pivot-17 obstructions.
For every distinct Wang source basis appearing in those certificates, and every
element of the actual pivot-17 stabilizer in GL3(F2)xGL3(F2), export the full
lift-bit row

  sum_{p:s(p) in W} y0_p + sum_{p:s(p)+q in W} y1_p <= cap20(W).

This preserves relation-level information that support cuts discard.  It does
not assert that this finite family alone proves a branch closed.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from collections import Counter
from pathlib import Path
import numpy as np

ROOT=Path('research/research_record')
S04=Path('scripts')
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import rref_basis, pack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

PIVOT=17
LUT=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
OUTDIR=ROOT/'workspace/data/quotient_lift/relations'
OUTDIR.mkdir(parents=True,exist_ok=True)

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

def build_stabilizer():
    G=gl3(); qmat=bits_to_mat(PIVOT); out=[]
    for Pmask,P in G:
        for Qmask,Q in G:
            QinvT=gf2_inv(Q).T & 1
            if mat_to_bits((P.T @ qmat @ QinvT)&1)==PIVOT:
                out.append({'Pmask':Pmask,'Qmask':Qmask,'QinvTmask':mat_to_bits(QinvT),'P':P,'QinvT':QinvT})
    return out

def section_lift(p:int,pivot:int=PIVOT)->int:
    h=pivot.bit_length()-1
    return (p & ((1<<h)-1)) | ((p>>h)<<(h+1))

def reduce(x:int,basis)->int:
    y=int(x)
    for b in rref_basis([int(z) for z in basis],n=9):
        hb=int(b).bit_length()-1
        if (y>>hb)&1:
            y^=int(b)
            if y==0: return 0
    return y

def inspan(x:int,basis)->bool:
    return reduce(x,basis)==0

def certificate_entries(path:Path):
    d=json.loads(path.read_text())
    if 'assignment_certificate' in d:
        cert=d['assignment_certificate']['certificate']
        cut=d.get('minimized_points') or d.get('cut',{}).get('points')
    else:
        cert=d['certificate']
        cut=d.get('cut_points') or d.get('points')
    return d,cert,cut

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--certificate',action='append',type=Path,required=True)
    ap.add_argument('--output',type=Path,default=OUTDIR/'rank2_relation_rows_from_two_certificates.json')
    args=ap.parse_args(); t0=time.time()
    print('loading LUT',flush=True); lut,_=load_lut(LUT)
    print('building stabilizer',flush=True); stab=build_stabilizer(); print(f'stab={len(stab)}',flush=True)
    source_basis={} ; source_records=[]
    for ci,path in enumerate(args.certificate):
        data,cert,cut=certificate_entries(path)
        seen_here=set()
        for e in cert:
            b=tuple(int(x) for x in e['source_basis9'])
            if b not in source_basis:
                source_basis[b]={'basis':b,'source_certificate':str(path),'first_assignment':int(e['assignment_int']),'source_cap20':int(e.get('source_cap20',e.get('cap'))),'source_dim':int(e['source_dim']),'source_lb':int(e['source_lb']),'cert_index':ci}
            seen_here.add(b)
        source_records.append({'path':str(path),'sha256':sha_file(path),'certificate_entries':len(cert),'unique_bases_in_certificate':len(seen_here),'cut_points':cut})
    rows={}; basis_transport_count=Counter(); cap_mismatch=[]
    bases=list(source_basis.values())
    for bi,src in enumerate(bases):
        for gi,g in enumerate(stab):
            tbasis=tuple(rref_basis([full_action(g['P'],g['QinvT'],int(b)) for b in src['basis']],n=9))
            key=int(pack_basis(tbasis)); lb=int(lut[key]); cap=20-lb
            if cap != int(src['source_cap20']):
                cap_mismatch.append({'basis_index':bi,'gi':gi,'expected_cap':src['source_cap20'],'got_cap':cap,'tbasis':list(tbasis)})
                continue
            if inspan(PIVOT,tbasis):
                # Certificates for lift obstructions use q-avoiding rows; if a
                # transformed basis contains q, skip rather than making a mixed
                # quotient row. This should not occur under the stabilizer.
                cap_mismatch.append({'basis_index':bi,'gi':gi,'error':'contains_pivot','tbasis':list(tbasis)})
                continue
            eps0=[]; eps1=[]
            for p in range(1,256):
                a0=section_lift(p); a1=a0^PIVOT
                b0=inspan(a0,tbasis); b1=inspan(a1,tbasis)
                if b0 and b1: raise AssertionError('q-avoiding row contains both lifts')
                if b0: eps0.append(p)
                elif b1: eps1.append(p)
            zmask=sum(1<<p for p in eps0); omask=sum(1<<p for p in eps1)
            k=(zmask,omask,cap)
            if k not in rows:
                rows[k]={'cap':cap,'source_lb':lb,'source_dim':len(tbasis),'source_basis9':list(map(int,tbasis)),'eps0_points':eps0,'eps1_points':eps1,'eps0_mask_hex':hex(zmask),'eps1_mask_hex':hex(omask),'source_certificate':src['source_certificate'],'source_certificate_index':src['cert_index'],'source_first_assignment':src['first_assignment'],'base_basis':list(src['basis']),'transport_element_index':gi,'Pmask':int(g['Pmask']),'Qmask':int(g['Qmask']),'QinvTmask':int(g['QinvTmask'])}
            basis_transport_count[bi]+=1
    rel=list(rows.values())
    rel.sort(key=lambda r:(r['cap'],len(r['eps0_points'])+len(r['eps1_points']),r['source_dim'],r['eps0_mask_hex'],r['eps1_mask_hex']))
    cap_hist=Counter(r['cap'] for r in rel); dim_hist=Counter(r['source_dim'] for r in rel); active_hist=Counter(len(r['eps0_points'])+len(r['eps1_points']) for r in rel)
    out={'schema':'s0908_relation_rows_from_lift_certificates_v1','pivot_name':'rank2','pivot':PIVOT,'source_lut':str(LUT),'source_lut_sha256':sha_file(LUT),'stabilizer_size':len(stab),'source_certificates':source_records,'unique_source_bases':len(bases),'unique_relation_row_count':len(rel),'cap_hist':dict(sorted((str(k),int(v)) for k,v in cap_hist.items())),'source_dim_hist':dict(sorted((str(k),int(v)) for k,v in dim_hist.items())),'active_point_count_hist':dict(sorted((str(k),int(v)) for k,v in active_hist.items())),'cap_mismatch_or_errors':cap_mismatch[:20],'relation_rows_sha256':sha_obj(rel),'relation_rows':rel,'semantics':'Each row is valid for pivot-17: sum eps0 y0 + sum eps1 y1 <= cap. It is a transported full-Wang q-avoiding row from a certified lift obstruction assignment witness.','elapsed_sec':time.time()-t0}
    args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:out[k] for k in ['unique_source_bases','unique_relation_row_count','cap_hist','source_dim_hist','active_point_count_hist','relation_rows_sha256','elapsed_sec']},indent=2,sort_keys=True),flush=True)
    print('saved',args.output,flush=True)

if __name__=='__main__': main()
