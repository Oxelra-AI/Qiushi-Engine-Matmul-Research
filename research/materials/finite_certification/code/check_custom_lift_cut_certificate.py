#!/usr/bin/env python3
"""analysis: replay a custom lift-cut assignment certificate.

Supports both the analysis flat certificate format and the analysis custom
minimizer format where the certificate is nested under assignment_certificate.
Checks every assignment witness directly against the pinned Wang LUT, the stated
pivot, the high-pivot section, and source-subspace membership.
"""
from __future__ import annotations
import argparse, hashlib, json, sys
from pathlib import Path

S04 = Path('scripts')
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, pack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore


def reduce(x:int,basis):
    y=int(x)
    for b in rref_basis([int(z) for z in basis], n=9):
        hb=int(b).bit_length()-1
        if (y>>hb)&1:
            y ^= int(b)
    return y


def inspan(x:int,basis)->bool:
    return reduce(x,basis)==0


def section_lift(p:int,pivot:int)->int:
    h=pivot.bit_length()-1
    return (p & ((1<<h)-1)) | ((p>>h)<<(h+1))


def sha_obj(obj)->str:
    return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def normalize_payload(data:dict):
    if 'assignment_certificate' in data:
        cert_block=data['assignment_certificate']
        cert=cert_block['certificate']
        points=[int(x) for x in (data.get('minimized_points') or data.get('cut',{}).get('points') or [])]
        if not points:
            raise ValueError('custom certificate lacks minimized_points/cut.points')
        pivot=int(data['pivot'])
        source_lut=data['source_lut']
        expected_sha=cert_block.get('certificate_sha256') or data.get('assignment_certificate_sha256')
        label=data.get('label','custom')
        rhs=len(points)-1
    else:
        cert=data['certificate']
        points=[int(x) for x in data['cut_points']]
        pivot=int(data['pivot'])
        source_lut=data['source_lut']
        expected_sha=data.get('certificate_sha256')
        label=data.get('label','flat')
        rhs=int(data.get('rhs',len(points)-1))
    return cert,points,pivot,source_lut,expected_sha,label,rhs


def bits_from_record(rec, n:int):
    if 'bits_in_A_order' in rec:
        b=[int(x) for x in rec['bits_in_A_order']]
    elif 'bits_in_point_order' in rec:
        b=[int(x) for x in rec['bits_in_point_order']]
    else:
        assn=int(rec['assignment_int']); b=[(assn>>i)&1 for i in range(n)]
    return b


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('cert_json')
    ap.add_argument('--out', default='')
    args=ap.parse_args()
    path=Path(args.cert_json)
    data=json.loads(path.read_text())
    cert,points,pivot,source_lut,expected_sha,label,rhs=normalize_payload(data)
    n=len(points)
    assert len(cert)==(1<<n), (len(cert), n)
    actual_sha=sha_obj(cert)
    if expected_sha:
        assert actual_sha==expected_sha, (actual_sha, expected_sha)
    lut,_=load_lut(Path(source_lut))
    seen=set(); cap_hist={}; dim_hist={}; active_hist={}; excess_hist={}
    for rec in cert:
        assn=int(rec['assignment_int'])
        seen.add(assn)
        bits=bits_from_record(rec,n)
        assert bits==[(assn>>i)&1 for i in range(n)], (assn,bits)
        basis=[int(x) for x in rec['source_basis9']]
        rbasis=rref_basis(basis,n=9)
        key=int(pack_basis(rbasis))
        lb=int(lut[key]); cap=20-lb
        assert lb==int(rec['source_lb']), (assn,lb,rec['source_lb'])
        assert cap==int(rec.get('source_cap20',rec['cap']))==int(rec['cap']), (assn,cap,rec)
        assert not inspan(pivot,rbasis), f'witness for assignment {assn} contains pivot'
        occ=0; eps0=[]; eps1=[]
        for i,p in enumerate(points):
            a0=section_lift(int(p),pivot); a1=a0^pivot
            b0=inspan(a0,rbasis); b1=inspan(a1,rbasis)
            assert not (b0 and b1), (assn,p,rbasis)
            if b0: eps0.append(int(p))
            if b1: eps1.append(int(p))
            if bits[i]==0 and b0: occ+=1
            if bits[i]==1 and b1: occ+=1
        assert eps0==[int(x) for x in rec['eps0_points']], (assn,eps0,rec['eps0_points'])
        assert eps1==[int(x) for x in rec['eps1_points']], (assn,eps1,rec['eps1_points'])
        assert occ==int(rec['occ']) and occ>cap, (assn,occ,cap)
        cap_hist[cap]=cap_hist.get(cap,0)+1
        dim_hist[len(rbasis)]=dim_hist.get(len(rbasis),0)+1
        active_hist[len(eps0)+len(eps1)]=active_hist.get(len(eps0)+len(eps1),0)+1
        excess_hist[occ-cap]=excess_hist.get(occ-cap,0)+1
    assert seen==set(range(1<<n)), (len(seen),n)
    out={'status':'ok','input':str(path),'label':label,'pivot':pivot,'cut_points':points,'rhs':rhs,'assignments_checked':len(seen),'certificate_sha256':actual_sha,'cap_hist':{str(k):v for k,v in sorted(cap_hist.items())},'source_dim_hist':{str(k):v for k,v in sorted(dim_hist.items())},'active_hist':{str(k):v for k,v in sorted(active_hist.items())},'excess_hist':{str(k):v for k,v in sorted(excess_hist.items())}}
    if args.out:
        Path(args.out).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
