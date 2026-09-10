#!/usr/bin/env python3
"""Replay checker for lift_cut_assignment_certificate.json.

Checks every listed assignment witness against the pinned Wang LUT, the corrected
pivot-17 section, and direct membership in the listed source subspace basis.
"""
from __future__ import annotations
import argparse, hashlib, json, sys
from pathlib import Path
S04=Path('scripts')
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import rref_basis, pack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

def reduce(x:int,basis):
    y=x
    for b in rref_basis(basis,n=9):
        hb=b.bit_length()-1
        if (y>>hb)&1: y^=b
    return y

def inspan(x,basis): return reduce(x,basis)==0

def section_lift(p:int,pivot:int)->int:
    h=pivot.bit_length()-1
    return (p & ((1<<h)-1)) | ((p>>h)<<(h+1))

def sha_obj(obj): return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('cert',nargs='?',default='data/quotient_lift/lift_cut_assignment_certificate.json'); args=ap.parse_args()
    data=json.loads(Path(args.cert).read_text())
    lut,_=load_lut(Path(data['source_lut']))
    pivot=int(data['pivot']); A=[int(x) for x in data['cut_points']]
    assert len(data['certificate'])==(1<<len(A))
    assert sha_obj(data['certificate'])==data['certificate_sha256']
    seen=set()
    for rec in data['certificate']:
        assn=int(rec['assignment_int']); seen.add(assn); bits=[(assn>>i)&1 for i in range(len(A))]
        assert bits==[int(x) for x in rec['bits_in_A_order']]
        basis=[int(x) for x in rec['source_basis9']]
        key=int(pack_basis(rref_basis(basis,n=9)))
        lb=int(lut[key]); cap=20-lb
        assert lb==int(rec['source_lb']) and cap==int(rec['source_cap20'])==int(rec['cap'])
        assert not inspan(pivot,basis), 'witness row should avoid pivot for lift-bit constraint'
        occ=0; eps0=[]; eps1=[]
        for i,p in enumerate(A):
            a0=section_lift(p,pivot); a1=a0^pivot; b0=inspan(a0,basis); b1=inspan(a1,basis)
            assert not (b0 and b1)
            if b0: eps0.append(p)
            if b1: eps1.append(p)
            if bits[i]==0 and b0: occ+=1
            if bits[i]==1 and b1: occ+=1
        assert eps0==[int(x) for x in rec['eps0_points']]
        assert eps1==[int(x) for x in rec['eps1_points']]
        assert occ==int(rec['occ']) and occ>cap
    assert seen==set(range(1<<len(A)))
    print(json.dumps({'status':'ok','assignments_checked':len(seen),'certificate_sha256':data['certificate_sha256'],'cut_points':A,'rhs':len(A)-1},indent=2,sort_keys=True))
if __name__=='__main__': main()
