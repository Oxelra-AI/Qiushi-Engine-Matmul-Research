#!/usr/bin/env python3
"""Coordinate sanity checks for the peer rank-2 quotient support.

The support was reported by research_record as Wang-admissible against all quotient rows.
This script checks it against research_record's native-bit-p quotient binaries and also
against a bit-(p-1) interpretation to expose coordinate/index mismatches.
"""
from __future__ import annotations
import json, struct, hashlib
from pathlib import Path
ROOT=Path('research/research_record')
SUP=[1,3,9,33,99,128,132,144,148,160,184,189,192,198,209,215,224,249,254]
BIN=ROOT/'workspace/data/quotient_dfs/rank2_cap5_n19.bin'
OUT=ROOT/'workspace/data/quotient_lift/peer_support_coordinate_check.json'

def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()

def load(path):
    rows=[]
    with path.open('rb') as f:
        assert f.read(8)==b'E11WANG1'
        n=struct.unpack('<I',f.read(4))[0]
        for i in range(n):
            cap=struct.unpack('<B',f.read(1))[0]; dim=struct.unpack('<B',f.read(1))[0]; f.read(2)
            words=struct.unpack('<4Q',f.read(32)); m=0
            for j,w in enumerate(words): m |= int(w)<<(64*j)
            rows.append((cap,dim,m))
    return rows

def mask(bitminus:bool):
    m=0
    for p in SUP: m |= 1 << (p-1 if bitminus else p)
    return m

def scan(rows,m):
    v=[]; hist={}
    for idx,(cap,dim,rm) in enumerate(rows):
        occ=(m&rm).bit_count()
        if occ>cap:
            v.append({'idx':idx,'cap':cap,'dim':dim,'occ':occ,'excess':occ-cap,'row_pop':rm.bit_count()})
            hist[str(cap)]=hist.get(str(cap),0)+1
    return {'violations':len(v),'hist_by_cap':hist,'head':v[:20]}

def main():
    rows=load(BIN)
    out={'schema':'s0908_peer_support_coordinate_check_v1','support':SUP,'binary':str(BIN),'binary_sha256':sha(BIN),'rows':len(rows),'native_bit_p':scan(rows,mask(False)),'bit_p_minus_1':scan(rows,mask(True))}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
