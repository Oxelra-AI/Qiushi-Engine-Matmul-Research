#!/usr/bin/env python3
"""Compare Python-built E11 Wang constraints with the native binary file.
"""
import json, struct, sys
from collections import Counter, defaultdict
from pathlib import Path

S04 = Path("scripts")
if str(S04) not in sys.path: sys.path.insert(0, str(S04))
from core_capacity_from_wang_lut import CoreQuotient, load_lut
from e11_wang_dfs_enumerator import build_constraints as py_build

BIN = Path("data/wang_native/e11_wang_cap5.bin")
LUT = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")

def load_bin():
    data = BIN.read_bytes()
    assert data[:8] == b"E11WANG1"
    n = struct.unpack_from('<I', data, 8)[0]
    off = 12
    rows=[]
    for _ in range(n):
        cap, dim, res, w0,w1,w2,w3 = struct.unpack_from('<BBHQQQQ', data, off)
        off += struct.calcsize('<BBHQQQQ')
        pts=set()
        for p in range(1,256):
            words=[w0,w1,w2,w3]
            if (words[p>>6] >> (p&63)) & 1:
                pts.add(p)
        rows.append((cap, frozenset(pts), dim))
    assert off == len(data)
    return rows

def main():
    lut,_=load_lut(LUT)
    core=CoreQuotient(pivot=1)
    py_rows, py_pr = py_build(lut, core, max_cap=5)
    bi_rows=load_bin()
    print('py rows', len(py_rows), 'bin rows', len(bi_rows))
    print('py cap', Counter(c for c,_ in py_rows))
    print('bin cap', Counter(c for c,_,d in bi_rows))
    py_set=Counter(py_rows)
    bi_set=Counter((c,pts) for c,pts,d in bi_rows)
    print('set diff py-bi', sum((py_set-bi_set).values()), 'bi-py', sum((bi_set-py_set).values()))
    if py_set-bi_set:
        print('py not bin head', list((py_set-bi_set).items())[:3])
    if bi_set-py_set:
        print('bin not py head', list((bi_set-py_set).items())[:3])
    py_len=[len(py_pr.get(p,[])) for p in range(256)]
    bi_pr=defaultdict(list)
    for i,(c,pts,d) in enumerate(bi_rows):
        for p in pts: bi_pr[p].append(i)
    bi_len=[len(bi_pr.get(p,[])) for p in range(256)]
    print('point row len equal?', py_len==bi_len, 'maxdiff', max(abs(a-b) for a,b in zip(py_len,bi_len)))
    print('point1 py/bin', py_len[1], bi_len[1])
    # Count valid next choices after fixed prefixes from Python pilot first path [1,2,3,...]
    for prefix in ([1], [1,2], [1,2,3], [1,2,3,4], [1,2,3,4,5], [1,2,3,4,5,8], [1,2,3,4,5,8,9]):
        cnt=0; badprefix=False
        for cap, pts in py_rows:
            if len(set(prefix)&pts)>cap: badprefix=True; break
        if not badprefix:
            for q in range(prefix[-1]+1,256):
                s=set(prefix); s.add(q)
                ok=True
                for cap, pts in py_rows:
                    if len(s&pts)>cap: ok=False; break
                if ok: cnt+=1
        print('prefix',prefix,'bad?',badprefix,'valid_next_py_slow',cnt)

if __name__=='__main__':
    main()
