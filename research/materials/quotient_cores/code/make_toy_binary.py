#!/usr/bin/env python3
"""Write small E11WANG1-like binary test files for analysis C++ DFS."""
import struct
from pathlib import Path
OUT = Path('data/domain_dfs_soundness')
MAGIC=b'E11WANG1'

def words(points):
    w=[0,0,0,0]
    for p in points:
        w[p>>6] |= 1 << (p&63)
    return w

def write(path, rows):
    with open(path,'wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I', len(rows)))
        for cap, dim, pts in rows:
            f.write(struct.pack('<BBHQQQQ', cap, dim, 0, *words(pts)))

OUT.mkdir(parents=True, exist_ok=True)
# Toy from review: |S∩{1,2}|<=1 and |S∩{2,3}|<=2, target 2.
write(OUT/'toy_upper_bounds.bin', [(1,1,[1,2]), (2,2,[2,3])])
# A deliberately impossible tiny case: target 2 with three singleton zero-cap rows.
write(OUT/'toy_impossible.bin', [(0,1,[1]), (0,1,[2]), (0,1,[3])])
print({'toy_upper_bounds': str(OUT/'toy_upper_bounds.bin'), 'toy_impossible': str(OUT/'toy_impossible.bin')})
