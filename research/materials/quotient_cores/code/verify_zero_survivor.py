#!/usr/bin/env python3
"""Corrected diagnostic for rep2 prefix vertex exclusions in the Wang F2 LUT.

This file originally contained a broken local LUT-key decoder and falsely
reported zero survivors for prefix [1,2].  It now uses the canonical key layout:
low 4 bits store dimension d, then d nine-bit basis vectors from key>>4.
With this correction, prefix [1,2] has no residual-0 vertex exclusions and the
analysis zero-survivor interpretation must remain withdrawn.
"""
from __future__ import annotations
import json, pathlib, pickle, time
from collections import Counter
from typing import Dict, List, Set

def load_lut(path: str) -> Dict[int, int]:
    with open(path, 'rb') as f:
        payload = pickle.load(f)
    if isinstance(payload, dict) and 'lut' in payload:
        return payload['lut']
    return payload

def unpack_basis(key: int) -> List[int]:
    """Canonical Wang LUT key decoder: low 4 bits are dimension, then d 9-bit rows."""
    d = int(key) & 0xF
    vecs = []
    r = int(key) >> 4
    for _ in range(d):
        vecs.append(r & 0x1FF)
        r >>= 9
    return vecs

def span_of(basis: List[int]) -> Set[int]:
    n = len(basis)
    s: set[int] = set()
    for m in range(1, 1 << n):
        v = 0
        for i in range(n):
            if m & (1 << i): v ^= basis[i]
        s.add(v)
    return s

def main():
    lut_path = 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl'
    print(f'Loading LUT {lut_path}...')
    lut = load_lut(lut_path)
    print(f'  {len(lut):,} rows')

    # LUT dimension/lb distribution
    dim_lb = Counter()
    for key, lb in lut.items():
        dim = len(unpack_basis(key))
        dim_lb[(dim, lb)] += 1
    print('\n  Dimension x LB distribution (sorted):')
    for (d, l), c in sorted(dim_lb.items()):
        if l >= 17:
            print(f'    dim={d} lb={l}: {c:,}')

    # ---- Prefix [1,2] vertex exclusion analysis ----
    prefix12 = {1, 2}
    cands12 = set(range(1, 512)) - prefix12
    excluded_by_lb18 = set()
    excluded_by_lb19 = set()
    example_entries = {}  # candidate -> (key, lb, dim, span_size)
    
    t0 = time.time()
    for key, lb in lut.items():
        if lb < 18:
            continue
        basis = unpack_basis(key)
        sp = span_of(basis)
        pocc = len(sp & prefix12)
        res = (20 - lb) - pocc
        if res != 0:
            continue
        cands_in = sp & cands12
        for p in cands_in:
            if p not in example_entries:
                example_entries[p] = (key, lb, len(basis), len(sp))
            if lb == 18:
                excluded_by_lb18.add(p)
            elif lb == 19:
                excluded_by_lb19.add(p)
    t1 = time.time()
    
    print(f'\n---- Prefix [1,2] vertex exclusion ({t1-t0:.1f}s) ----')
    print(f'  Excluded by lb=18 rows: {len(excluded_by_lb18)}')
    print(f'  Excluded by lb=19 rows: {len(excluded_by_lb19)}')
    total_excluded = excluded_by_lb18 | excluded_by_lb19
    print(f'  Total excluded: {len(total_excluded)} / {len(cands12)} candidates')
    
    not_excluded = cands12 - total_excluded
    if not_excluded:
        print(f'  SURVIVORS ({len(not_excluded)}): {sorted(not_excluded)[:20]}...')
    else:
        print(f'  ALL candidates vertex-excluded (unexpected under corrected decoder)!')
    
    # Show a few example exclusions
    print(f'\n  Example vertex exclusions:')
    for p in sorted(list(example_entries.keys()))[:10]:
        key, lb, dim, sz = example_entries[p]
        print(f'    point {p:3d}: lb={lb} dim={dim} span_size={sz} key_hex={key:#x}')

    # ---- Cross-check with prefix [1,2,3] ----
    prefix123 = {1, 2, 3}
    cands123 = set(range(1, 512)) - prefix123
    excluded123 = set()
    
    t0 = time.time()
    for key, lb in lut.items():
        if lb < 17:
            continue
        basis = unpack_basis(key)
        sp = span_of(basis)
        pocc = len(sp & prefix123)
        res = (20 - lb) - pocc
        if res != 0:
            continue
        cands_in = sp & cands123
        excluded123.update(cands_in)
    t1 = time.time()
    
    survivors123 = cands123 - excluded123
    print(f'\n---- Prefix [1,2,3] vertex exclusion ({t1-t0:.1f}s) ----')
    print(f'  Excluded: {len(excluded123)} / {len(cands123)}')
    print(f'  Survivors: {len(survivors123)}')
    
    # Check which prefix-[1,2] exclusions are lost for prefix [1,2,3]
    # (these come from lb=18 rows through {1,2} where prefix_occ becomes 3)
    lost = (excluded_by_lb18 & cands123) - excluded123
    print(f'  Lost exclusions (lb=18 through {{1,2}} with 3 in span): {len(lost)}')
    
    # ---- Dimension analysis of excluding entries ----
    print(f'\n---- Dimension of vertex-excluding entries for [1,2] ----')
    dim_count = Counter()
    for p in sorted(list(example_entries.keys())):
        _, lb, dim, sz = example_entries[p]
        dim_count[dim] += 1
    for d in sorted(dim_count):
        print(f'  First excluding entry dim={d}: {dim_count[d]} candidates')
    
    # ---- Sanity: check a specific non-trivial candidate ----
    test_points = [256, 273, 17, 100, 511]
    print(f'\n---- Detailed check for specific candidates ----')
    for tp in test_points:
        if tp in example_entries:
            key, lb, dim, sz = example_entries[tp]
            basis = unpack_basis(key)
            sp = span_of(basis)
            pocc = len(sp & prefix12)
            res = (20 - lb) - pocc
            print(f'  point {tp}: key={key:#x} basis={basis} lb={lb} dim={dim} '
                  f'span_size={sz} prefix_occ={pocc} residual={res}')
        else:
            print(f'  point {tp}: NOT excluded (BUG?)')
    
    # Save results
    out = pathlib.Path('workspace/data/ruling_line/diagnostic')
    out.mkdir(parents=True, exist_ok=True)
    result = {
        'prefix_12_excluded': len(total_excluded),
        'prefix_12_total_cands': len(cands12),
        'prefix_12_zero_survivors': len(not_excluded) == 0,
        'prefix_123_excluded': len(excluded123),
        'prefix_123_survivors': len(survivors123),
        'prefix_123_lost_exclusions': len(lost),
    }
    (out / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'\n{json.dumps(result, sort_keys=True)}')

if __name__ == '__main__':
    main()
