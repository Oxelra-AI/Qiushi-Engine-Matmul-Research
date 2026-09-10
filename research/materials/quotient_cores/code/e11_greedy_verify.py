#!/usr/bin/env python3
"""Identify cap=2 vectors and verify greedy solution against all constraints."""
import pickle, sys, json
from pathlib import Path
from collections import Counter

sys.path.insert(0, str(Path("scripts")))
from core_capacity_from_wang_lut import CoreQuotient, PIVOTS
from wang_capacity_lazy import (
    pack_basis, unpack_basis, rref_basis,
    subspace_points_from_basis,
)
from wang_capacity_orbit_closed import extension_keys

with open("data/wang_f2_lb20/wang_subspace_lut.pkl", 'rb') as f:
    data = pickle.load(f)
lut = data['lut']
core = CoreQuotient(PIVOTS['E11'])
s = 19

# Find cap=2 vectors
print("=== Cap=2 vectors (can appear with multiplicity 2) ===")
cap2_vectors = []
for q in range(1, 256):
    key8 = pack_basis((q,))
    key9 = core.key9_from_key8(key8)
    L = lut[key9]
    cap = s - L
    if cap == 2:
        # Decode the 8-bit vector as a 3x3 matrix (minus first row/col entry)
        # Bits: related analysis,related analysis,a10,a11,a12,a20,a21,a22
        bits = [(q >> i) & 1 for i in range(8)]
        cap2_vectors.append({'q': q, 'L': L, 'cap': cap, 'bits': bits})
        print(f"  q={q} (0b{q:08b}), L={L}, cap={cap}")

# The greedy solution from cap1_structure
greedy = [1, 2, 3, 4, 8, 9, 12, 13, 16, 18, 20, 22, 24, 27, 28, 31, 32, 36, 42]
print(f"\n=== Verifying greedy solution: {len(greedy)} vectors ===")
print(f"Greedy vectors: {greedy}")

# Build all subspace constraints
def enumerate_subspace_keys(n=8):
    levels = {0: {pack_basis(tuple())}}
    all_keys = set(levels[0])
    for d in range(n):
        nxt = set()
        for key in levels[d]:
            for ekey in extension_keys(unpack_basis(key), n=n):
                if (ekey & 0xF) == d + 1:
                    nxt.add(ekey)
        levels[d + 1] = nxt
        all_keys.update(nxt)
    return sorted(all_keys)

print("Enumerating all F2^8 subspaces...")
keys8 = enumerate_subspace_keys(8)
print(f"Total: {len(keys8)}")

# Build solution dict
sol = {v: 1 for v in greedy}

# Check all constraints
violations = []
violation_by_dim = Counter()
for key8 in keys8:
    key9 = core.key9_from_key8(key8)
    L = lut[key9]
    cap = s - L
    pts = subspace_points_from_basis(unpack_basis(key8))
    occ = sum(sol.get(p, 0) for p in pts)
    if occ > cap:
        dim = key8 & 0xF
        violations.append({'dim': dim, 'L': L, 'cap': cap, 'occ': occ,
                           'excess': occ - cap, 'pts': sorted(pts),
                           'pts_used': sorted(p for p in pts if p in sol)})
        violation_by_dim[dim] += 1

print(f"\nViolations: {len(violations)}")
if violations:
    print(f"By dimension: {dict(sorted(violation_by_dim.items()))}")
    for v in violations[:10]:
        print(f"  dim={v['dim']} L={v['L']} cap={v['cap']} occ={v['occ']} "
              f"pts_used={v['pts_used']}")
else:
    print("GREEDY SOLUTION PASSES ALL 417,199 CONSTRAINTS!")

result = {
    'cap2_vectors': cap2_vectors,
    'greedy_vectors': greedy,
    'total_constraints': len(keys8),
    'violation_count': len(violations),
    'violations_by_dim': dict(violation_by_dim),
    'violations_head': violations[:20],
}
out = Path("data/e11_complete_capacity/greedy_verify.json")
out.write_text(json.dumps(result, indent=2) + '\n')
print(f"\nSaved {out}")
