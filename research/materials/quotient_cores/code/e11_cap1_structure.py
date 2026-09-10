#!/usr/bin/env python3
"""Analyze the cap=1 constraint structure for E11 core at s=19."""
import pickle, sys, json
from pathlib import Path
from collections import Counter

sys.path.insert(0, str(Path("scripts")))
from core_capacity_from_wang_lut import CoreQuotient, PIVOTS
from wang_capacity_lazy import (
    pack_basis, unpack_basis, rref_basis,
    subspace_points_from_basis,
)

with open("data/wang_f2_lb20/wang_subspace_lut.pkl", 'rb') as f:
    data = pickle.load(f)
lut = data['lut']

core = CoreQuotient(PIVOTS['E11'])
s = 19

# Dim-1: each core vector q -> capacity
cap_dist = Counter()
cap1_vectors = set()
for q in range(1, 256):
    key8 = pack_basis((q,))
    key9 = core.key9_from_key8(key8)
    L = lut[key9]
    cap = s - L
    cap_dist[cap] += 1
    if cap <= 1:
        cap1_vectors.add(q)

print("Dim-1 capacity at s=19:")
for c in sorted(cap_dist):
    print(f"  cap={c}: {cap_dist[c]} vectors")
print(f"Vectors with x_q <= 1: {len(cap1_vectors)}/255")

# Dim-2: triple exclusions
from itertools import combinations
cap1_triples = set()
cap_dist2 = Counter()
seen_subs = set()
for a, b in combinations(range(1, 256), 2):
    c = a ^ b
    key_triple = frozenset((a, b, c))
    if key_triple in seen_subs:
        continue
    seen_subs.add(key_triple)
    key8 = pack_basis(rref_basis((a, b), n=8))
    key9 = core.key9_from_key8(key8)
    L = lut[key9]
    cap = s - L
    cap_dist2[cap] += 1
    if cap <= 1:
        cap1_triples.add(key_triple)

print(f"\nDim-2 capacity at s=19:")
for c in sorted(cap_dist2):
    print(f"  cap={c}: {cap_dist2[c]} subspaces")
print(f"Cap<=1 triples: {len(cap1_triples)}")

# Vertices in cap=1 triples
v_in_triples = set()
for t in cap1_triples:
    v_in_triples.update(t)
print(f"Vertices in cap<=1 triples: {len(v_in_triples)}/255")

# Degree distribution: how many cap=1 triples contain each vector
from collections import defaultdict
deg = defaultdict(int)
for t in cap1_triples:
    for v in t:
        deg[v] += 1
deg_dist = Counter(deg.values())
print(f"\nDegree dist in cap=1 hypergraph:")
for d in sorted(deg_dist):
    print(f"  degree {d}: {deg_dist[d]} vertices")
max_deg_v = max(deg, key=deg.get) if deg else 0
print(f"Max degree: {max(deg.values()) if deg else 0} (vertex {max_deg_v})")

# Quick feasibility check: can we find 19 independent vectors?
# Greedy: pick vertex with lowest degree
used = set()
for _ in range(19):
    best = None
    best_deg = float('inf')
    for v in range(1, 256):
        if v in used:
            continue
        # Check if v conflicts with any used vertex
        ok = True
        for t in cap1_triples:
            if v in t and len(t & used) >= 1:
                ok = False
                break
        if ok:
            d = deg.get(v, 0)
            if d < best_deg:
                best_deg = d
                best = v
    if best is None:
        print(f"\nGreedy failed at size {len(used)} - couldn't add more")
        break
    used.add(best)

print(f"\nGreedy independent set: {len(used)} vectors")
if len(used) >= 19:
    print("  Greedy found 19 independent vectors -> LP likely feasible")
    print(f"  Vectors: {sorted(used)[:25]}...")

result = {
    'dim1_cap_dist': dict(cap_dist),
    'dim2_cap_dist': dict(cap_dist2),
    'cap1_triples_count': len(cap1_triples),
    'vertices_in_cap1': len(v_in_triples),
    'greedy_independent_set_size': len(used),
    'greedy_vectors': sorted(used) if len(used) >= 19 else None,
}
out = Path("data/e11_complete_capacity/cap1_structure.json")
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps(result, indent=2) + '\n')
print(f"\nSaved {out}")
