#!/usr/bin/env python3
"""Debug: verify cn122 decomposition mod 2 matches T<3,3,3>."""
import numpy as np

def build_T():
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*k+i] = 1
    return T

def read_scheme(path):
    terms = []
    term = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line.startswith('term '):
                if 'u' in term: terms.append(term)
                term = {}
            elif line.startswith('u '):
                term['u'] = list(map(int, line.split()[1:]))
            elif line.startswith('v '):
                term['v'] = list(map(int, line.split()[1:]))
            elif line.startswith('w '):
                term['w'] = list(map(int, line.split()[1:]))
    if 'u' in term: terms.append(term)
    return terms

T = build_T()
terms = read_scheme('data/cn122_3x3_r23_repro/scheme.qmm')

# Method 1: integer sum then mod 2
recon_int = np.zeros((9,9,9), dtype=np.int64)
for t in terms:
    u = np.array(t['u'], dtype=np.int64)
    v = np.array(t['v'], dtype=np.int64)
    w = np.array(t['w'], dtype=np.int64)
    recon_int += np.einsum('a,b,c->abc', u, v, w)
print(f"Integer decomp matches T: {np.array_equal(recon_int, T.astype(np.int64))}")

# Method 2: reduce each factor mod 2, then accumulate mod 2
recon_f2 = np.zeros((9,9,9), dtype=np.uint8)
for t in terms:
    u = np.array([abs(x)%2 for x in t['u']], dtype=np.uint8).reshape(9,1,1)
    v = np.array([abs(x)%2 for x in t['v']], dtype=np.uint8).reshape(1,9,1)
    w = np.array([abs(x)%2 for x in t['w']], dtype=np.uint8).reshape(1,1,9)
    recon_f2 = (recon_f2 + u*v*w) % 2
print(f"F2 element-wise matches T: {np.array_equal(recon_f2, T)}")
print(f"  Differences: {np.sum(recon_f2 != T)}")

# Method 3: integer sum mod 2 (handles -1*-1=+1 correctly)  
recon_mod2 = recon_int % 2
# Python % is always non-negative for positive divisor, so -1%2 = 1 ✓
print(f"Integer-then-mod2 matches T: {np.array_equal(recon_mod2, T.astype(np.int64))}")
print(f"  Differences: {np.sum(recon_mod2 != T.astype(np.int64))}")

if not np.array_equal(recon_f2, T):
    # Find where they differ
    diffs = np.argwhere(recon_f2 != T)
    print(f"\n  First 10 differences at (a,b,c):")
    for d in diffs[:10]:
        a,b,c = d
        print(f"    ({a},{b},{c}): recon={recon_f2[a,b,c]}, T={T[a,b,c]}")
    # Compare with integer mod 2
    print(f"\n  Comparing F2 method vs integer-mod2:")
    diffs2 = np.argwhere(recon_f2.astype(np.int64) != recon_mod2)
    print(f"    Differences between methods: {len(diffs2)}")
    if len(diffs2) > 0:
        for d in diffs2[:5]:
            a,b,c = d
            print(f"    ({a},{b},{c}): f2={recon_f2[a,b,c]}, int_mod2={recon_mod2[a,b,c]}")

# Now test: for mask 1, restrict cn122 and verify
print("\n--- Testing mask 1 restriction ---")
mask = 1
pivot = 0
free_bits = mask ^ (1 << pivot)  # = 0

# Apply constraint to tensor
T_restr = T.copy()
T_restr[pivot] = 0
core = T_restr[1:]  # remove slice 0
print(f"Core shape: {core.shape}, core nnz: {np.sum(core)}")

# Restrict decomposition (integer, then mod 2)
recon_core_int = np.zeros((8,9,9), dtype=np.int64)
surviving = 0
for t in terms:
    u = list(t['u'])
    v = np.array(t['v'], dtype=np.int64)
    w = np.array(t['w'], dtype=np.int64)
    # The restriction just drops coordinate 0
    # u_restricted = u[1:] (no folding for mask 1)
    u_rest = np.array(u[1:], dtype=np.int64)
    if np.any(u_rest != 0):
        surviving += 1
    recon_core_int += np.einsum('a,b,c->abc', u_rest, v, w)

print(f"Integer restricted matches core: {np.array_equal(recon_core_int % 2, core.astype(np.int64))}")
print(f"Surviving terms (integer nonzero): {surviving}")

# Restrict with F2 reduction
recon_core_f2 = np.zeros((8,9,9), dtype=np.uint8)
surviving_f2 = 0
for t in terms:
    u = [abs(x)%2 for x in t['u']]
    v = np.array([abs(x)%2 for x in t['v']], dtype=np.uint8)
    w = np.array([abs(x)%2 for x in t['w']], dtype=np.uint8)
    u[0] = 0  # apply constraint
    u_rest = np.array(u[1:], dtype=np.uint8)
    if np.any(u_rest):
        surviving_f2 += 1
    recon_core_f2 = (recon_core_f2 + np.einsum('a,b,c->abc', u_rest, v, w)) % 2

print(f"F2 restricted matches core: {np.array_equal(recon_core_f2, core)}")
print(f"Surviving terms (F2 nonzero): {surviving_f2}")
print(f"Differences: {np.sum(recon_core_f2 != core)}")
