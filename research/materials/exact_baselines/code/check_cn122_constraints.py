#!/usr/bin/env python3
"""Diagnostic: check if cn122's 21-term E11 core restriction satisfies Wang capacity constraints."""
import numpy as np

def mat_rank_f2(M):
    A = M.copy(); n, m = A.shape; rank = 0
    for col in range(m):
        pivot = None
        for row in range(rank, n):
            if A[row, col]: pivot = row; break
        if pivot is None: continue
        if pivot != rank: A[[rank, pivot]] = A[[pivot, rank]]
        for row in range(n):
            if row != rank and A[row, col]: A[row] = (A[row] + A[rank]) % 2
        rank += 1
    return rank

def mask_to_mat(v):
    M = np.zeros((3, 3), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            if v & (1 << (3*i+j)): M[i, j] = 1
    return M

# Load cn122
lines = open('data/cn122_3x3_r23_repro/scheme.qmm').read().strip().split('\n')
terms = []
current = {}
for line in lines:
    line = line.strip()
    if line.startswith('term '):
        if current: terms.append(current)
        current = {}
    elif line.startswith('u '):
        current['u'] = [int(x) for x in line.split()[1:]]
    elif line.startswith('v '):
        current['v'] = [int(x) for x in line.split()[1:]]
    elif line.startswith('w '):
        current['w'] = [int(x) for x in line.split()[1:]]
if current: terms.append(current)

# Reduce to F2 and restrict to E11 core
surviving_a_factors = []
for t in terms:
    u_f2 = [x % 2 for x in t['u']]
    if u_f2[0] == 0:  # a11 = 0
        # 8-bit A-factor: coordinates a12,...,a33 mapped to bits 0-7
        u8 = u_f2[1:]
        val = sum(b << i for i, b in enumerate(u8))
        surviving_a_factors.append(val)

print(f"cn122 restriction to E11 core: {len(surviving_a_factors)} terms")
print(f"A-factors (8-bit): {surviving_a_factors}")
from collections import Counter
factor_counts = Counter(surviving_a_factors)
print(f"Distinct factors: {len(factor_counts)}")
print(f"Factor multiplicities: {dict(factor_counts)}")

# Build LB table
def classify(f_9bit):
    F = mask_to_mat(f_9bit)
    rk = mat_rank_f2(F)
    e1 = np.array([1,0,0], dtype=np.uint8)
    Fe1_nz = np.any((F @ e1) % 2)
    FTe1_nz = np.any((F.T @ e1) % 2)
    if rk == 1 and (Fe1_nz or FTe1_nz): return 17
    return 18

lb_table = {f8: classify(f8 << 1) for f8 in range(1, 256)}

# Check constraints
r = len(surviving_a_factors)
violations = []
for f8 in range(1, 256):
    lb = lb_table[f8]
    cap = r - lb
    count = sum(1 for a in surviving_a_factors if bin(f8 & a).count('1') % 2 == 1)
    if count > cap:
        violations.append((f8, lb, cap, count))

print(f"\nr = {r}")
print(f"Constraint violations: {len(violations)} / 255")
if violations:
    print("\nViolations:")
    for f8, lb, cap, count in sorted(violations, key=lambda x: -x[3]):
        print(f"  f={f8} (9bit={f8<<1}), LB={lb}, cap={cap}, violators={count}, excess={count-cap}")

# Also check: what's the max number of violators for LB-18 functionals?
max_viol_18 = 0
for f8 in range(1, 256):
    if lb_table[f8] != 18: continue
    count = sum(1 for a in surviving_a_factors if bin(f8 & a).count('1') % 2 == 1)
    max_viol_18 = max(max_viol_18, count)
print(f"\nMax violators on any LB-18 functional: {max_viol_18}")
print(f"Required capacity for LB-18: {max_viol_18} => min rank = {18 + max_viol_18}")

max_viol_17 = 0
for f8 in range(1, 256):
    if lb_table[f8] != 17: continue
    count = sum(1 for a in surviving_a_factors if bin(f8 & a).count('1') % 2 == 1)
    max_viol_17 = max(max_viol_17, count)
print(f"Max violators on any LB-17 functional: {max_viol_17}")
print(f"Required capacity for LB-17: {max_viol_17} => min rank = {17 + max_viol_17}")
