#!/usr/bin/env python3
"""Critical check: do rank-21 pool rows contain terms with u=1 (E11-only)?

If a core decomposition has terms with u_t = 1 (bit 0 only in 9-bit),
those terms contribute nothing to the core tensor (which lives on slices 1-8).
The effective core rank would be 21 - count_of_u1_terms.

If effective rank = 19, we already have a rank-19 core decomposition!
"""
import numpy as np, json, sys
from pathlib import Path
from collections import Counter

sys.path.insert(0, str(Path("scripts")))
from core_capacity_from_wang_lut import CoreQuotient

pool = np.load("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
core = CoreQuotient(pivot=1)

N, cols = pool.shape
R = cols // 3  # 21

print(f"Pool shape: {N} rows, {cols} columns = {R} terms × 3")
print(f"Value range: u ∈ [{pool.min()}, {pool.max()}]")

# Check each row for terms with u=1 or u with only bit 0
u1_counts = []
u0_counts = []  # terms where project9(u) == 0

for row_idx in range(N):
    row = pool[row_idx]
    n_u1 = 0
    n_q0 = 0
    for t in range(R):
        u = int(row[3*t])
        if u == 1:
            n_u1 += 1
        q = core.project9(u)
        if q == 0:
            n_q0 += 1
    u1_counts.append(n_u1)
    u0_counts.append(n_q0)

print(f"\nTerms with u=1 (E₁₁ only):")
print(f"  Distribution: {Counter(u1_counts)}")

print(f"\nTerms with project9(u)=0:")
print(f"  Distribution: {Counter(u0_counts)}")

# Check first 5 rows in detail
for row_idx in range(5):
    row = pool[row_idx]
    u_vals = [int(row[3*t]) for t in range(R)]
    q_vals = [core.project9(u) for u in u_vals]
    u1_terms = [(t, u_vals[t]) for t in range(R) if q_vals[t] == 0]
    
    print(f"\nRow {row_idx}: u-masks = {u_vals}")
    print(f"  Quotient dirs = {q_vals}")
    print(f"  Direction-0 terms: {u1_terms}")
    print(f"  Distinct nonzero dirs: {len(set(q for q in q_vals if q != 0))}")
    
    # Verify: do the remaining terms reconstruct the core?
    T_core = np.zeros((8,9,9), dtype=np.uint8)
    for a in range(8):
        for j in range(3):
            for k in range(3):
                i = (a+1) // 3  # using T[3i+j, 3j+k, 3i+k]=1
                jj = (a+1) % 3
                T_core[a, 3*jj+k, 3*i+k] = 1
    
    # Build core from ALL 21 terms
    T_recon = np.zeros((8,9,9), dtype=np.uint8)
    for t in range(R):
        u = u_vals[t]
        v = int(row[3*t+1])
        w = int(row[3*t+2])
        for a in range(8):
            if (u >> (a+1)) & 1:  # bits 1-8 map to core slices 0-7
                for b in range(9):
                    for c in range(9):
                        if ((v >> b) & 1) and ((w >> c) & 1):
                            T_recon[a,b,c] ^= 1
    
    diff_all = int(np.sum(T_core != T_recon))
    
    # Build core from only nonzero-quotient terms
    T_recon2 = np.zeros((8,9,9), dtype=np.uint8)
    for t in range(R):
        u = u_vals[t]
        if core.project9(u) == 0:
            continue  # skip direction-0 terms
        v = int(row[3*t+1])
        w = int(row[3*t+2])
        for a in range(8):
            if (u >> (a+1)) & 1:
                for b in range(9):
                    for c in range(9):
                        if ((v >> b) & 1) and ((w >> c) & 1):
                            T_recon2[a,b,c] ^= 1
    
    diff_nonzero = int(np.sum(T_core != T_recon2))
    
    print(f"  Core diff (all 21 terms): {diff_all}")
    print(f"  Core diff (nonzero-quotient only): {diff_nonzero}")
    
    if diff_nonzero == 0 and len(u1_terms) > 0:
        print(f"  *** EFFECTIVE RANK {R - len(u1_terms)} CORE DECOMPOSITION! ***")
