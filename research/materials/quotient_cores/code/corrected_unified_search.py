#!/usr/bin/env python3
"""analysis: CORRECTED unified containment search for rank-22 tau-invariant decompositions.

Fixed: L_1 basis uses entries (3b+k, 3k+a) for the first slice space of T_{333}.
The old code incorrectly used {X ⊗ I_3} which has entries (3a+c, 3b+c).
"""
import numpy as np
from pathlib import Path
import json

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / "data" / "unified_containment"
DATA_DIR.mkdir(parents=True, exist_ok=True)

p = 65521  # large prime, p ≡ 1 mod 4

def extended_gcd(a, b):
    if a == 0: return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def mod_inv(a, m):
    g, x, _ = extended_gcd(a % m, m)
    if g != 1: return None
    return x % m

def modp_rank(M, mod):
    M = M.copy() % mod
    rows, cols = M.shape
    r = 0
    for col in range(cols):
        if r >= rows: break
        pivot = None
        for row in range(r, rows):
            if M[row, col] % mod != 0:
                pivot = row; break
        if pivot is None: continue
        M[[r, pivot]] = M[[pivot, r]]
        inv = mod_inv(int(M[r, col]), mod)
        if inv is None: continue
        M[r] = (M[r] * inv) % mod
        for row in range(rows):
            if row == r: continue
            if M[row, col] % mod != 0:
                factor = M[row, col] % mod
                M[row] = (M[row] - factor * M[r]) % mod
        r += 1
    return r

# CORRECT L_1 basis: T_{E_{ab}} has entries at (3b+k, 3k+a) for k=0,1,2
def build_L_basis():
    basis = []
    for a in range(3):
        for b in range(3):
            M = np.zeros((9, 9), dtype=int)
            for k in range(3):
                M[3*b + k, 3*k + a] = 1
            basis.append(M)
    return basis

L_basis = build_L_basis()
L_vecs = np.array([B.ravel() for B in L_basis], dtype=int)
L_rank = modp_rank(L_vecs.copy(), p)
print(f"L_1 rank: {L_rank} (should be 9)")

# Verify naive_27 control
naive_vecs = []
for i in range(3):
    for j in range(3):
        for k in range(3):
            v = np.zeros(9, dtype=int); v[3*j+k] = 1
            w = np.zeros(9, dtype=int); w[3*k+i] = 1
            naive_vecs.append(np.outer(v, w).ravel())
A_naive = np.array(naive_vecs, dtype=int) % p
AB = np.vstack([A_naive, L_vecs]) % p
rA = modp_rank(A_naive.copy(), p)
rAB = modp_rank(AB.copy(), p)
print(f"naive_27 control: rank={rA}, joint rank={rAB}, contained={rA==rAB}")

# === Main search ===
results = {"L_rank": int(L_rank), "naive27_contained": bool(rA == rAB), "searches": {}}
np.random.seed(2024)

def check_containment(pairs, L_vecs_int, mod):
    """Check span{v_i w_i^T} ⊇ L_1."""
    all_vecs = np.array([np.outer(v, w).ravel() % mod for v, w in pairs], dtype=int) % mod
    AB = np.vstack([all_vecs, L_vecs_int]) % mod
    rA = modp_rank(all_vecs.copy(), mod)
    rAB = modp_rank(AB.copy(), mod)
    return rA == rAB, rAB - rA

print("\n=== Random search over skeletons ===")
for f, m in [(0,11), (2,10), (4,9), (6,8), (8,7), (10,6), (12,5)]:
    if f + 2*m != 22: continue
    N = f + m
    n_trials = 3000
    successes = 0
    best_defect = 9
    
    for trial in range(n_trials):
        pairs = []
        for _ in range(f):
            v = np.random.randint(0, p, 9)
            pairs.append((v, v))
            # Also add (v,v) as rank-1 symmetric
        for _ in range(m):
            v = np.random.randint(0, p, 9)
            w = np.random.randint(0, p, 9)
            pairs.append((v, w))
            pairs.append((w, v))  # transpose pair
        
        ok, defect = check_containment(pairs, L_vecs, p)
        if defect < best_defect:
            best_defect = defect
        if ok:
            successes += 1
    
    rate = successes / n_trials
    results["searches"][f"f{f}_m{m}"] = {
        "f": f, "m": m, "N": N, "trials": n_trials,
        "successes": successes, "rate": rate, "best_defect": int(best_defect)
    }
    print(f"  (f={f:2d}, m={m:2d}, N={N:2d}): {successes}/{n_trials} ({rate:.4f}), defect={best_defect}")

# === Try rank-23 control (general random, no tau structure) ===
print("\n=== Rank-23 random controls ===")
for N in [12, 15, 18, 22, 23]:
    n_trials = 2000
    successes = 0
    for trial in range(n_trials):
        pairs = []
        for _ in range(N):
            v = np.random.randint(0, p, 9)
            w = np.random.randint(0, p, 9)
            pairs.append((v, w))
        ok, defect = check_containment(pairs, L_vecs, p)
        if ok: successes += 1
    rate = successes / n_trials
    results["searches"][f"general_N{N}"] = {"N": N, "trials": n_trials, "successes": successes, "rate": rate}
    print(f"  N={N:2d} general pairs: {successes}/{n_trials} ({rate:.4f})")

# === Structured search: row-block products ===
print("\n=== Row-block structured search (8 fixed + 7 free cross-dir) ===")
# K^9 = K^3 ⊗ K^3 (row ⊗ col). Use row directions u_a = e_a and col vectors
n_trials = 5000
successes = 0
for trial in range(n_trials):
    pairs = []
    # 8 fixed: random vectors
    for _ in range(8):
        v = np.random.randint(0, p, 9)
        pairs.append((v, v))
    # 7 free: random cross-row pairs
    for _ in range(7):
        a = np.random.randint(0, 3)
        b = np.random.randint(0, 3)
        while b == a: b = np.random.randint(0, 3)
        x = np.random.randint(0, p, 3)
        y = np.random.randint(0, p, 3)
        v = np.zeros(9, dtype=int); v[3*a:3*a+3] = x % p
        w = np.zeros(9, dtype=int); w[3*b:3*b+3] = y % p
        pairs.append((v, w))
        pairs.append((w, v))
    ok, _ = check_containment(pairs, L_vecs, p)
    if ok: successes += 1
print(f"  cross-dir (f=8,m=7): {successes}/{n_trials}")
results["searches"]["crossdir_f8_m7"] = {"f": 8, "m": 7, "trials": n_trials, "successes": successes}

# === Mixed full-support search ===
print("\n=== Full-support mixed search (various skeletons) ===")
for f, m in [(4,9), (6,8), (8,7)]:
    if f + 2*m != 22: continue
    n_trials = 5000
    successes = 0
    for trial in range(n_trials):
        pairs = []
        for _ in range(f):
            v = np.random.randint(0, p, 9)
            pairs.append((v, v))
        for _ in range(m):
            v = np.random.randint(0, p, 9)
            w = np.random.randint(0, p, 9)
            pairs.append((v, w))
            pairs.append((w, v))
        ok, _ = check_containment(pairs, L_vecs, p)
        if ok: successes += 1
    rate = successes / n_trials
    results["searches"][f"full_f{f}_m{m}"] = {"f": f, "m": m, "trials": n_trials, "successes": successes, "rate": rate}
    print(f"  (f={f}, m={m}): {successes}/{n_trials} ({rate:.4f})")

out_path = DATA_DIR / "corrected_unified_search.json"
with open(out_path, 'w') as f:
    json.dump(results, f, indent=2, default=lambda o: int(o) if isinstance(o, (np.integer,)) else float(o))
print(f"\nSAVED {out_path}")
