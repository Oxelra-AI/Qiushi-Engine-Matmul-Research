#!/usr/bin/env python3
"""analysis: Direct search for m_0 of L_anti -- minimum decomposable bivector cover.

Question: what is the smallest m such that L_anti ⊂ span{v_1∧w_1,...,v_m∧w_m}
for decomposable bivectors v_j∧w_j in Λ²(K⁹)?

Known: m_0 ≤ 9 (canonical columns), m_0 ≥ 7 (analysis A-wedge flattening).
Abstract: m_0 ≤ 8 (Laderman conjugation over C).
This script: direct finite-field constructive search.
"""
import numpy as np
from pathlib import Path
import json, time

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "laderman_anti"
OUT.mkdir(parents=True, exist_ok=True)

p = 65521  # large prime

def mod_inv(a, m):
    a = a % m
    if a == 0: return None
    g, x = m, 0
    g1, x1 = a, 1
    while g1 != 0:
        q = g // g1
        g, g1 = g1, g - q * g1
        x, x1 = x1, x - q * x1
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

WEDGE_PAIRS = [(a, b) for a in range(9) for b in range(a+1, 9)]

def wedge_vec_mod(a, b, mod):
    v = np.zeros(36, dtype=np.int64)
    for t, (i, j) in enumerate(WEDGE_PAIRS):
        v[t] = (int(a[i])*int(b[j]) - int(a[j])*int(b[i])) % mod
    return v

# Anti target over F_p
def anti_target_mod(mod):
    T = np.zeros((3, 36), dtype=np.int64)
    SKEW = [(0,1),(0,2),(1,2)]
    for r, (a, b) in enumerate(SKEW):
        M = np.zeros((9, 9), dtype=np.int64)
        for i in range(3):
            for j in range(3):
                A_ij = 0
                if (i,j)==(a,b): A_ij = 1
                elif (i,j)==(b,a): A_ij = mod - 1
                if A_ij == 0: continue
                for k in range(3):
                    y = 3*j+k; z = 3*i+k
                    M[y,z] = (M[y,z] + A_ij) % mod
        for t, (i, j) in enumerate(WEDGE_PAIRS):
            T[r, t] = M[i, j] % mod
    return T

A_TARGET = anti_target_mod(p)
target_rank = modp_rank(A_TARGET.copy(), p)
print(f"Anti target rank over F_{p}: {target_rank}")

def spans_target(bivecs, target, mod):
    """Check if bivecs span target."""
    if len(bivecs) == 0: return False
    B = np.array(bivecs, dtype=np.int64) % mod
    aug = np.vstack([B, target]) % mod
    return modp_rank(B.copy(), mod) == modp_rank(aug.copy(), mod)

# ========== Greedy random search for m=8 cover ==========
print("\n=== Greedy search for m=8 decomposable-bivector cover ===")
rng = np.random.default_rng(42)
t0 = time.time()
best_m = 9
best_cover = None
n_restarts = 5000

for trial in range(n_restarts):
    bivecs = []
    # Build greedily: at each ARTIFACT, add a random decomposable bivector that increases rank
    for step in range(12):  # up to 12 bivectors
        found = False
        for attempt in range(200):
            v = rng.integers(0, p, size=9, dtype=np.int64)
            w = rng.integers(0, p, size=9, dtype=np.int64)
            eta = wedge_vec_mod(v, w, p)
            if np.all(eta % p == 0): continue
            cand = bivecs + [eta]
            B = np.array(cand, dtype=np.int64)
            new_rank = modp_rank(B.copy(), p)
            old_rank = modp_rank(np.array(bivecs, dtype=np.int64).reshape(-1, 36).copy(), p) if bivecs else 0
            if new_rank > old_rank:
                bivecs.append(eta)
                found = True
                break
        if not found:
            break
        if spans_target(bivecs, A_TARGET, p):
            m = len(bivecs)
            if m < best_m:
                best_m = m
                best_cover = [(list(map(int, bv)), ) for bv in bivecs]
                print(f"  Trial {trial}: found m={m} cover!")
            break
    if time.time() - t0 > 120:
        print(f"  Time budget reached at trial {trial}")
        break

print(f"Best m found: {best_m} ({n_restarts} restarts, {time.time()-t0:.1f}s)")

# ========== Targeted search: random 8 decomposable bivectors ==========
print("\n=== Direct random 8-bivector test ===")
hits_8 = 0
hits_7 = 0
n_direct = 200000
t1 = time.time()
for trial in range(n_direct):
    vecs = rng.integers(0, p, size=(8, 9), dtype=np.int64)
    wecs = rng.integers(0, p, size=(8, 9), dtype=np.int64)
    bivecs = [wedge_vec_mod(vecs[j], wecs[j], p) for j in range(8)]
    if spans_target(bivecs, A_TARGET, p):
        hits_8 += 1
        if hits_8 <= 5:
            print(f"  Hit at trial {trial}!")
    if trial < 50000:
        bivecs7 = bivecs[:7]
        if spans_target(bivecs7, A_TARGET, p):
            hits_7 += 1
    if time.time() - t1 > 180:
        print(f"  Time budget at trial {trial}")
        break

trials_done = min(trial + 1, n_direct)
print(f"8-bivec hits: {hits_8}/{trials_done}")
print(f"7-bivec hits: {hits_7}/{min(trials_done, 50000)}")

# ========== Rank of decomposable bivector span in the quotient ==========
# How often do 8 random decomposable bivectors have quotient rank ≥ 3 wrt L_anti?
print("\n=== Quotient rank analysis ===")
qrank_hist = {}
for trial in range(10000):
    vecs = rng.integers(0, p, size=(8, 9), dtype=np.int64)
    wecs = rng.integers(0, p, size=(8, 9), dtype=np.int64)
    bivecs = [wedge_vec_mod(vecs[j], wecs[j], p) for j in range(8)]
    B = np.array(bivecs, dtype=np.int64) % p
    aug = np.vstack([B, A_TARGET]) % p
    rB = modp_rank(B.copy(), p)
    rAug = modp_rank(aug.copy(), p)
    defect = rAug - rB
    qrank_hist[defect] = qrank_hist.get(defect, 0) + 1

print(f"Defect histogram (8 random bivecs): {sorted(qrank_hist.items())}")

# Same for m=9
qrank_hist_9 = {}
for trial in range(10000):
    vecs = rng.integers(0, p, size=(9, 9), dtype=np.int64)
    wecs = rng.integers(0, p, size=(9, 9), dtype=np.int64)
    bivecs = [wedge_vec_mod(vecs[j], wecs[j], p) for j in range(9)]
    B = np.array(bivecs, dtype=np.int64) % p
    aug = np.vstack([B, A_TARGET]) % p
    rB = modp_rank(B.copy(), p)
    rAug = modp_rank(aug.copy(), p)
    defect = rAug - rB
    qrank_hist_9[defect] = qrank_hist_9.get(defect, 0) + 1

print(f"Defect histogram (9 random bivecs): {sorted(qrank_hist_9.items())}")

# ========== Save ==========
out = {
    "field": f"F_{p}",
    "target_rank": int(target_rank),
    "greedy_best_m": int(best_m),
    "direct_8_hits": int(hits_8),
    "direct_8_trials": int(trials_done),
    "direct_7_hits": int(hits_7),
    "direct_7_trials": int(min(trials_done, 50000)),
    "defect_hist_8": {str(k):v for k,v in sorted(qrank_hist.items())},
    "defect_hist_9": {str(k):v for k,v in sorted(qrank_hist_9.items())},
    "interpretation": (
        "Direct search for m_0 of L_anti. m=8 hits would prove m_0<=8 constructively. "
        "Defect 0 means the random bivectors span L_anti. "
        "m_0>=7 from analysis A-wedge flattening det=8."
    )
}
path = OUT / "m0_direct_search.json"
path.write_text(json.dumps(out, indent=2) + "\n")
print(f"\nSAVED {path}")
print(json.dumps(out, indent=2))
