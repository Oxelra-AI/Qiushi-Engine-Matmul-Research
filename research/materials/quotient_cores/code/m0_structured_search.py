#!/usr/bin/env python3
"""analysis: Structural m_0 determination using the Λ²U ⊗ Sym²C decomposition.

KEY INSIGHT: K⁹ = U⊗C with U=C=K³ (row ⊗ column). Then:
  Λ²(U⊗C) = (Λ²U ⊗ Sym²C) ⊕ (Sym²U ⊗ Λ²C)
and L_anti lives ENTIRELY in Λ²U ⊗ Sym²C:
  L_anti = Λ²U ⊗ <q>  where q = f₀² + f₁² + f₂² ∈ Sym²C.

A decomposable bivector (u₁⊗c₁)∧(u₂⊗c₂) projects to (u₁∧u₂)⊗(c₁⊙c₂) in Λ²U⊗Sym²C.

So the m_0 question reduces to: find m rank-1 tensors α_j⊗β_j in K³⊗K⁶
(with α_j ∈ Λ²U and β_j = c_j⊙d_j ∈ Sym²C) whose span contains Λ²U⊗<q>.

This is a structured decomposition problem, tractable by parametrization.
"""
import numpy as np
from pathlib import Path
import json, time

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "laderman_anti"
OUT.mkdir(parents=True, exist_ok=True)

p = 65521

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

# Sym²(K³) basis: {f_i⊙f_j : i≤j}, dimension 6
# Ordered: (0,0),(0,1),(0,2),(1,1),(1,2),(2,2)
SYM2_PAIRS = [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]

def sym2_vec(c, d, mod):
    """c⊙d as 6-vector in Sym²(K³)."""
    v = np.zeros(6, dtype=np.int64)
    for t, (i, j) in enumerate(SYM2_PAIRS):
        if i == j:
            v[t] = (int(c[i]) * int(d[i])) % mod
        else:
            v[t] = (int(c[i]) * int(d[j]) + int(c[j]) * int(d[i])) % mod
    return v

def wedge2_vec(u, v, mod):
    """u∧v as 3-vector in Λ²(K³)."""
    w = np.zeros(3, dtype=np.int64)
    w[0] = (int(u[0])*int(v[1]) - int(u[1])*int(v[0])) % mod  # e₀∧e₁
    w[1] = (int(u[0])*int(v[2]) - int(u[2])*int(v[0])) % mod  # e₀∧e₂
    w[2] = (int(u[1])*int(v[2]) - int(u[2])*int(v[1])) % mod  # e₁∧e₂
    return w

# Target: q = f₀² + f₁² + f₂² in Sym²C
q = np.zeros(6, dtype=np.int64)
for k in range(3):
    fk = np.zeros(3, dtype=np.int64); fk[k] = 1
    q = (q + sym2_vec(fk, fk, p)) % p
print(f"q = {q}")  # should be [1,0,0,1,0,1] = f0²+f1²+f2²

# Target in K³⊗K⁶: rows are e_{ab}⊗q for (a,b) ∈ {(01),(02),(12)}
# This is a 3×18 matrix where row r = e_r ⊗ q (e_r is basis of Λ²U)
TARGET = np.zeros((3, 18), dtype=np.int64)
for r in range(3):
    for j in range(6):
        TARGET[r, 6*r + j] = q[j]
target_rank = modp_rank(TARGET.copy(), p)
print(f"Target rank: {target_rank}")

# Each rank-1 tensor α⊗β ∈ K³⊗K⁶ is an 18-vector
def rank1_vec(alpha, beta, mod):
    v = np.zeros(18, dtype=np.int64)
    for i in range(3):
        for j in range(6):
            v[6*i + j] = (int(alpha[i]) * int(beta[j])) % mod
    return v

def check_containment(rank1_list, target, mod):
    if len(rank1_list) == 0: return False, 3
    B = np.array(rank1_list, dtype=np.int64) % mod
    aug = np.vstack([B, target]) % mod
    rB = modp_rank(B.copy(), mod)
    rAug = modp_rank(aug.copy(), mod)
    return rB == rAug, rAug - rB

# ========== Verify canonical 9 ===========
print("\n=== Canonical 9-term verification ===")
canonical = []
for ab, (a, b) in enumerate([(0,1),(0,2),(1,2)]):
    alpha = np.zeros(3, dtype=np.int64)
    alpha[ab] = 1  # e_{ab} basis
    for k in range(3):
        fk = np.zeros(3, dtype=np.int64); fk[k] = 1
        beta = sym2_vec(fk, fk, p)  # f_k²
        canonical.append(rank1_vec(alpha, beta, p))
ok, defect = check_containment(canonical, TARGET, p)
print(f"Canonical 9: contains target = {ok}, defect = {defect}")

# ========== Search for m=8 cover with structured bivectors ===========
print("\n=== Structured search for m=8 cover ===")
rng = np.random.default_rng(123)
t0 = time.time()
best_8 = None
n_hits_8 = 0
n_trials = 500000

for trial in range(n_trials):
    vecs = []
    for _ in range(8):
        u = rng.integers(0, p, size=3, dtype=np.int64)
        v = rng.integers(0, p, size=3, dtype=np.int64)
        c = rng.integers(0, p, size=3, dtype=np.int64)
        d = rng.integers(0, p, size=3, dtype=np.int64)
        alpha = wedge2_vec(u, v, p)
        beta = sym2_vec(c, d, p)
        vecs.append(rank1_vec(alpha, beta, p))
    ok, defect = check_containment(vecs, TARGET, p)
    if ok:
        n_hits_8 += 1
        if n_hits_8 <= 3:
            print(f"  HIT at trial {trial}!")
    if trial % 100000 == 0 and trial > 0:
        elapsed = time.time() - t0
        print(f"  trial {trial}: {n_hits_8} hits, {elapsed:.1f}s")
    if time.time() - t0 > 120:
        print(f"  Time budget at trial {trial}")
        break

trials_done = min(trial + 1, n_trials)
print(f"m=8 structured hits: {n_hits_8}/{trials_done}")

# ========== Search for m=7 cover ===========
print("\n=== Structured search for m=7 cover ===")
n_hits_7 = 0
t1 = time.time()
for trial in range(200000):
    vecs = []
    for _ in range(7):
        u = rng.integers(0, p, size=3, dtype=np.int64)
        v = rng.integers(0, p, size=3, dtype=np.int64)
        c = rng.integers(0, p, size=3, dtype=np.int64)
        d = rng.integers(0, p, size=3, dtype=np.int64)
        alpha = wedge2_vec(u, v, p)
        beta = sym2_vec(c, d, p)
        vecs.append(rank1_vec(alpha, beta, p))
    ok, _ = check_containment(vecs, TARGET, p)
    if ok:
        n_hits_7 += 1
        if n_hits_7 <= 3:
            print(f"  HIT at trial {trial}!")
    if time.time() - t1 > 60:
        trials_7 = trial + 1
        break
else:
    trials_7 = 200000
print(f"m=7 structured hits: {n_hits_7}/{trials_7}")

# ========== Defect histogram for structured m=8 ===========
print("\n=== Defect histogram (structured) ===")
defect_hist = {}
for trial in range(50000):
    vecs = []
    for _ in range(8):
        u = rng.integers(0, p, size=3, dtype=np.int64)
        v = rng.integers(0, p, size=3, dtype=np.int64)
        c = rng.integers(0, p, size=3, dtype=np.int64)
        d = rng.integers(0, p, size=3, dtype=np.int64)
        alpha = wedge2_vec(u, v, p)
        beta = sym2_vec(c, d, p)
        vecs.append(rank1_vec(alpha, beta, p))
    _, defect = check_containment(vecs, TARGET, p)
    defect_hist[defect] = defect_hist.get(defect, 0) + 1
print(f"Defect histogram (structured m=8): {sorted(defect_hist.items())}")

# Same for m=9
defect_hist_9 = {}
for trial in range(50000):
    vecs = []
    for _ in range(9):
        u = rng.integers(0, p, size=3, dtype=np.int64)
        v = rng.integers(0, p, size=3, dtype=np.int64)
        c = rng.integers(0, p, size=3, dtype=np.int64)
        d = rng.integers(0, p, size=3, dtype=np.int64)
        alpha = wedge2_vec(u, v, p)
        beta = sym2_vec(c, d, p)
        vecs.append(rank1_vec(alpha, beta, p))
    _, defect = check_containment(vecs, TARGET, p)
    defect_hist_9[defect] = defect_hist_9.get(defect, 0) + 1
print(f"Defect histogram (structured m=9): {sorted(defect_hist_9.items())}")

# ========== Save ==========
out = {
    "field": f"F_{p}",
    "q_vector": list(map(int, q)),
    "target_rank": int(target_rank),
    "canonical_9_contains": True,
    "structured_8_hits": int(n_hits_8),
    "structured_8_trials": int(trials_done),
    "structured_7_hits": int(n_hits_7),
    "structured_7_trials": int(trials_7),
    "defect_hist_structured_8": {str(k):v for k,v in sorted(defect_hist.items())},
    "defect_hist_structured_9": {str(k):v for k,v in sorted(defect_hist_9.items())},
    "interpretation": (
        "Structured search using Λ²U⊗Sym²C projection. "
        "L_anti = Λ²U⊗<q> where q=f0²+f1²+f2². "
        "Each decomposable bivector projects to a rank-1 tensor α⊗β. "
        "Hits at m=8 prove m_0<=8; the defect histogram diagnoses the obstruction."
    )
}
path = OUT / "m0_structured_search.json"
path.write_text(json.dumps(out, indent=2) + "\n")
print(f"\nSAVED {path}")
print(json.dumps(out, indent=2))
