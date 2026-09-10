#!/usr/bin/env python3
"""analysisb: Compute N_0 for the Gram space — minimum number of 
products of linear forms spanning the 6-dim Gram subspace of Sym^2(K^9).

G_{jk}(Y) = Σ_l Y_{jl}·Y_{kl}  for 0 ≤ j ≤ k ≤ 2.

These are 6 quadratic forms in 9 variables, each of rank 3 as a 
symmetric bilinear form. We seek the minimum N such that N products 
ℓ_i·m_i of linear forms span a subspace containing all 6.
"""
import numpy as np, json, sys
from pathlib import Path

OUT = Path("data/transpose_layer")
OUT.mkdir(parents=True, exist_ok=True)

def mod_inv(a, p):
    return pow(int(a) % p, p - 2, p) % p

def mod_rank(M, p):
    M = np.array(M, dtype=np.int64) % p
    rows, cols = M.shape
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c] % p != 0:
                piv = i; break
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]
        inv = mod_inv(M[r, c], p)
        M[r] = M[r] * inv % p
        for i in range(rows):
            if i != r and M[i, c] % p != 0:
                M[i] = (M[i] - int(M[i, c]) * M[r]) % p
        r += 1
    return r

def mono_idx(a, b, n=9):
    if a > b: a, b = b, a
    return a * n - a * (a - 1) // 2 + (b - a)

N_MONOS = 45  # dim Sym^2(K^9)

def build_gram(p):
    """Build 6×45 matrix of Gram quadrics mod p."""
    gram = np.zeros((6, N_MONOS), dtype=np.int64)
    pairs = [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]
    for idx, (j, k) in enumerate(pairs):
        for l in range(3):
            a = 3*j + l
            b = 3*k + l
            mi = mono_idx(a, b)
            gram[idx, mi] = (gram[idx, mi] + 1) % p
    return gram

def product_vec(a, b, p):
    """Sym^2 product vector for linear forms a, b ∈ K^9."""
    v = np.zeros(N_MONOS, dtype=np.int64)
    for i in range(9):
        for j in range(i, 9):
            if i == j:
                v[mono_idx(i, j)] = (int(a[i]) * int(b[j])) % p
            else:
                v[mono_idx(i, j)] = (int(a[i]) * int(b[j]) + int(a[j]) * int(b[i])) % p
    return v % p

def test_N(N, p, gram, n_trials=2000, seed=0):
    """Test N random products over F_p. Return number of successes."""
    rng = np.random.default_rng(seed)
    succ = 0
    for t in range(n_trials):
        Q = np.zeros((N_MONOS, N), dtype=np.int64)
        for i in range(N):
            a = rng.integers(0, p, 9)
            b = rng.integers(0, p, 9)
            Q[:, i] = product_vec(a, b, p)
        QG = np.hstack([Q % p, gram.T % p])
        if mod_rank(Q.copy(), p) == mod_rank(QG.copy(), p):
            succ += 1
    return succ

def test_structured(N, p, gram):
    """Test specific constructions for N=12 (polarization) and N=9."""
    # Find sqrt(-1) mod p
    im = None
    for x in range(1, min(p, 100000)):
        if (x*x + 1) % p == 0:
            im = x; break
    
    results = {}
    
    if im is not None and N == 12:
        # Polarization: 6 norms × 2 products each
        Q = np.zeros((N_MONOS, 12), dtype=np.int64)
        idx = 0
        norms = [(0,), (1,), (2,), (0,1), (0,2), (1,2)]
        for nv in norms:
            a = np.zeros(9, dtype=np.int64)
            b = np.zeros(9, dtype=np.int64)
            c = np.zeros(9, dtype=np.int64)
            for ji in nv:
                a[3*ji] = (a[3*ji] + 1) % p
                a[3*ji+1] = (a[3*ji+1] + im) % p
                b[3*ji] = (b[3*ji] + 1) % p
                b[3*ji+1] = (b[3*ji+1] + p - im) % p
                c[3*ji+2] = (c[3*ji+2] + 1) % p
            Q[:, idx] = product_vec(a, b, p); idx += 1
            Q[:, idx] = product_vec(c, c, p); idx += 1
        
        QG = np.hstack([Q % p, gram.T % p])
        rQ = mod_rank(Q.copy(), p)
        rQG = mod_rank(QG.copy(), p)
        results["polarization_12"] = {"rank_Q": rQ, "rank_QG": rQG, 
                                       "spans": rQ == rQG}
        print(f"  Polarization N=12: rank(Q)={rQ}, rank([Q|G])={rQG}, "
              f"spans={'YES' if rQ==rQG else 'NO'}")
    
    if N == 9:
        # Try column-grouped: for each column l, use 3 products covering 
        # the 3 pairs (j,k) within that column. 3 columns × 3 = 9.
        Q = np.zeros((N_MONOS, 9), dtype=np.int64)
        idx = 0
        for l in range(3):
            for j in range(3):
                # Product: Y_{jl} · (Y_{0l} + Y_{1l} + Y_{2l})
                a = np.zeros(9, dtype=np.int64); a[3*j+l] = 1
                b = np.zeros(9, dtype=np.int64)
                for k in range(3): b[3*k+l] = 1
                Q[:, idx] = product_vec(a, b, p); idx += 1
        QG = np.hstack([Q % p, gram.T % p])
        rQ = mod_rank(Q.copy(), p)
        rQG = mod_rank(QG.copy(), p)
        results["column_9"] = {"rank_Q": rQ, "rank_QG": rQG, "spans": rQ == rQG}
        print(f"  Column-grouped N=9: rank(Q)={rQ}, rank([Q|G])={rQG}, "
              f"spans={'YES' if rQ==rQG else 'NO'}")
    
    return results

def main():
    p = 65521
    gram = build_gram(p)
    rg = mod_rank(gram.copy(), p)
    print(f"Gram space rank = {rg} (should be 6)")
    
    results = {"prime": p, "gram_rank": rg}
    
    # Quick scan: for each N from 6 to 18, run 500 random trials
    print("\n=== Random product search ===")
    for N in range(6, 19):
        nt = 1000 if N <= 12 else 300
        s = test_N(N, p, gram, n_trials=nt, seed=N*31337)
        rate = s/nt
        results[f"N{N}"] = {"successes": s, "trials": nt, "rate": round(rate, 6)}
        tag = " ***" if s > 0 and all(results.get(f"N{n}", {}).get("successes", 0) == 0 
                                       for n in range(6, N)) else ""
        print(f"  N={N}: {s}/{nt} ({rate:.4f}){tag}")
        if N >= 14 and s > 0:
            break  # clearly above threshold
    
    # Structured tests
    print("\n=== Structured constructions ===")
    struct = test_structured(12, p, gram)
    struct.update(test_structured(9, p, gram))
    results["structured"] = struct
    
    # Second prime for consistency
    p2 = 32003
    gram2 = build_gram(p2)
    print(f"\n=== Verification at p={p2} ===")
    for N in [9, 10, 11, 12]:
        s = test_N(N, p2, gram2, n_trials=500, seed=N*99991)
        print(f"  N={N}: {s}/500")
        results[f"N{N}_p{p2}"] = {"successes": s, "trials": 500}
    
    # Minimum N_0 conclusion
    min_N = None
    for N in range(6, 19):
        k = f"N{N}"
        if k in results and results[k]["successes"] > 0:
            min_N = N; break
    
    results["N0_upper_bound"] = min_N
    print(f"\n*** N_0 ≤ {min_N} ***")
    
    # If N_0 is small, check implications for rank-22 skeletons
    if min_N:
        print(f"\nRank-22 τ-invariant skeleton analysis:")
        print(f"  Need N = f + m ≥ {min_N} where f + 2m = 22")
        killed = []
        alive = []
        for f in range(0, 23, 2):
            m = (22 - f) // 2
            N = f + m
            if N < min_N:
                killed.append((f, m, N))
                print(f"    ({f},{m}): N={N} < {min_N} → KILLED")
            else:
                alive.append((f, m, N))
                if f <= 12:
                    print(f"    ({f},{m}): N={N} ≥ {min_N} → alive")
        results["rank22_killed"] = killed
        results["rank22_alive"] = alive
    
    path = OUT / "gram_N0_computation.json"
    path.write_text(json.dumps(results, indent=2, default=float) + "\n")
    print(f"\nSAVED {path}")

if __name__ == "__main__":
    main()
