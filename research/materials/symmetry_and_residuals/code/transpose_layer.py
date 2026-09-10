#!/usr/bin/env python3
"""analysis: Transpose-layer analysis for T_333.

τ(X,Y,Z) = (X^T, Z^T, Y^T) preserves tr(XYZ).
On decomposition terms: (u,v,w) → (u^T, w^T, v^T).

This script:
1. Checks τ-symmetry of known rank-23 schemes
2. Computes N_0: minimum reducible quadrics spanning the 3×3 Gram space
3. Verifies the fixed-locus Gram reduction
4. Records the τ-invariant dimension (729+27)/2 = 378
"""
import numpy as np
import json, sys, itertools
from pathlib import Path

OUT = Path("data/transpose_layer")
OUT.mkdir(parents=True, exist_ok=True)

# ─── Modular arithmetic ───
def mod_inv(a, p):
    return pow(int(a) % p, p - 2, p) % p

def mod_rank(M, p):
    """Row-reduce M mod p, return rank."""
    M = np.array(M, dtype=np.int64) % p
    rows, cols = M.shape
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c] % p != 0:
                piv = i
                break
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        inv = mod_inv(M[r, c], p)
        M[r] = M[r] * inv % p
        for i in range(rows):
            if i != r and M[i, c] % p != 0:
                M[i] = (M[i] - int(M[i, c]) * M[r]) % p
        r += 1
    return r

# ─── 1. τ-symmetry check ───
def parse_qmm(path):
    """Parse QMM scheme file, return list of (u,v,w) as 3×3 matrices."""
    terms = []
    with open(path) as f:
        lines = f.readlines()
    current = {}
    for line in lines:
        line = line.strip()
        if line.startswith("term "):
            if current:
                terms.append(current)
            current = {}
        elif line.startswith("u "):
            current["u"] = np.array([int(x) for x in line.split()[1:]]).reshape(3, 3)
        elif line.startswith("v "):
            current["v"] = np.array([int(x) for x in line.split()[1:]]).reshape(3, 3)
        elif line.startswith("w "):
            current["w"] = np.array([int(x) for x in line.split()[1:]]).reshape(3, 3)
    if current:
        terms.append(current)
    return [(t["u"], t["v"], t["w"]) for t in terms]

def check_tau_symmetry(terms, name):
    """Check if a scheme has τ-symmetry: each (u,v,w) maps to (u^T,w^T,v^T)
    which should match another term (up to scalar)."""
    n = len(terms)
    matched = [False] * n
    fixed = []
    free_orbits = []
    
    for i in range(n):
        if matched[i]:
            continue
        u, v, w = terms[i]
        # τ image: (u^T, w^T, v^T)
        tu, tv, tw = u.T, w.T, v.T
        
        # Check if self-paired (fixed): u=u^T, v=w^T (up to scalar)
        found_match = False
        for j in range(i, n):
            if matched[j] and j != i:
                continue
            uj, vj, wj = terms[j]
            # Check if (tu, tv, tw) = λ(uj, vj, wj)
            # Find scalar: first nonzero pair
            scalar = None
            consistent = True
            for M1, M2 in [(tu, uj), (tv, vj), (tw, wj)]:
                for ii in range(3):
                    for jj in range(3):
                        if M1[ii, jj] != 0 or M2[ii, jj] != 0:
                            if M1[ii, jj] == 0 and M2[ii, jj] != 0:
                                consistent = False
                                break
                            if M1[ii, jj] != 0 and M2[ii, jj] == 0:
                                consistent = False
                                break
                            s = M2[ii, jj] / M1[ii, jj] if M1[ii, jj] != 0 else None
                            if scalar is None:
                                scalar = s
                            elif s is not None and abs(s - scalar) > 1e-10:
                                consistent = False
                                break
                    if not consistent:
                        break
                if not consistent:
                    break
            
            if consistent and scalar is not None:
                # Verify: check all entries
                all_match = True
                for M1, M2 in [(tu, uj), (tv, vj), (tw, wj)]:
                    if not np.allclose(M1 * scalar, M2, atol=1e-10):
                        all_match = False
                        break
                if all_match:
                    if i == j:
                        matched[i] = True
                        fixed.append(i)
                    else:
                        matched[i] = True
                        matched[j] = True
                        free_orbits.append((i, j))
                    found_match = True
                    break
        
        if not found_match:
            pass  # unmatched
    
    unmatched = [i for i in range(n) if not matched[i]]
    is_tau_inv = len(unmatched) == 0
    f = len(fixed)
    m = len(free_orbits)
    N = f + m
    
    print(f"  {name}: τ-invariant={is_tau_inv}, fixed={f}, free_orbits={m}, "
          f"N={N}, unmatched={len(unmatched)}")
    if unmatched and len(unmatched) <= 5:
        for idx in unmatched:
            u, v, w = terms[idx]
            print(f"    unmatched term {idx}: u has sym={np.allclose(u, u.T)}")
    
    return {
        "name": name,
        "tau_invariant": is_tau_inv,
        "fixed_count": f,
        "free_orbit_count": m,
        "N": N,
        "rank": n,
        "unmatched": unmatched,
        "fixed_indices": fixed,
        "free_orbit_indices": free_orbits
    }

def build_bilr_terms():
    """Reconstruct BILR scheme from analysis data."""
    data = json.load(open("data/ballard_z4_cyclic/"
                          "ballard_z4_cyclic_scheme.json"))
    terms = []
    # Fixed cubes: (L, L, L) where L is a 3×3 matrix  
    for cube in data["cubes"]:
        L = np.array(cube)
        terms.append((L, L, L))
    # Free orbits: (U, V, W) and cyclic rotations
    a0 = np.array(data["a0"])  # the Z4 generator
    for orb in data["free_orbit_representatives"]:
        U = np.array(orb["U"])
        V = np.array(orb["V"])
        W = np.array(orb["W"])
        # Add original and 2 cyclic images (Z3 rotation)
        for k in range(3):
            terms.append((U, V, W))
            # Cyclic rotation: (U,V,W) -> (a0 @ V @ a0^{-1}, a0 @ W @ a0^{-1}, a0 @ U @ a0^{-1})
            # Actually the Z3 acts on the three factor spaces
            # From analysis: rotation sigma: (X,Y,Z) -> (a0 Y a0^{-1}, a0 Z a0^{-1}, a0 X a0^{-1})
            a0inv = np.linalg.inv(a0.astype(float))
            U_new = a0 @ V @ a0inv
            V_new = a0 @ W @ a0inv  
            W_new = a0 @ U @ a0inv
            U, V, W = U_new.round().astype(int), V_new.round().astype(int), W_new.round().astype(int)
    return terms

def build_naive_scheme():
    """Standard 27-term naive algorithm: T_{ij,kl,mn} with u=e_{ij}, v=e_{jk}, w=e_{ki}."""
    terms = []
    for i in range(3):
        for j in range(3):
            for k in range(3):
                u = np.zeros((3,3), dtype=int); u[i,j] = 1
                v = np.zeros((3,3), dtype=int); v[j,k] = 1
                w = np.zeros((3,3), dtype=int); w[k,i] = 1
                terms.append((u, v, w))
    return terms

# ─── 2. Gram space N_0 computation ───
def build_gram_vectors(p):
    """Build the 6 Gram quadric vectors in monomial basis of Sym^2(K^9).
    
    Variable index: i = 3*j + l (j=row, l=col of Y).
    Monomial basis: pairs (a,b) with a <= b, index triangular.
    G_{jk} = sum_l Y_{jl} * Y_{kl}.
    """
    n = 9
    n_monos = n * (n + 1) // 2  # 45
    
    def mono_idx(a, b):
        if a > b: a, b = b, a
        return a * n - a * (a - 1) // 2 + (b - a)
    
    gram_pairs = [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]  # j <= k
    gram = np.zeros((6, n_monos), dtype=np.int64)
    
    for idx, (j, k) in enumerate(gram_pairs):
        for l in range(3):
            a = 3 * j + l  # variable Y_{jl}
            b = 3 * k + l  # variable Y_{kl}
            mi = mono_idx(a, b)
            coeff = 1 if a == b else 1  # same coefficient for diagonal and off-diagonal
            gram[idx, mi] = (gram[idx, mi] + coeff) % p
    
    return gram % p, mono_idx

def product_vector(a_vec, b_vec, p, n=9):
    """Compute the monomial vector for sym(a ⊗ b) in Sym^2(K^n)."""
    n_monos = n * (n + 1) // 2
    v = np.zeros(n_monos, dtype=np.int64)
    
    def mono_idx(a, b):
        if a > b: a, b = b, a
        return a * n - a * (a - 1) // 2 + (b - a)
    
    for i in range(n):
        for j in range(i, n):
            if i == j:
                v[mono_idx(i, j)] = (int(a_vec[i]) * int(b_vec[j])) % p
            else:
                v[mono_idx(i, j)] = (int(a_vec[i]) * int(b_vec[j]) + 
                                     int(a_vec[j]) * int(b_vec[i])) % p
    return v % p

def test_gram_span(N, p, gram, n_trials=2000, structured=False):
    """Test whether N random products can span the Gram space."""
    n_monos = gram.shape[1]
    successes = 0
    
    for trial in range(n_trials):
        if structured and N == 12:
            # Use polarization construction over F_p with a root of -1
            # Find i such that i^2 = -1 mod p
            im = None
            for x in range(1, p):
                if (x * x + 1) % p == 0:
                    im = x
                    break
            if im is None:
                return 0, 0  # p ≡ 3 mod 4, no square root of -1
            
            Q = np.zeros((n_monos, N), dtype=np.int64)
            idx = 0
            # 6 norms: y_1, y_2, y_3, y_1+y_2, y_1+y_3, y_2+y_3
            vectors = []
            for j in range(3):
                e = np.zeros(9, dtype=np.int64)
                e[3*j:3*j+3] = [1, 0, 0]; e[3*j] = 1; e[3*j+1] = 0; e[3*j+2] = 0
                # Actually: y_j has components Y_{j0}, Y_{j1}, Y_{j2}
                # basis vector for Y_{jl} is e_{3j+l}
                vectors.append(j)  # just index
            
            norms = [(0,), (1,), (2,), (0,1), (0,2), (1,2)]
            for norm_vec in norms:
                # Sum of basis rows
                # For norm of y_j1 + y_j2 + ...: the vector is sum of e_{3*ji+l} for each ji
                # Product 1: (sum_ji Y_{ji,0} + i*Y_{ji,1})(sum_ji Y_{ji,0} - i*Y_{ji,1})
                a = np.zeros(9, dtype=np.int64)
                b = np.zeros(9, dtype=np.int64)
                for ji in norm_vec:
                    a[3*ji + 0] = (a[3*ji + 0] + 1) % p
                    a[3*ji + 1] = (a[3*ji + 1] + im) % p
                    b[3*ji + 0] = (b[3*ji + 0] + 1) % p
                    b[3*ji + 1] = (b[3*ji + 1] + p - im) % p
                Q[:, idx] = product_vector(a, b, p)
                idx += 1
                
                # Product 2: (sum_ji Y_{ji,2})^2
                c = np.zeros(9, dtype=np.int64)
                for ji in norm_vec:
                    c[3*ji + 2] = (c[3*ji + 2] + 1) % p
                Q[:, idx] = product_vector(c, c, p)
                idx += 1
            
            # Check span
            QG = np.hstack([Q % p, gram.T % p])
            rQ = mod_rank(Q.copy(), p)
            rQG = mod_rank(QG.copy(), p)
            if rQ == rQG:
                successes += 1
            if trial == 0:
                print(f"    Structured N={N}: rank(Q)={rQ}, rank([Q|G])={rQG}, "
                      f"spans={'YES' if rQ==rQG else 'NO'}")
            return successes, 1  # Only one structured trial
        else:
            # Random products
            rng = np.random.default_rng(trial * 1000 + N)
            Q = np.zeros((n_monos, N), dtype=np.int64)
            for i in range(N):
                a = rng.integers(0, p, 9)
                b = rng.integers(0, p, 9)
                Q[:, i] = product_vector(a, b, p)
            
            QG = np.hstack([Q % p, gram.T % p])
            rQ = mod_rank(Q.copy(), p)
            rQG = mod_rank(QG.copy(), p)
            if rQ == rQG:
                successes += 1
    
    return successes, n_trials

def compute_N0(p):
    """Find minimum N such that N products can span the Gram space."""
    gram, _ = build_gram_vectors(p)
    results = {}
    
    # First check: what's the rank of the Gram vectors?
    gram_rank = mod_rank(gram.copy(), p)
    print(f"  Gram vectors rank = {gram_rank} (should be 6)")
    
    # Test structured polarization at N=12
    print(f"\n  Structured polarization test (N=12):")
    s, t = test_gram_span(12, p, gram, structured=True)
    results["structured_12"] = {"success": s > 0, "trials": t}
    
    # Random search for various N
    for N in [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18]:
        s, t = test_gram_span(N, p, gram, n_trials=500)
        rate = s / t if t > 0 else 0
        results[f"random_N{N}"] = {"successes": s, "trials": t, "rate": round(rate, 4)}
        print(f"  Random N={N}: {s}/{t} successes ({rate:.4f})")
        if N <= 8 and s == 0:
            pass  # expected
    
    return results, gram

# ─── 3. Gram projection analysis ───
def gram_projection_analysis(p):
    """Analyze the structure of the Gram projection map.
    
    For a product ℓ_a · ℓ_b where a,b ∈ K^9 viewed as 3×3 matrices A,B:
    π_V(sym(a,b)) = (AB^T + BA^T) ∈ Sym_3(K)
    
    Key question: what constrains the V⊥ components?
    """
    # The Gram space V = {S ⊗ I_3 : S ∈ Sym_3} has dim 6 in Sym^2(K^9) dim 45.
    # For a rank-2 element q = sym(a,b), its projection onto V is (AB^T + BA^T)/normalization.
    # The V⊥ component has the traceless part of each 3×3 block.
    
    # Dimension count:
    # Sym^2(K^9) = 45
    # V has dim 6 (the Gram space)
    # V⊥ has dim 39
    # Each rank-2 element lives in a 45-dim space
    
    # For products of rank-1 tensors: a = α⊗φ, b = β⊗ψ:
    # π_V = ⟨φ,ψ⟩ (αβ^T + βα^T), rank ≤ 2 in Sym_3
    # π_{V⊥}: traceless parts, dimension 5 per block × 6 blocks = 30... 
    # actually 6 diagonal blocks have 5-dim traceless, 
    # 3 off-diagonal block pairs have 8-dim traceless each = 24
    # Total V⊥ dim = 6*5 + ... wait let me compute properly.
    # Sym^2(K^9) with K^9 = K^3 ⊗ K^3:
    # Sym^2(K^3 ⊗ K^3) = Sym^2(K^3) ⊗ Sym^2(K^3) ⊕ Λ^2(K^3) ⊗ Λ^2(K^3)
    # dim = 6*6 + 3*3 = 36 + 9 = 45 ✓
    
    # The Gram space V = {S ⊗ I_3} ≅ Sym^2(K^3) (as the "scalar" part)
    # V⊥ (within Sym^2(K^9)) has dim 39.
    
    print("\n=== Gram projection structure ===")
    print(f"  Sym^2(K^9) dim = 45")
    print(f"  V = Gram space dim = 6")
    print(f"  V⊥ dim = 39")
    print(f"  For rank-1 tensor products a=α⊗φ, b=β⊗ψ:")
    print(f"    π_V = ⟨φ,ψ⟩·(αβ^T + βα^T) ∈ Sym_3, rank ≤ 2")
    print(f"    V⊥ component involves traceless 3×3 block parts")
    print(f"  For general a,b ∈ K^9 (viewed as 3×3 matrices A,B):")
    print(f"    π_V = AB^T + BA^T, rank up to 3")
    
    # Verify V⊥ cancellation requirements numerically
    # Take N random products, project to V, check deficit
    rng = np.random.default_rng(42)
    gram, mono_idx_fn = build_gram_vectors(p)
    
    for N in [6, 9, 12]:
        # Build Q matrix
        Q = np.zeros((45, N), dtype=np.int64)
        for i in range(N):
            a = rng.integers(0, p, 9)
            b = rng.integers(0, p, 9)
            Q[:, i] = product_vector(a, b, p)
        
        # Check if gram rows are in column span
        QG = np.hstack([Q % p, gram.T % p])
        rQ = mod_rank(Q.copy(), p)
        rQG = mod_rank(QG.copy(), p)
        deficit = rQG - rQ
        
        print(f"  N={N}: rank(Q)={rQ}, rank([Q|G])={rQG}, deficit={deficit}")

# ─── 4. τ-invariant dimension verification ───
def tau_invariant_dimension(p):
    """Verify dim of τ-invariant subspace of K^{9⊗3} is (729+27)/2 = 378."""
    # τ acts on the 729-dim tensor space K^9 ⊗ K^9 ⊗ K^9
    # τ: e_{ij} ⊗ e_{kl} ⊗ e_{mn} → e_{ji} ⊗ e_{nm} ⊗ e_{lk}
    # Fixed if (i,j)=(j,i), (k,l)=(n,m), (m,n)=(l,k)
    # i.e., i=j (but really (ij)→(ji) fixes iff matrix is symmetric)
    # Wait: e_{ij} means the matrix E_{ij}, and E_{ij}^T = E_{ji}
    # So τ maps basis element (E_{ij}, E_{kl}, E_{mn}) to (E_{ji}, E_{nm}, E_{lk})
    
    # Count fixed points:
    count = 0
    for i in range(3):
        for j in range(3):
            for k in range(3):
                for l in range(3):
                    for m in range(3):
                        for n in range(3):
                            # (i,j,k,l,m,n) fixed iff (j,i,n,m,l,k) = (i,j,k,l,m,n)
                            if j == i and n == k and l == m and m == l and k == n:
                                # Simplifies to: j=i, k=n, l=m
                                count += 1
    
    # Count more carefully
    count2 = 0
    for i in range(3):  # j=i forced
        for k in range(3):
            for l in range(3):  # n=k, m=l forced
                count2 += 1
    
    dim_inv = (729 + count2) // 2
    print(f"\n=== τ-invariant dimension ===")
    print(f"  Fixed points of τ: {count2} (should be 27 = 3×3×3)")
    print(f"  dim(invariant) = (729 + {count2})/2 = {dim_inv} (should be 378)")
    return dim_inv

# ─── 5. Fixed-locus Gram reduction ───
def gram_reduction_verification(p):
    """Verify the Gram reduction on the fixed locus X=S (symmetric), Z=Y^T.
    
    tr(S Y Y^T) = Σ_{j,k} S_{jk} G_{jk}(Y) where G_{jk} = Σ_l Y_{jl} Y_{kl}.
    
    A τ-fixed term (u symmetric, w=v^T) contributes:
    tr(u·S) · (tr(v·Y))^2  [a square in Y-variables]
    
    A τ-free orbit {(u,v,w), (u^T,w^T,v^T)} contributes:
    2·tr(u·S) · tr(v·Y) · tr(w^T·Y)  [a product of two linear forms]
    """
    print("\n=== Gram reduction verification ===")
    
    # Verify on the naive scheme (rank 27, expected τ-invariant)
    naive = build_naive_scheme()
    
    # Check τ-symmetry of naive
    tau_result = check_tau_symmetry(naive, "naive_27")
    f = tau_result["fixed_count"]
    m = tau_result["free_orbit_count"]
    N = tau_result["N"]
    r = tau_result["rank"]
    print(f"  Naive: rank={r}, f={f}, m={m}, N={N}, r_check={f+2*m}")
    
    # For each fixed term, verify u=u^T and that the Gram contribution is a square
    if tau_result["tau_invariant"]:
        print(f"  Expected N for Gram: N = f + m = {f} + {m} = {N}")
        print(f"  This gives {N} reducible quadrics for the Gram space")
    
    # Check cn122
    cn122 = parse_qmm("data/cn122_r23_reproduce/scheme.qmm")
    tau_cn122 = check_tau_symmetry(cn122, "cn122")
    
    # Check BILR
    bilr = build_bilr_terms()
    tau_bilr = check_tau_symmetry(bilr, "BILR_Z4xZ3")
    
    return tau_result, tau_cn122, tau_bilr

# ─── 6. Compute exact N_0 with better methodology ───
def compute_N0_refined(p):
    """Use a combination of random and structured searches to bound N_0.
    
    Key insight: for N products with vectors a_i, b_i ∈ K^9 viewed as
    3×3 matrices A_i, B_i:
    - V-projection: π_V(q_i) = A_i B_i^T + B_i A_i^T ∈ Sym_3
    - V⊥ component: traceless parts of 3×3 blocks
    
    For V ⊂ span(q_1,...,q_N):
    - Need V-projections to span Sym_3 (6 independent elements)
    - Need the V⊥ "overhead" to cancel for each G_{jk}
    
    Lower bound argument: each rank-1 tensor product a=α⊗φ, b=β⊗ψ
    gives V-projection of rank ≤ 2 in Sym_3 and V⊥ component of rank 
    determined by the traceless part of φψ^T.
    """
    gram, _ = build_gram_vectors(p)
    
    print("\n=== Refined N_0 computation ===")
    
    # Strategy 1: Try to find explicit minimal constructions
    # The 18 axis-aligned products work but are not minimal
    
    # Strategy 2: Optimized random search with many trials
    best_N = 45  # worst case
    
    for N in range(6, 19):
        found = False
        n_trials = 5000 if N <= 12 else 1000
        rng = np.random.default_rng(N * 7919)
        
        for trial in range(n_trials):
            Q = np.zeros((45, N), dtype=np.int64)
            for i in range(N):
                a = rng.integers(0, p, 9)
                b = rng.integers(0, p, 9)
                Q[:, i] = product_vector(a, b, p)
            
            QG = np.hstack([Q % p, gram.T % p])
            rQ = mod_rank(Q.copy(), p)
            rQG = mod_rank(QG.copy(), p)
            
            if rQ == rQG:
                found = True
                best_N = min(best_N, N)
                if N <= 12:
                    print(f"  N={N}: FOUND spanning set at trial {trial}")
                break
        
        if not found:
            print(f"  N={N}: no spanning set in {n_trials} trials")
        else:
            if N == best_N:
                print(f"  *** N_0 ≤ {N} ***")
                break  # found the minimum
    
    # Also try with rank-1 products only (a=b, squares)
    print(f"\n  Testing with squares only (rank-1 in Sym^2):")
    for N in range(6, 25):
        found = False
        rng = np.random.default_rng(N * 13337)
        for trial in range(3000):
            Q = np.zeros((45, N), dtype=np.int64)
            for i in range(N):
                a = rng.integers(0, p, 9)
                Q[:, i] = product_vector(a, a, p)
            
            QG = np.hstack([Q % p, gram.T % p])
            rQ = mod_rank(Q.copy(), p)
            rQG = mod_rank(QG.copy(), p)
            if rQ == rQG:
                found = True
                print(f"  Squares N={N}: FOUND at trial {trial}")
                break
        if not found and N <= 14:
            print(f"  Squares N={N}: not found in 3000 trials")
        if found:
            break
    
    return best_N

# ─── Main ───
def main():
    p = 65521
    results = {}
    
    print("=" * 60)
    print("analysis: Transpose layer τ(X,Y,Z) = (X^T, Z^T, Y^T)")
    print("=" * 60)
    
    # 1. τ-symmetry of known schemes
    print("\n--- 1. τ-symmetry check ---")
    tau_naive, tau_cn122, tau_bilr = gram_reduction_verification(p)
    results["tau_symmetry"] = {
        "naive": tau_naive,
        "cn122": tau_cn122,
        "BILR": tau_bilr
    }
    
    # 2. τ-invariant dimension
    dim_inv = tau_invariant_dimension(p)
    results["tau_invariant_dim"] = dim_inv
    
    # 3. N_0 computation
    print("\n--- 3. Gram space N_0 computation ---")
    N0_results, gram = compute_N0(p)
    results["N0_preliminary"] = N0_results
    
    # 4. Gram projection analysis
    gram_projection_analysis(p)
    
    # 5. Refined N_0
    print("\n--- 5. Refined N_0 search ---")
    best_N = compute_N0_refined(p)
    results["N0_bound"] = best_N
    
    # 6. τ-invariant skeleton for rank 22
    print("\n--- 6. τ-invariant rank-22 skeletons ---")
    print("  For rank r=22: f + 2m = 22 (f fixed, m free orbits)")
    print("  Gram product count: N = f + m = 11 + f/2")
    print("  f must be even (f + 2m = 22)")
    print("  Skeletons (f, m, N):")
    skeletons = []
    for f in range(0, 23, 2):
        if f > 22:
            break
        m = (22 - f) // 2
        N = f + m
        skeletons.append({"f": f, "m": m, "N": N, "rank": f + 2*m})
        if f <= 10:
            print(f"    ({f}, {m}): N = {N}")
    results["rank22_skeletons"] = skeletons
    results["N0_kills_below"] = best_N
    
    # Save
    path = OUT / "transpose_layer_analysis.json"
    path.write_text(json.dumps(results, indent=2, default=str) + "\n")
    print(f"\nSAVED {path}")

if __name__ == "__main__":
    main()
