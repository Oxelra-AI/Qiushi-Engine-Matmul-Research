#!/usr/bin/env python3
"""
Comprehensive analysis of the E11 quotient core of T_<3,3,3> over F_2.

Computes:
  1. Full 3x3 matrix multiplication tensor over F_2
  2. E11 core slices and M_0 (deleted slice)
  3. Flattening ranks (all three modes)
  4. Rank-23 scheme analysis reduced to F_2
  5. Rank-one cover structure for core slices
  6. Residual rank condition analysis

Convention: e_{ij} -> index 3*(i-1) + (j-1), so e_{11}=0, e_{12}=1, ..., e_{33}=8
"""

import numpy as np
import json
import os
import sys

# ---- F_2 linear algebra utilities ----

def f2_rank(mat):
    """Rank of a binary matrix over F_2 via Gauss elimination."""
    M = np.array(mat, dtype=int) % 2
    rows, cols = M.shape
    r = 0
    for col in range(cols):
        pivot = None
        for row in range(r, rows):
            if M[row, col] == 1:
                pivot = row
                break
        if pivot is None:
            continue
        M[[r, pivot]] = M[[pivot, r]]
        for row in range(rows):
            if row != r and M[row, col] == 1:
                M[row] = (M[row] + M[r]) % 2
        r += 1
    return r

def f2_nullspace(mat):
    """Nullspace of a binary matrix over F_2. Returns generator matrix."""
    M = np.array(mat, dtype=int) % 2
    rows, cols = M.shape
    # Augment with identity
    aug = np.hstack([M.T, np.eye(cols, dtype=int)])  # cols x (rows+cols)
    # Row reduce
    r = 0
    for col in range(rows):
        pivot = None
        for row in range(r, cols):
            if aug[row, col] == 1:
                pivot = row
                break
        if pivot is None:
            continue
        aug[[r, pivot]] = aug[[pivot, r]]
        for row in range(cols):
            if row != r and aug[row, col] == 1:
                aug[row] = (aug[row] + aug[r]) % 2
        r += 1
    # Null vectors are rows with zero left part
    null_vecs = []
    for row in range(r, cols):
        if np.all(aug[row, :rows] == 0):
            null_vecs.append(aug[row, rows:] % 2)
    return np.array(null_vecs, dtype=int) if null_vecs else np.zeros((0, cols), dtype=int)


# ---- Tensor construction ----

def build_matmul_tensor():
    """Build T_<3,3,3> over F_2 as 9x9x9 binary tensor.
    T[a,b,c] = 1 iff (a=e_{ik}, b=e_{kj}, c=e_{ij}) for some i,j,k in {1,2,3}.
    """
    T = np.zeros((9, 9, 9), dtype=int)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a_idx = 3*i + k
                b_idx = 3*k + j
                c_idx = 3*i + j
                T[a_idx, b_idx, c_idx] = 1
    return T

def idx_to_label(idx):
    """Convert index 0-8 to e_{ij} label."""
    i = idx // 3 + 1
    j = idx % 3 + 1
    return f"e_{{{i}{j}}}"

def extract_core_and_slice(T):
    """Extract E11 core (8x9x9) and M_0 (9x9)."""
    M0 = T[0, :, :]   # E11 slice
    T_core = T[1:, :, :]  # core (projecting out e_{11} direction)
    return T_core, M0


# ---- Flattening analysis ----

def compute_flattenings(T_core, label="core"):
    """Compute flattening ranks of the core tensor."""
    shape = T_core.shape
    # A-flattening: shape[0] x (shape[1]*shape[2])
    A_flat = T_core.reshape(shape[0], shape[1]*shape[2])
    # B-flattening: shape[1] x (shape[0]*shape[2])  
    B_flat = T_core.transpose(1, 0, 2).reshape(shape[1], shape[0]*shape[2])
    # C-flattening: shape[2] x (shape[0]*shape[1])
    C_flat = T_core.transpose(2, 0, 1).reshape(shape[2], shape[0]*shape[1])
    
    rA = f2_rank(A_flat)
    rB = f2_rank(B_flat)
    rC = f2_rank(C_flat)
    
    print(f"\n=== Flattening ranks of {label} (shape {shape}) ===")
    print(f"  A-flattening ({shape[0]}x{shape[1]*shape[2]}): rank = {rA}")
    print(f"  B-flattening ({shape[1]}x{shape[0]*shape[2]}): rank = {rB}")
    print(f"  C-flattening ({shape[2]}x{shape[0]*shape[1]}): rank = {rC}")
    print(f"  Max flattening rank (tensor rank lower bound): {max(rA, rB, rC)}")
    
    return {"A_rank": rA, "B_rank": rB, "C_rank": rC, "max": max(rA, rB, rC)}


# ---- Core slice analysis ----

def analyze_core_slices(T_core, M0):
    """Analyze the 8 core slices and M_0."""
    labels_core = [idx_to_label(i+1) for i in range(8)]  # indices 1-8 in original
    # Actually the core A-indices correspond to original indices 1..8
    # which are e_{12}, e_{13}, e_{21}, e_{22}, e_{23}, e_{31}, e_{32}, e_{33}
    
    print("\n=== Core slice analysis ===")
    print(f"M_0 (E11 slice): rank = {f2_rank(M0)}")
    print(f"  Nonzero entries: ", end="")
    for r in range(9):
        for c in range(9):
            if M0[r,c] == 1:
                print(f"({idx_to_label(r)},{idx_to_label(c)})", end=" ")
    print()
    
    slice_info = []
    for s in range(8):
        S = T_core[s, :, :]
        rk = f2_rank(S)
        nz = []
        for r in range(9):
            for c in range(9):
                if S[r,c] == 1:
                    nz.append((r,c))
        print(f"  Slice {labels_core[s]} (A-core idx {s}): rank={rk}, "
              f"nonzero={([(idx_to_label(r),idx_to_label(c)) for r,c in nz])}")
        slice_info.append({"label": labels_core[s], "rank": rk, "nonzero_count": len(nz)})
    
    # Check pairwise overlap of nonzero entries
    print("\n  Pairwise nonzero overlaps between core slices:")
    overlap_count = 0
    for s1 in range(8):
        for s2 in range(s1+1, 8):
            ov = np.sum((T_core[s1] * T_core[s2]) % 2)
            if ov > 0:
                print(f"    {labels_core[s1]} ∩ {labels_core[s2]}: {ov} shared entries")
                overlap_count += 1
    if overlap_count == 0:
        print("    No overlaps — all 8 core slices have disjoint support.")
    
    # Check overlap of M_0 with core slices
    print("\n  M_0 overlaps with core slices:")
    m0_overlap = 0
    for s in range(8):
        ov = np.sum((M0 * T_core[s]) % 2)
        if ov > 0:
            print(f"    M_0 ∩ {labels_core[s]}: {ov}")
            m0_overlap += 1
    if m0_overlap == 0:
        print("    No overlaps — M_0 is disjoint from all core slices.")
    
    return slice_info


# ---- Rank-23 scheme analysis over F_2 ----

def parse_qmm_scheme(filepath):
    """Parse a QMM scheme file and return list of (u, v, w) integer vectors."""
    terms = []
    current_term = {}
    with open(filepath) as f:
        for line in f:
            line = line.strip()
            if line.startswith('term'):
                if current_term:
                    terms.append(current_term)
                current_term = {}
            elif line.startswith('u '):
                current_term['u'] = list(map(int, line.split()[1:]))
            elif line.startswith('v '):
                current_term['v'] = list(map(int, line.split()[1:]))
            elif line.startswith('w '):
                current_term['w'] = list(map(int, line.split()[1:]))
    if current_term:
        terms.append(current_term)
    return terms

def analyze_rank23_mod2(scheme_path):
    """Reduce rank-23 scheme to F_2 and analyze E11 core structure."""
    terms = parse_qmm_scheme(scheme_path)
    print(f"\n=== Rank-23 scheme analysis over F_2 ({len(terms)} terms) ===")
    
    # Reduce mod 2
    f2_terms = []
    for i, term in enumerate(terms):
        u2 = [abs(x) % 2 for x in term['u']]
        v2 = [abs(x) % 2 for x in term['v']]
        w2 = [abs(x) % 2 for x in term['w']]
        f2_terms.append({'u': u2, 'v': v2, 'w': w2})
    
    # Check for zero terms
    zero_terms = []
    nonzero_terms = []
    for i, t in enumerate(f2_terms):
        if all(x == 0 for x in t['u']) or all(x == 0 for x in t['v']) or all(x == 0 for x in t['w']):
            zero_terms.append(i)
        else:
            nonzero_terms.append(i)
    
    print(f"  Nonzero terms over F_2: {len(nonzero_terms)}")
    print(f"  Zero terms over F_2: {len(zero_terms)} (indices: {zero_terms})")
    
    # Check if these terms actually reconstruct T over F_2
    T_check = np.zeros((9, 9, 9), dtype=int)
    for t in f2_terms:
        u = np.array(t['u'])
        v = np.array(t['v'])
        w = np.array(t['w'])
        T_check = (T_check + np.einsum('i,j,k->ijk', u, v, w)) % 2
    
    T_real = build_matmul_tensor()
    match = np.all(T_check == T_real)
    print(f"  Reconstruction check (T_check == T): {match}")
    
    if not match:
        diff = np.sum(np.abs(T_check - T_real))
        print(f"  WARNING: {diff} differing entries!")
    
    # E11 core analysis: for each F_2 nonzero term, check A-direction
    print("\n  E11 core structure of nonzero F_2 terms:")
    e11_terms = []  # terms with A = e_{11} (only index 0 is 1)
    core_terms = []  # terms with nonzero A-projection
    for i in nonzero_terms:
        u = f2_terms[i]['u']
        if u[0] == 1:  # has e_{11} component
            projected_u = u[1:]  # project out e_{11}
            if all(x == 0 for x in projected_u):
                e11_terms.append(i)
                print(f"    Term {i}: A = e_{{11}} (pure E11 direction)")
            else:
                core_terms.append(i)
                wt = sum(projected_u)
                print(f"    Term {i}: A = e_{{11}} + (wt-{wt} core), proj_A = {projected_u}")
        else:
            core_terms.append(i)
            proj = u[1:]
            wt = sum(proj)
            print(f"    Term {i}: A = (wt-{wt} core), no e_{{11}}, proj_A = {u[1:]}")
    
    print(f"\n  Pure E11 terms: {len(e11_terms)}")
    print(f"  Core-contributing terms: {len(core_terms)}")
    print(f"  Total terms for core decomposition: {len(core_terms)}")
    
    # For core-contributing terms, compute the residual
    if nonzero_terms:
        # Compute what the core decomposition gives
        T_core_from_scheme = np.zeros((8, 9, 9), dtype=int)
        for i in core_terms:
            u = np.array(f2_terms[i]['u'])
            v = np.array(f2_terms[i]['v'])
            w = np.array(f2_terms[i]['w'])
            proj_u = u[1:]  # 8-dimensional
            T_core_from_scheme = (T_core_from_scheme + np.einsum('i,j,k->ijk', proj_u, v, w)) % 2
        
        T_core_actual = T_real[1:, :, :]
        core_match = np.all(T_core_from_scheme == T_core_actual)
        print(f"\n  Core reconstruction from scheme: {'MATCH' if core_match else 'MISMATCH'}")
        
        # Compute residual in E11 direction
        # For each core-contributing term, its epsilon = u[0]
        # Residual = M_0 + sum_{epsilon_i=1} X_i
        M0 = T_real[0, :, :]
        X_sum = np.zeros((9, 9), dtype=int)
        for i in core_terms:
            if f2_terms[i]['u'][0] == 1:  # epsilon_i = 1
                v = np.array(f2_terms[i]['v'])
                w = np.array(f2_terms[i]['w'])
                X_sum = (X_sum + np.outer(v, w)) % 2
        
        # Also add contributions from pure E11 terms
        for i in e11_terms:
            v = np.array(f2_terms[i]['v'])
            w = np.array(f2_terms[i]['w'])
            X_sum = (X_sum + np.outer(v, w)) % 2
        
        residual = (M0 + X_sum) % 2  # should be zero for an exact decomposition
        res_rank = f2_rank(residual)
        print(f"  Residual M_0 + sum(epsilon_i * X_i): rank = {res_rank}")
        print(f"  (Should be 0 for a complete decomposition)")
        
        # Also compute: for each choice of lift bits on just the core terms,
        # what is the residual rank?
        # For the actual scheme, the lift bits are determined
        # The residual should be exactly covered by the E11 terms
        
        # What does M_0 - (E11 terms contribution) - (epsilon-selected core terms) look like?
        print(f"\n  Analyzing the residual coverage by pure E11 terms:")
        e11_coverage = np.zeros((9,9), dtype=int)
        for i in e11_terms:
            v = np.array(f2_terms[i]['v'])
            w = np.array(f2_terms[i]['w'])
            e11_coverage = (e11_coverage + np.outer(v, w)) % 2
        
        uncovered = (M0 + X_sum + e11_coverage) % 2  # should equal M0 + all E11-component X_i
        # Actually T = sum of all terms = M0-part + core-part
        # The M0-part = sum of E11-component contributions = sum_{all t} u_t[0] * X_t
        total_e11_sum = np.zeros((9,9), dtype=int)
        for i in nonzero_terms:
            if f2_terms[i]['u'][0] == 1:
                v = np.array(f2_terms[i]['v'])
                w = np.array(f2_terms[i]['w'])
                total_e11_sum = (total_e11_sum + np.outer(v, w)) % 2
        e11_check = np.all(total_e11_sum == M0)
        print(f"  Sum of all E11-component X_i == M_0: {e11_check}")
    
    return {
        "total_f2_nonzero": len(nonzero_terms),
        "pure_e11": len(e11_terms),
        "core_contributing": len(core_terms),
        "reconstruction_ok": match
    }


# ---- Rank-one cover analysis ----

def count_rank_one_covers(T_core):
    """For each core slice, count how many rank-one F_2 matrices it decomposes into.
    Also find all rank-one matrices that appear in each slice's support."""
    print("\n=== Rank-one decomposition of individual core slices ===")
    
    for s in range(8):
        S = T_core[s, :, :]
        rk = f2_rank(S)
        # Find the rank-one decomposition by finding nonzero entries
        # Each core slice has exactly 3 nonzero entries, each of which is 
        # a separate rank-one matrix (since they're in distinct rows and columns)
        nz = []
        for r in range(9):
            for c in range(9):
                if S[r,c] == 1:
                    nz.append((r,c))
        
        # Check if these form a "generalized diagonal" (no two share row or column)
        rows_used = set(x[0] for x in nz)
        cols_used = set(x[1] for x in nz)
        is_partial_perm = (len(rows_used) == len(nz) and len(cols_used) == len(nz))
        
        print(f"  Slice {s} ({idx_to_label(s+1)}): rank={rk}, "
              f"{len(nz)} entries, partial_perm={is_partial_perm}")


def subspace_rank_one_count():
    """Count total rank-one 9x9 matrices over F_2 and those in various subspaces."""
    print("\n=== Rank-one matrix counts over F_2 in 9x9 ===")
    count = 0
    for b_int in range(1, 512):  # nonzero b vectors
        for c_int in range(1, 512):
            count += 1
    print(f"  Total rank-one 9x9 matrices over F_2: {count}")
    print(f"  (= (2^9 - 1)^2 = 511^2 = {511**2})")


def analyze_bc_structure(T_core, M0):
    """Analyze the B and C factor structure of core slices.
    
    Key question: which rank-one bc^T matrices can contribute to 
    multiple core slices simultaneously?
    
    For the core decomposition T_core = sum_i a_bar_i ⊗ b_i c_i^T,
    a term b_i c_i^T contributes to slice s iff (a_bar_i)_s = 1.
    
    So the question is: given the 8 target slice matrices S_0,...,S_7,
    which rank-one matrices X = b c^T satisfy X ∈ S_alpha for 
    multiple alpha simultaneously?
    """
    print("\n=== B⊗C factor sharing analysis ===")
    
    # A rank-one matrix X = bc^T contributes to slice S_alpha
    # iff when we write S_alpha = sum of rank-one terms, X appears.
    # But over F_2, S_alpha has rank 3, so it decomposes into 
    # exactly 3 rank-one matrices (since they're partial permutation matrices).
    
    # The actual question is different: given the FLEXIBLE decomposition
    # T_core = sum a_bar_i ⊗ X_i, which X_i patterns work?
    
    # For each pair of slices, check if there exists a rank-one bc^T 
    # that satisfies bc^T ≤ S_alpha + S_beta (entrywise, meaning 
    # bc^T is in the support intersection... no, that's not right either)
    
    # The correct formulation: X contributes to slices alpha where a_bar_alpha = 1.
    # For those slices: S_alpha = sum_{i: (a_bar_i)_alpha=1} X_i
    # This means X is one of the rank-one terms in the decomposition of S_alpha.
    
    # But S_alpha has MANY different rank-one decompositions!
    # A rank-3 matrix over F_2 can be decomposed into rank-one terms 
    # in multiple ways.
    
    # Let's enumerate rank-one matrices that lie "inside" each slice
    # (meaning bc^T has support within the support of S_alpha)
    
    for s in range(8):
        S = T_core[s, :, :]
        # Find all rank-one bc^T that are "compatible" with S
        # meaning every entry of bc^T that is 1 is also 1 in S
        # (bc^T ≤ S entrywise)
        
        # Find nonzero rows and columns of S
        nz_rows = [r for r in range(9) if any(S[r,c]==1 for c in range(9))]
        nz_cols = [c for c in range(9) if any(S[r,c]==1 for r in range(9))]
        
        # A rank-one bc^T with bc^T ≤ S means:
        # b can only have nonzero entries in nz_rows
        # c can only have nonzero entries in nz_cols
        # AND for every (i,j) where b_i=c_j=1, S[i,j] must be 1
        
        count_inside = 0
        for b_mask in range(1, 1 << len(nz_rows)):
            b = np.zeros(9, dtype=int)
            for bit, r in enumerate(nz_rows):
                if b_mask & (1 << bit):
                    b[r] = 1
            for c_mask in range(1, 1 << len(nz_cols)):
                c = np.zeros(9, dtype=int)
                for bit, cl in enumerate(nz_cols):
                    if c_mask & (1 << bit):
                        c[cl] = 1
                # Check bc^T ≤ S
                bc = np.outer(b, c)
                if np.all(bc * (1 - S) == 0):  # no entry where bc=1 but S=0
                    count_inside += 1
        
        print(f"  Slice {s} ({idx_to_label(s+1)}): "
              f"{count_inside} rank-one matrices with bc^T ≤ S "
              f"(rows: {nz_rows}, cols: {nz_cols})")


def compute_substitution_rank(T_core, M0):
    """
    For the rank-23 scheme reduced to F_2, compute the residual rank
    when we try different lift-bit patterns.
    
    Key insight from the review: R(T) ≤ R(T_core) + min_ε rank(M_0 + Σ ε_i X_i)
    
    For a given core decomposition T_core = Σ a_bar_i ⊗ X_i,
    the residual for lift bits ε is: M_0 + Σ ε_i X_i
    """
    # This requires an actual core decomposition, which we get from the rank-23 scheme
    pass  # Handled in analyze_rank23_mod2


# ---- Kruskal lower bound ----

def kruskal_bound(T_core):
    """Compute Kruskal's lower bound on tensor rank.
    
    R(T) >= rank_A(T) + rank_B(T) + rank_C(T) - 2 * min(rank_A, rank_B, rank_C)
    
    Wait, this isn't quite right. The actual Kruskal bound requires 
    k-ranks (maximum k such that any k columns of the factor matrix are LI).
    
    For the basic bound, we use:
    R(T) >= max(rank over any flattening)
    """
    shape = T_core.shape
    A_flat = T_core.reshape(shape[0], shape[1]*shape[2])
    B_flat = T_core.transpose(1, 0, 2).reshape(shape[1], shape[0]*shape[2])
    C_flat = T_core.transpose(2, 0, 1).reshape(shape[2], shape[0]*shape[1])
    
    rA = f2_rank(A_flat)
    rB = f2_rank(B_flat)
    rC = f2_rank(C_flat)
    
    # Basic lower bound
    basic_lb = max(rA, rB, rC)
    
    print(f"\n=== Lower bounds on R(T_core) ===")
    print(f"  Flattening lower bound: {basic_lb}")
    print(f"    (A-flat: {rA}, B-flat: {rB}, C-flat: {rC})")
    
    return basic_lb


def analyze_full_tensor(T):
    """Full tensor flattening analysis."""
    print("\n=== Full tensor T_<3,3,3> over F_2 ===")
    print(f"  Shape: {T.shape}")
    print(f"  Number of nonzero entries: {np.sum(T)}")
    flat = compute_flattenings(T, "T_<3,3,3>")
    return flat


# ---- Main ----

def main():
    outdir = "data/core_analysis"
    os.makedirs(outdir, exist_ok=True)
    
    results = {}
    
    # 1. Build tensor
    T = build_matmul_tensor()
    
    # Verify: T should have exactly 27 nonzero entries
    assert np.sum(T) == 27, f"Expected 27 nonzero entries, got {np.sum(T)}"
    print("=== 3x3 matrix multiplication tensor T_<3,3,3> over F_2 ===")
    print(f"Shape: {T.shape}, nonzero entries: {np.sum(T)}")
    
    # 2. Full tensor analysis
    full_flat = analyze_full_tensor(T)
    results["full_tensor_flattenings"] = full_flat
    
    # 3. Extract core and slice
    T_core, M0 = extract_core_and_slice(T)
    
    print(f"\n=== E11 quotient core ===")
    print(f"Core shape: {T_core.shape}")
    print(f"Core nonzero entries: {np.sum(T_core)}")
    print(f"M_0 rank: {f2_rank(M0)}")
    print(f"M_0 nonzero entries: {np.sum(M0)}")
    
    # 4. Core flattening analysis
    core_flat = compute_flattenings(T_core, "E11 core")
    results["core_flattenings"] = core_flat
    
    # 5. Core slice analysis
    slice_info = analyze_core_slices(T_core, M0)
    
    # 6. Kruskal bound
    kruskal_lb = kruskal_bound(T_core)
    results["kruskal_lower_bound"] = kruskal_lb
    
    # 7. Rank-one cover analysis
    count_rank_one_covers(T_core)
    
    # 8. BC structure analysis
    analyze_bc_structure(T_core, M0)
    
    # 9. Rank-23 scheme analysis
    scheme_path = "data/cn122_3x3_r23_repro/scheme.qmm"
    if os.path.exists(scheme_path):
        r23_info = analyze_rank23_mod2(scheme_path)
        results["rank23_f2_analysis"] = r23_info
    else:
        print(f"\nWARNING: scheme file not found at {scheme_path}")
    
    # 10. Summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    print(f"Full tensor T flattening ranks: A={full_flat['A_rank']}, "
          f"B={full_flat['B_rank']}, C={full_flat['C_rank']}")
    print(f"E11 core flattening ranks: A={core_flat['A_rank']}, "
          f"B={core_flat['B_rank']}, C={core_flat['C_rank']}")
    print(f"Flattening lower bound on R(T_core): {core_flat['max']}")
    print(f"Sum of core slice ranks: 8 × 3 = 24 (naive upper bound)")
    print(f"Target: R(T_core) ≤ 19 would give R(T) ≤ 22")
    print(f"Target: R(T_core) ≥ 20 (distinct branch) would give R(T) ≥ 21")
    
    # Save results
    results_path = os.path.join(outdir, "analysis_results.json")
    with open(results_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {results_path}")
    
    # Save the core tensor for later use
    np.save(os.path.join(outdir, "T_core_f2.npy"), T_core)
    np.save(os.path.join(outdir, "M0_f2.npy"), M0)
    np.save(os.path.join(outdir, "T_full_f2.npy"), T)
    print(f"Tensor arrays saved to {outdir}/")
    
    return results


if __name__ == "__main__":
    main()
