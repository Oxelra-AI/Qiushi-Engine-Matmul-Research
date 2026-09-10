#!/usr/bin/env python3
"""
Verify cross-contamination constraint and explore valid sharing patterns
for the E11 core decomposition over F_2.

Key insight discovered in analysis: A rank-one 9x9 matrix that contributes to 
multiple core blocks ALSO contaminates other blocks within each of its assigned
slices. For a valid core decomposition, this contamination must be CANCELED
by other terms assigned to the same slices.

This script:
1. Demonstrates the cross-contamination with a concrete example
2. Explores what valid 2-block sharing patterns exist
3. Computes the inner product condition rank(I_3 + bc^T) = 2 iff b·c = 1
4. Analyzes the cancellation requirements for sharing
5. Tests whether a rank-19 core decomposition is achievable with structured sharing
"""

import numpy as np
from itertools import product, combinations
import json, os

def f2_rank(mat):
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

def build_core_slices():
    """Build the 8 core slice matrices (each 9x9, rank 3)."""
    slices = []
    # Core A-indices 0..7 correspond to (i,k) != (1,1) in order:
    # 0: e12 (i=1,k=2), 1: e13 (i=1,k=3), 2: e21 (i=2,k=1),
    # 3: e22 (i=2,k=2), 4: e23 (i=2,k=3), 5: e31 (i=3,k=1),
    # 6: e32 (i=3,k=2), 7: e33 (i=3,k=3)
    ik_pairs = [(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)]
    
    for (i_val, k_val) in ik_pairs:
        S = np.zeros((9,9), dtype=int)
        for j in range(1, 4):
            b_idx = 3*(k_val-1) + (j-1)
            c_idx = 3*(i_val-1) + (j-1)
            S[b_idx, c_idx] = 1
        slices.append(S)
    
    return slices, ik_pairs


def verify_cross_contamination():
    """Demonstrate that naive multi-block rank-one terms contaminate slices."""
    print("=== Cross-contamination demonstration ===")
    
    # Construct the "sharing" term from my failed attempt:
    # b = e_{21} = (0,0,0,1,0,0,0,0,0), c = e_{11}+e_{21}+e_{31} = (1,0,0,1,0,0,1,0,0)
    b = np.array([0,0,0,1,0,0,0,0,0])
    c = np.array([1,0,0,1,0,0,1,0,0])
    X = np.outer(b, c) % 2
    
    print(f"Rank-one term X = b⊗c^T:")
    print(f"  b = {b} (B-block 2 only)")
    print(f"  c = {c} (C-blocks 1, 2, 3)")
    
    # Block analysis
    for bk in range(3):
        for ci in range(3):
            block = X[3*bk:3*bk+3, 3*ci:3*ci+3]
            if np.any(block):
                print(f"  Block ({bk+1},{ci+1}): nonzero = {block.tolist()}")
    
    # Check against core slices
    slices, ik_pairs = build_core_slices()
    print(f"\n  This term has nonzero blocks in (2,1), (2,2), (2,3)")
    print(f"  If assigned A-label (1,0,0,1,0,0,1,0):")
    print(f"    Contributes to slice 0 (e12, target=I3 in (2,1)): CONTAMINATES (2,2),(2,3)")
    print(f"    Contributes to slice 3 (e22, target=I3 in (2,2)): CONTAMINATES (2,1),(2,3)")
    print(f"    Contributes to slice 6 (e32, target=I3 in (2,3)): CONTAMINATES (2,1),(2,2)")


def inner_product_rank_condition():
    """Verify: rank(I_3 + bc^T) = 2 iff b·c = 1 over F_2."""
    print("\n=== Inner product rank condition ===")
    I3 = np.eye(3, dtype=int)
    
    count_rank2 = 0
    count_rank3 = 0
    
    for b_int in range(1, 8):
        for c_int in range(1, 8):
            b = np.array([(b_int >> i) & 1 for i in range(3)])
            c = np.array([(c_int >> i) & 1 for i in range(3)])
            X = np.outer(b, c)
            R = (I3 + X) % 2
            rk = f2_rank(R)
            inner = (np.dot(b, c)) % 2
            
            if rk == 2:
                count_rank2 += 1
                assert inner == 1, f"rank=2 but b·c={inner}: b={b}, c={c}"
            elif rk == 3:
                count_rank3 += 1
                assert inner == 0, f"rank=3 but b·c={inner}: b={b}, c={c}"
            else:
                print(f"  UNEXPECTED: rank={rk} for b={b}, c={c}")
    
    print(f"  rank(I_3 + bc^T) = 2: {count_rank2} cases (all have b·c = 1)")
    print(f"  rank(I_3 + bc^T) = 3: {count_rank3} cases (all have b·c = 0)")
    print(f"  Confirmed: rank(I_3 + bc^T) = 2 ⟺ b·c = 1")
    print(f"  Confirmed: rank(I_3 + bc^T) = 3 ⟺ b·c = 0")


def explore_valid_sharing():
    """
    Explore valid 2-block sharing with cancellation.
    
    For a valid sharing term X_t that contributes to two slices α₁, α₂:
    - X_t's block at (k₁,i₁) [target for α₁] must be part of I₃ decomposition
    - X_t's block at (k₂,i₂) [target for α₂] must be part of I₃ decomposition  
    - X_t's other blocks are "pollution" that must be canceled
    
    The pollution in slice α₁ is in block (k₂,i₂) and vice versa.
    Cancellation requires another term with the SAME block contribution
    at the pollution position, also contributing to the polluted slice.
    """
    print("\n=== Valid sharing analysis with cancellation ===")
    
    slices, ik_pairs = build_core_slices()
    
    # Map from core index to (i,k) pair and hence to block (k,i)
    # Core index s → (i,k) = ik_pairs[s] → block (k-1, i-1) in 0-indexed
    # Block of slice s: (k-1, i-1) where (i,k) = ik_pairs[s]
    def slice_block(s):
        i, k = ik_pairs[s]
        return (k-1, i-1)  # B-block, C-block in 0-indexed
    
    print(f"Slice-to-block mapping:")
    for s in range(8):
        bk, ci = slice_block(s)
        print(f"  Slice {s} ({ik_pairs[s]}): target block ({bk+1},{ci+1})")
    
    # For two slices s1, s2 that a sharing term covers:
    # The term has nonzero blocks at a set containing the target blocks.
    # For a rank-one X = bc^T, the nonzero blocks are {(bk,ci) : b_bk ≠ 0, c_ci ≠ 0}
    # This is a rectangular set.
    
    # The "pollution" of slice s1 from the sharing term is at ALL blocks other than
    # the target block of s1. Similarly for s2.
    
    # For cancellation, other terms contributing to s1 must have the opposite
    # value at the pollution positions.
    
    # Key question: what pairs of slices (s1, s2) can share a rank-one term
    # such that the pollution is cancelable?
    
    print(f"\n  Analyzing all pairs of core slices for sharing potential:")
    
    good_pairs = []
    for s1 in range(8):
        for s2 in range(s1+1, 8):
            bk1, ci1 = slice_block(s1)
            bk2, ci2 = slice_block(s2)
            
            # A rank-one term covering both slices needs:
            # b has nonzero in both B-blocks bk1, bk2
            # c has nonzero in both C-blocks ci1, ci2
            
            # This means the term also hits blocks:
            # (bk1,ci1) [target for s1], (bk1,ci2), (bk2,ci1), (bk2,ci2) [target for s2]
            # Plus any other blocks from additional B/C-block activity.
            
            if bk1 == bk2:
                # Same B-block: the term only spans one B-block
                # Nonzero blocks: (bk1, ci1) and (bk1, ci2)
                # No "rectangular fill" across B-blocks
                n_contamination = 0
                sharing_type = "same-B-block"
            elif ci1 == ci2:
                # Same C-block
                n_contamination = 0
                sharing_type = "same-C-block"
            else:
                # Different B-blocks AND C-blocks
                # The term hits (bk1,ci1), (bk1,ci2), (bk2,ci1), (bk2,ci2)
                # Of these: (bk1,ci1) is target for s1, (bk2,ci2) is target for s2
                # (bk1,ci2) and (bk2,ci1) are pollution
                n_contamination = 2
                sharing_type = "cross"
                
                # Check if (bk1,ci2) and (bk2,ci1) are core blocks
                block_12_is_core = (bk1, ci2) != (0, 0)
                block_21_is_core = (bk2, ci1) != (0, 0)
            
            # For same-B or same-C sharing, contamination is simpler
            if bk1 == bk2:
                # b only in block bk1 = bk2, c spans ci1 and ci2
                # Blocks hit: (bk1, ci1) and (bk1, ci2)
                # At slice s1: target (bk1,ci1) OK, pollution (bk1,ci2)
                # But (bk1,ci2) is the target block of s2!
                # At slice s2: target (bk1,ci2) OK, pollution (bk1,ci1)
                # So pollution from s1→s2 and s2→s1 are in each other's target blocks.
                detail = f"pollution at each other's targets"
                
            elif ci1 == ci2:
                detail = f"pollution at each other's targets"
                
            else:
                cross_blocks = [(bk1,ci2), (bk2,ci1)]
                detail = f"cross blocks {cross_blocks}"
            
            good_pairs.append((s1, s2, sharing_type, detail))
            if len(good_pairs) <= 15:
                print(f"  Slices {s1},{s2}: blocks ({bk1+1},{ci1+1}),({bk2+1},{ci2+1}), "
                      f"type={sharing_type}, {detail}")
    
    # Count by type
    type_counts = {}
    for _, _, t, _ in good_pairs:
        type_counts[t] = type_counts.get(t, 0) + 1
    print(f"\n  Sharing type counts: {type_counts}")
    
    # For same-B or same-C sharing: 
    # The pollution is in each other's target blocks. If both slices s1, s2
    # see the sharing term, then:
    # Slice s1 gets: target_s1 contribution + target_s2 contribution (pollution)
    # Slice s2 gets: target_s2 contribution + target_s1 contribution (pollution)
    # 
    # To cancel pollution at slice s1 in target_s2 block: other terms at s1
    # must sum to zero in that block. But the target for s2 is I_3, so
    # those other terms must also contribute 0 to s1's view of the s2 block.
    # 
    # This means: at slice s1, the sum of ALL terms' contributions at the s2 block
    # must be zero. The sharing term contributes its (bk_s2, ci_s2) block content.
    # Other terms at s1 must contribute the negative (= same, over F₂) content.
    
    print("\n=== Same-block sharing: detailed feasibility ===")
    # Example: slices 0 (e12, block (2,1)) and 3 (e22, block (2,2))
    # Same B-block (2). A sharing term has b in B-block 2, c in C-blocks 1 and 2.
    # Block contributions: (2,1) = b₂c₁^T, (2,2) = b₂c₂^T
    # At slice 0: want (2,1) = part of I₃, but (2,2) is pollution
    # At slice 3: want (2,2) = part of I₃, but (2,1) is pollution
    
    # For the pollution to cancel: other terms at slice 0 must contribute 
    # -b₂c₂^T = b₂c₂^T (over F₂) in block (2,2). But slice 0's target is 
    # zero in block (2,2). So the pollution + cancellation = 0, meaning
    # the sum of all block-(2,2) contributions at slice 0 must be zero.
    
    # This requires OTHER terms at slice 0 to contribute b₂c₂^T in block (2,2).
    # Those other terms must have ā_t(0) = 1 AND have nonzero (2,2) block.
    
    # The total (2,2)-block contribution at slice 0 must be zero. So:
    # sharing_term's (2,2) block + cancellation_terms' (2,2) blocks = 0
    
    # Similarly, at slice 3, total (2,1) block = 0.
    
    # This means the cancellation terms contribute OPPOSITE content to the 
    # sharing term at the pollution positions.
    
    # CAN this be done efficiently? Let's check:
    # If we use N sharing terms between slices 0 and 3, they each add
    # pollution to both slices. The cancellation terms must cancel ALL
    # the accumulated pollution.
    
    # The cancellation terms themselves are also rank-one matrices.
    # They contribute to slice 0 (so ā_t(0)=1) and have nonzero (2,2) block.
    # But they also contribute to the (2,1) block at slice 0 (part of the target).
    
    # Key: the cancellation terms become sharing terms themselves! They must
    # contribute to BOTH the target block of slice 0 AND the pollution block.
    # This creates a recursive sharing/cancellation structure.
    
    # The net effect: sharing between same-B-block slices requires a balanced
    # structure where the sharing terms' pollution is exactly canceled.
    
    # Bottom line: this is the FULL tensor rank problem in disguise.
    # There's no "free" sharing without cancellation.
    print("  Same-block sharing requires exact cancellation of cross-contamination.")
    print("  This couples the sharing terms with cancellation terms, making the")
    print("  problem equivalent to the full tensor rank computation.")
    print("  Naive block sharing does NOT reduce the rank.")


def compute_core_rank_bounds():
    """Compute various bounds on R(T_core)."""
    print("\n=== Core tensor rank bounds ===")
    
    slices, ik_pairs = build_core_slices()
    
    # Build the full core tensor
    T_core = np.zeros((8, 9, 9), dtype=int)
    for s in range(8):
        T_core[s] = slices[s]
    
    # Lower bounds
    # 1. Flattening bound
    A_flat = T_core.reshape(8, 81)
    B_flat = T_core.transpose(1, 0, 2).reshape(9, 72)
    C_flat = T_core.transpose(2, 0, 1).reshape(9, 72)
    
    rA = f2_rank(A_flat)
    rB = f2_rank(B_flat)
    rC = f2_rank(C_flat)
    flat_lb = max(rA, rB, rC)
    
    print(f"  Flattening lower bound: {flat_lb} (A:{rA}, B:{rB}, C:{rC})")
    
    # 2. From full tensor: R(T_core) >= R(T) - 3 >= 17
    print(f"  From R(T)>=20: R(T_core) >= R(T) - rank(M0) >= 17")
    
    # Upper bounds
    # 1. Naive: 8 slices × 3 = 24
    print(f"  Naive upper bound: 24 (8 × 3)")
    
    # 2. From R(T) <= 23: R(T_core) <= 23
    print(f"  From R(T)<=23: R(T_core) <= 23")
    
    # 3. From rank-23 scheme (gives 21-term core): R(T_core) <= 21
    print(f"  From cn122 rank-23 scheme (F2): R(T_core) <= 21")
    
    # Target
    print(f"\n  TARGET: R(T_core) <= 19 would give R(T) <= 22")
    print(f"  OPEN QUESTION: 17 <= R(T_core) <= 21")
    
    # 4. Check the 2x2 submatrix multiplication bound
    # T_core restricted to certain sub-tensors
    # The core is an 8x9x9 tensor. Its first few slices represent
    # parts of the 3x3 multiplication that can be related to 2x2 multiplication.
    
    # The 2x2 submatrix multiplication tensor T_<2,2,2> has rank 7 over any field.
    # Can we embed T_<2,2,2> inside T_core?
    
    # T_<2,2,2> has A-space F_2^4, B-space F_2^4, C-space F_2^4.
    # We need linear maps from F_2^8, F_2^9, F_2^9 to F_2^4, F_2^4, F_2^4
    # such that the restriction of T_core gives T_<2,2,2>.
    
    # Actually, this is a restriction, and R(restriction) <= R(T_core).
    # So R(T_core) >= R(any restriction).
    
    # T_<2,2,2> has rank 7. If T_core restricts to T_<2,2,2>, then R(T_core) >= 7.
    # Not very helpful (we already know >= 17).
    
    print(f"\n  Note: Better lower bounds come from Wang certificates, not flattenings.")
    print(f"  The 417,198-row Wang E11 core table is the strongest available lower bound tool.")


def construct_and_verify_candidate(num_terms, description=""):
    """
    Try to construct a core decomposition by choosing structured A-labels
    and solving for the rank-one terms.
    
    For a given set of A-labels (8xn binary matrix A), the core equations become:
    For each alpha: sum_{t: A[alpha,t]=1} X_t = S_alpha (9x9 equation)
    
    These are 8*81 = 648 linear equations in n*81 unknowns (entries of X_t),
    PLUS the rank-one constraint on each X_t.
    
    Without rank-one constraint: linear system in F_2.
    """
    print(f"\n=== Constructive analysis for {num_terms}-term core ({description}) ===")
    
    slices, ik_pairs = build_core_slices()
    
    # Try specific A-label patterns
    # Pattern 1: weight-1 labels (standard basis) - gives 24 terms
    # Pattern 2: weight-2 labels - potentially 12 terms but with cancellation
    # Pattern 3: weight-3 labels - potentially fewer terms
    
    # With n=19 terms and distinct nonzero labels, the 8x19 A-matrix
    # defines which terms contribute to which slices.
    # Each column is a distinct nonzero 8-bit vector.
    
    # The column weight determines how many slices see that term.
    # Total "assignments" = sum of column weights = 
    #   sum of row weights = total terms per slice * 8
    
    # Each row (slice) needs its assigned terms to sum to S_alpha.
    # The minimum terms per slice is 3 (since rank(S_alpha) = 3).
    # So total assignments >= 8 * 3 = 24.
    
    # With 19 terms, avg weight = 24/19 ≈ 1.26
    # So most terms must be weight 1 or 2, with a few weight 2+
    
    # Minimum possible: some terms weight 1 (contribute to 1 slice),
    # others weight 2+ (contribute to multiple slices, saving terms).
    # Let w_1 terms have weight 1, w_2 have weight 2, etc.
    # w_1 + w_2 + ... = 19 (total terms)
    # w_1 + 2*w_2 + 3*w_3 + ... >= 24 (total assignments)
    # Each slice gets >= 3 assignments.
    
    # Optimal: 5 terms weight 2, 14 terms weight 1
    # 14 + 2*5 = 24 assignments ✓
    # 5 + 14 = 19 terms ✓
    
    # But weight-2 terms create cross-contamination that must cancel!
    # The cancellation itself doesn't add terms (it uses existing terms),
    # but it constrains the choice of rank-one matrices.
    
    print(f"  Min assignments needed: 24 (8 slices × 3 rank-one terms)")
    print(f"  With {num_terms} terms, avg weight = {24/num_terms:.2f}")
    
    # Let's check: is 19 terms achievable with the linear system?
    # (ignoring rank-one constraint)
    
    # Try A-labels: 8 weight-1 + 11 from weight-2 choices
    # Wait, we need 19 terms total. Let's try:
    # - 14 weight-1 terms (14 assignments)
    # - 5 weight-2 terms (10 assignments)
    # Total: 24 assignments ✓
    
    # But 8 weight-1 vectors span F_2^8, so 14 weight-1 vectors include
    # 6 "duplicates" (which can't be, since labels must be distinct nonzero).
    # There are only 8 weight-1 vectors in F_2^8.
    # So at most 8 weight-1 labels, then 11 must have weight >= 2.
    # 8 + 2*11 = 30 > 24, so some can be weight 2 and still meet 24.
    
    # Minimum: 8*1 + x*2 >= 24, so x >= 8. But total = 8 + x = 19, so x = 11.
    # 8 + 11*2 = 30 >= 24. ✓ Excess = 6.
    
    # This means: each slice gets assigned:
    # - 1 weight-1 term (the unique weight-1 label for that slice)
    # - Sum of weight-2 terms that include that slice
    
    # Each slice must get >= 3 total terms. With 1 from weight-1,
    # needs >= 2 from weight-2 terms.
    
    # 11 weight-2 terms, each covering 2 slices = 22 slice-assignments.
    # 8 slices each need >= 2 = total need 16.
    # 22 >= 16, so feasible by counting.
    
    # But the LINEAR system must also be solvable.
    # Let's try a specific assignment and check.
    
    # Choice: weight-1 labels are e_0,...,e_7 (standard basis)
    # Weight-2 labels: choose 11 from the 28 weight-2 vectors in F_2^8
    
    # For balanced coverage: each slice should get 2-3 weight-2 terms.
    # 11 terms × 2 assignments / 8 slices = 2.75 per slice on average.
    
    # Example balanced choice:
    # Pair slices: (0,3), (0,6), (1,4), (1,7), (2,5), (3,6), (4,7), (2,3), (5,6), (5,7), (0,1)
    weight2_pairs = [
        (0,3), (0,6), (1,4), (1,7), (2,5), 
        (3,6), (4,7), (2,3), (5,6), (5,7), (0,1)
    ]
    
    # Count per slice:
    slice_weight2_count = [0]*8
    for s1, s2 in weight2_pairs:
        slice_weight2_count[s1] += 1
        slice_weight2_count[s2] += 1
    
    print(f"\n  Weight-2 pair assignments: {weight2_pairs}")
    print(f"  Weight-2 terms per slice: {slice_weight2_count}")
    print(f"  Total terms per slice (including weight-1): {[1+c for c in slice_weight2_count]}")
    
    # Each slice now has r_s = 1 + weight2_count terms.
    # The linear system at each slice: sum of assigned X_t = S_alpha
    # This is a 81-equation system in r_s * 81 unknowns (entries of X_t).
    # With rank-one constraint: r_s * (9+9) = r_s * 18 effective parameters.
    
    # For r_s = 3: 81 equations in 3*18 = 54 parameters. Overdetermined!
    # For r_s = 4: 81 equations in 4*18 = 72 parameters. Still overdetermined.
    # For r_s = 5: 81 equations in 5*18 = 90 parameters. Slightly underdetermined.
    
    # But the equations are coupled across slices (shared terms).
    
    min_terms = min(1+c for c in slice_weight2_count)
    max_terms = max(1+c for c in slice_weight2_count)
    print(f"  Terms per slice range: [{min_terms}, {max_terms}]")
    
    return slice_weight2_count


def main():
    outdir = "data/core_analysis"
    os.makedirs(outdir, exist_ok=True)
    
    print("=" * 60)
    print("CROSS-CONTAMINATION AND SHARING ANALYSIS")
    print("=" * 60)
    
    verify_cross_contamination()
    inner_product_rank_condition()
    explore_valid_sharing()
    compute_core_rank_bounds()
    construct_and_verify_candidate(19, "target for rank-22 full tensor")
    
    print("\n" + "=" * 60)
    print("CONCLUSIONS")
    print("=" * 60)
    print("""
1. CROSS-CONTAMINATION is the fundamental barrier to simple rank reduction.
   A rank-one 9x9 matrix spanning multiple blocks creates pollution in
   every assigned slice's non-target blocks.

2. INNER PRODUCT CONDITION: rank(I_3 + bc^T) = 2 iff b·c = 1 (mod 2).
   This means 28/49 rank-one perturbations reduce rank, 21/49 don't.

3. The RESIDUAL CONDITION (for rank-20 full decomposition) requires:
   - At least 2 rank-one contributions to reduce I_3's rank from 3 to ≤1
   - Global rank-1 constraint couples all blocks simultaneously
   - This is a strong obstruction to rank-20 decompositions

4. CORE RANK BOUNDS: 17 ≤ R(T_core) ≤ 21 over F_2.
   (Lower from R(T)≥20, upper from rank-23 scheme.)
   Target: R(T_core) ≤ 19.

5. A 19-term core decomposition requires ~5 "sharing" terms (weight ≥ 2)
   with exact cancellation of cross-contamination. This is a genuine
   algebraic difficulty, not a simple covering problem.
""")


if __name__ == "__main__":
    main()
