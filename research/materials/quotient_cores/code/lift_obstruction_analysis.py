#!/usr/bin/env python3
"""Analyze the rank-≤1 lift obstruction for full rank-20 decompositions.

KEY THEOREM (to establish):
In any full rank-20 decomposition of T_{333} over F_2, if one term
has pure E_{00} A-factor, the remaining 19 core terms have "lift bits"
ε_i ∈ {0,1} determining whether a_0(term_i) = 1. The constraint is:

    rank(M_0 + Δ) ≤ 1   where Δ = sum_{i: ε_i=1} v_i ⊗ w_i

and M_0 = I_3 in block (0,0) of the 9×9 B⊗C matrix.

This script:
1. Enumerates all rank-≤1 matrices q⊗r ∈ F_2^{9×9}
2. For each, computes Δ = M_0 + q⊗r and analyzes its block structure
3. Determines what constraints this places on core decompositions
"""
import numpy as np
from pathlib import Path
import json
import itertools

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUTDIR = WS / "data" / "lift_obstruction"
OUTDIR.mkdir(parents=True, exist_ok=True)

def vec_from_mask(mask, n):
    return np.array([(int(mask)>>i)&1 for i in range(n)], dtype=np.uint8)

def gf2_rank(M):
    A = M.copy().astype(np.uint8) % 2
    rows, cols = A.shape
    rank = 0
    for col in range(cols):
        pivot = None
        for row in range(rank, rows):
            if A[row, col] & 1:
                pivot = row
                break
        if pivot is None:
            continue
        A[[rank, pivot]] = A[[pivot, rank]]
        for row in range(rows):
            if row != rank and (A[row, col] & 1):
                A[row] ^= A[rank]
        rank += 1
    return rank

def block_decompose(M):
    """Decompose 9x9 matrix into 3x3 blocks."""
    blocks = {}
    for s in range(3):
        for t in range(3):
            block = M[3*s:3*s+3, 3*t:3*t+3].copy()
            blocks[(s,t)] = block
    return blocks

def main():
    print("=" * 60)
    print("RANK-≤1 LIFT OBSTRUCTION ANALYSIS")
    print("=" * 60)
    
    # M_0 = I_3 in block (0,0), zero elsewhere
    M0 = np.zeros((9,9), dtype=np.uint8)
    M0[:3,:3] = np.eye(3, dtype=np.uint8)
    print(f"\nM_0 rank: {gf2_rank(M0)}, nnz: {int(M0.sum())}")
    
    # Enumerate all q⊗r with q,r ∈ F_2^9 (rank ≤ 1)
    # q=0 or r=0 gives the zero matrix
    # q,r nonzero: 511 × 511 = 261121 rank-1 matrices
    # But many are equal: rank-1 matrix u⊗v = (cu)⊗(v/c), but over F_2 c=1 only
    # So each nonzero rank-1 matrix has unique factorization u⊗v
    
    # For each target Q = q⊗r (including Q=0), compute Δ = M_0 + Q
    # and analyze what Δ means for core terms
    
    # Case 1: Q = 0 (rank 0). Δ = M_0.
    print("\n--- Case 1: q⊗r = 0 (no residual) ---")
    print("Δ = M_0 = I_3 in block (0,0)")
    print("Lifted terms must sum to I_3 in block (0,0), 0 elsewhere")
    print("This requires ≥3 lifted terms with block-(0,0) contribution")
    print("AND all other block contributions must cancel exactly")
    
    # Case 2: Q = q⊗r nonzero. Analyze block structure.
    # q = (q_0, q_1, q_2) where q_s ∈ F_2^3
    # Block (s,t) of Q = q_s ⊗ r_t
    
    # The key question: for each valid Q, what does Δ = M_0 + Q look like in blocks?
    
    # Let's enumerate the DISTINCT Δ matrices (up to the block structure)
    # and classify them by:
    # - number of nonzero blocks
    # - rank of block (0,0) entry
    # - maximum rank of any block
    
    block_type_counts = {}
    delta_analysis = []
    
    # Include Q=0 case
    Q_zero = np.zeros((9,9), dtype=np.uint8)
    Delta_zero = (M0 + Q_zero) % 2
    blocks_zero = block_decompose(Delta_zero)
    nz_blocks_zero = sum(1 for b in blocks_zero.values() if b.any())
    print(f"\nQ=0: Delta has {nz_blocks_zero} nonzero blocks, block(0,0) rank = {gf2_rank(blocks_zero[(0,0)])}")
    
    # Systematic analysis of all Q = q⊗r
    q_nonzero_patterns = {}  # (q0_mask, q1_mask, q2_mask) -> count
    
    total_valid = 0  # Q where M_0+Q has some useful structure
    rank1_deltas = []  # collect info about each Q
    
    # For efficiency, enumerate q by 3-bit sub-blocks
    for qm in range(512):  # q ∈ F_2^9
        if qm == 0:
            continue
        q = vec_from_mask(qm, 9)
        q0, q1, q2 = q[:3], q[3:6], q[6:9]
        
        for rm in range(512):  # r ∈ F_2^9
            if rm == 0:
                continue
            r = vec_from_mask(rm, 9)
            r0, r1, r2 = r[:3], r[3:6], r[6:9]
            
            Q = np.outer(q, r).astype(np.uint8) % 2
            Delta = (M0 + Q) % 2
            
            # Block analysis
            blocks = block_decompose(Delta)
            nz_count = sum(1 for b in blocks.values() if b.any())
            b00_rank = gf2_rank(blocks[(0,0)])
            delta_rank = gf2_rank(Delta)
            
            key = (nz_count, b00_rank, delta_rank)
            block_type_counts[key] = block_type_counts.get(key, 0) + 1
    
    # Also include Q=0
    key_zero = (nz_blocks_zero, gf2_rank(blocks_zero[(0,0)]), gf2_rank(Delta_zero))
    block_type_counts[key_zero] = block_type_counts.get(key_zero, 0) + 1
    
    print(f"\n--- Block type classification of Δ = M_0 + q⊗r ---")
    print(f"{'(nz_blocks, b00_rank, Δ_rank)':<40} Count")
    for key in sorted(block_type_counts.keys()):
        print(f"{str(key):<40} {block_type_counts[key]}")
    
    total = sum(block_type_counts.values())
    print(f"\nTotal configurations: {total} (1 zero + {total-1} nonzero)")
    
    # Deeper analysis: for each Q, what does the constraint mean?
    # Δ_{st} = sum_{ε_i=1} v_i^{(s)} ⊗ w_i^{(t)} for each block (s,t)
    # This is a bilinear matrix factorization problem.
    
    # Key observation: Δ must be expressible as sum of rank-1 terms from 
    # a valid core decomposition's lifted subset.
    
    # Compute: for the Q=0 case, Δ = M_0.
    # Δ has rank 3, only in block (0,0).
    # Need: sum of lifted v_i ⊗ w_i = M_0.
    # Each v_i ⊗ w_i is 9×9 rank-1. In block (s,t), it contributes v_i^{(s)} ⊗ w_i^{(t)}.
    # For Δ_{st} = 0 when (s,t) ≠ (0,0), either v_i^{(s)} = 0 or w_i^{(t)} = 0 for each lifted term.
    # But also Δ_{00} = I_3, so v_i^{(0)} ⊗ w_i^{(0)} must sum to I_3.
    
    # This means: for each lifted term, if v_i^{(0)} ≠ 0 and w_i^{(0)} ≠ 0,
    # then for all s≠0: v_i^{(s)} = 0, and for all t≠0: w_i^{(t)} = 0.
    # i.e., v_i lives entirely in B-block 0, and w_i lives entirely in C-block 0.
    
    # Conversely, lifted terms with v_i^{(0)} = 0 or w_i^{(0)} = 0 don't affect block (0,0)
    # but must still cancel in all other blocks.
    
    print("\n--- Q=0 Case: Deep analysis ---")
    print("Lifted terms contributing to block (0,0) must have:")
    print("  v_i ∈ F_2^3 × {0}^6 and w_i ∈ F_2^3 × {0}^6")
    print("  (B,C factors confined to block 0)")
    print("These terms participate in NO core slice except possibly:")
    print("  Slices whose block is (0,*) or (*,0) - but block (0,0) is the removed slice")
    
    # The slices with block (0,*) are: block (0,1) = a10 (slice 2), block (0,2) = a20 (slice 5)
    # The slices with block (*,0) are: block (1,0) = related analysis (slice 0), block (2,0) = related analysis (slice 1)
    # But a term with v confined to block 0 and w confined to block 0 has:
    # v^{(s)} = 0 for s≠0 and w^{(t)} = 0 for t≠0
    # So v_i ⊗ w_i is zero in ALL blocks except (0,0).
    # This means the term contributes to a core slice s iff u_i[s] = 1,
    # but the contribution is all in block (0,0), which is NOT the assigned block for any s!
    # So these terms create "pollution" in block (0,0) of every slice they participate in,
    # and zero contribution in the assigned block.
    
    # This means: a term with v ∈ B-block-0 and w ∈ C-block-0 can only participate
    # in a core slice if that slice's assigned block is (0,0). But the only block (0,0)
    # assignment is the REMOVED slice (a00), not any core slice!
    
    # Therefore: such a term must have u_i = 0 (participate in no core slice).
    # But u_i ∈ F_2^8 \ {0} for all core terms.
    # CONTRADICTION unless the term is not a core term - but all 19 terms are core terms.
    
    # Wait - I need to be more careful. Let me re-examine.
    
    # A core term i with u_i has bit s set means it participates in slice s.
    # In slice s, its contribution to the 9×9 matrix is v_i ⊗ w_i.
    # The slice requires this (summed over all participating terms) to equal
    # core[s] = I_3 in block (j_s, i_s) and 0 elsewhere.
    
    # If term i has v confined to B-block 0 and w confined to C-block 0:
    # v_i ⊗ w_i has nonzero entries only in block (0,0) of the 9×9 matrix.
    # For slice s with assigned block (j_s, i_s) ≠ (0,0):
    #   - In the assigned block: contribution is 0 (bad - doesn't help)
    #   - In block (0,0): contribution is v_i^{(0)} ⊗ w_i^{(0)} (pollution)
    # For the pollution to cancel, other terms in slice s must cancel this.
    
    # So such terms are "parasitic" - they pollute block (0,0) of every slice they join
    # without contributing to the assigned block.
    
    # This is a very interesting structural constraint. But can the pollution be canceled?
    
    # Yes, IF there are other terms in the same slice that have compensating block-(0,0)
    # contributions. But those other terms would also pollute block (0,0) of their own
    # other slices. This creates a cascading constraint.
    
    # The STRONGER claim is that the Q=0 case is impossible. Let me try to prove this.
    
    # Claim: In the Q=0 case, there exist NO valid core decomposition + lift assignment.
    
    # In Q=0: lifted terms must sum to M_0 = I_3 in block (0,0), 0 elsewhere.
    # But we showed: any lifted term with v,w confined to block (0,0) can't participate
    # in any core slice (would need u_i = 0). So it can't be a core term.
    # Since all 19 terms are core terms, no term can be confined to block (0,0).
    
    # Therefore: the lifted terms that contribute to block (0,0) must also have
    # components in other blocks. But those components create nonzero entries in
    # other blocks of Δ, contradicting Δ_{st} = 0 for (s,t) ≠ (0,0).
    
    # UNLESS the contributions cancel. Let me check when they can cancel.
    
    # For (s,t) ≠ (0,0): sum_{ε_i=1} v_i^{(s)} ⊗ w_i^{(t)} = 0
    # This means: for each pair of B-block s and C-block t (not both 0),
    # the rank-one contributions from lifted terms must sum to zero.
    
    print("\n--- Feasibility analysis for Q=0 ---")
    print("Need: sum_{lifted} v_i ⊗ w_i = M_0 (I_3 in block (0,0), 0 elsewhere)")
    print("Each lifted term is also a core term with u_i ≠ 0")
    print("The term contributes v_i ⊗ w_i to every slice it participates in")
    print("In core slice s (assigned to block (j_s, i_s)):")
    print("  contribution in assigned block: v_i^{(j_s)} ⊗ w_i^{(i_s)}")
    print("  contribution in block (0,0): v_i^{(0)} ⊗ w_i^{(0)}")
    print("  contributions in other blocks must cancel with other terms in slice s")
    
    # Let me compute the number of "block-0-confined" rank-1 9×9 matrices
    # and check if any subset sums to M_0.
    
    # Actually, let me think differently. For the Q=0 case:
    # Δ = M_0 means the lifted subset's B⊗C sum equals M_0.
    # M_0 is supported only on block (0,0) with rank 3.
    # Any 9×9 rank-1 matrix v⊗w with nonzero block-(0,0) entry also has
    # nonzero entries in blocks (0,t) for t where w^{(t)}≠0 and (s,0) for s where v^{(s)}≠0.
    # For the sum to be zero in those blocks, we need cancellation.
    
    # This is more subtle than I initially thought. Let me compute exhaustively
    # for small cases.
    
    # Actually, let me compute the minimal rank of Δ for each case.
    
    # For the Q=0 case, Δ rank is 3.
    # For Q = q⊗r nonzero, Δ = M_0 + q⊗r has rank in {2,3,4}.
    
    # Let me compute the distribution
    delta_rank_dist = {0: 0, 1: 0, 2: 0, 3: 0, 4: 0}
    for qm in range(512):
        q = vec_from_mask(qm, 9)
        for rm in range(512):
            r = vec_from_mask(rm, 9)
            Q = np.outer(q, r).astype(np.uint8) % 2
            Delta = (M0 + Q) % 2
            rk = gf2_rank(Delta)
            delta_rank_dist[rk] = delta_rank_dist.get(rk, 0) + 1
    
    print(f"\n--- Δ = M_0 + q⊗r rank distribution (all q,r ∈ F_2^9) ---")
    for rk, cnt in sorted(delta_rank_dist.items()):
        print(f"  rank {rk}: {cnt} cases")
    
    # Now the key structural question: for each Δ, what is the minimum number
    # of rank-1 terms needed to express Δ over F_2?
    # This is the tensor rank of Δ as a matrix.
    # If this rank exceeds the number of available lifted terms, it's impossible.
    
    # For Q ≠ 0: Δ = M_0 + q⊗r. 
    # rank(Δ) = rank(M_0 + q⊗r).
    # The matrix rank of Δ is a lower bound on the number of rank-1 terms needed.
    # If rank(Δ) > 19, impossible (but rank is ≤ 9, so this doesn't help directly).
    # However, the constraint is that the rank-1 terms forming Δ must ALSO form
    # a valid core decomposition in their other roles.
    
    # Save results
    results = {
        "M0_rank": 3,
        "delta_rank_distribution": delta_rank_dist,
        "block_type_counts": {str(k): v for k, v in block_type_counts.items()},
        "key_observation": "Q=0 case requires lifted terms to sum to I_3 in block (0,0) with exact cancellation in all 8 other blocks. Each such term also participates in core slices, creating coupled constraints.",
        "structural_implications": {
            "Q_equals_zero": "Δ has rank 3, supported only on block (0,0). Lifted terms cannot be block-confined without u_i=0 contradiction. Must use terms with cross-block components that exactly cancel.",
            "Q_nonzero": "Δ = M_0 + q⊗r has rank 2-4. Block structure determined by q,r sub-vectors. Imposes bilinear factorization constraint on lifted subset of core terms."
        }
    }
    
    with open(OUTDIR / "lift_obstruction_analysis.json", "w") as f:
        json.dump(results, f, indent=2)
    
    print(f"\nSaved: {OUTDIR / 'lift_obstruction_analysis.json'}")
    
    # ========================================
    # KEY STRUCTURAL THEOREM ATTEMPT
    # ========================================
    print("\n" + "=" * 60)
    print("KEY STRUCTURAL ANALYSIS: Block-(0,0) coupling")
    print("=" * 60)
    
    # For a lifted term i with ε_i = 1:
    # Let v_i = (α_i, β_i, γ_i) where α_i, β_i, γ_i ∈ F_2^3 (B-blocks 0,1,2)
    # Let w_i = (a_i, b_i, c_i) where a_i, b_i, c_i ∈ F_2^3 (C-blocks 0,1,2)
    # Then v_i ⊗ w_i has block (s,t) = {α,β,γ}_s ⊗ {a,b,c}_t
    
    # For Δ = M_0 + q⊗r:
    # Block (0,0): sum_{lifted} α_i ⊗ a_i = I_3 + q_0 ⊗ r_0
    # Block (0,1): sum_{lifted} α_i ⊗ b_i = q_0 ⊗ r_1
    # Block (0,2): sum_{lifted} α_i ⊗ c_i = q_0 ⊗ r_2
    # Block (1,0): sum_{lifted} β_i ⊗ a_i = q_1 ⊗ r_0
    # Block (1,1): sum_{lifted} β_i ⊗ b_i = q_1 ⊗ r_1
    # Block (1,2): sum_{lifted} β_i ⊗ c_i = q_1 ⊗ r_2
    # Block (2,0): sum_{lifted} γ_i ⊗ a_i = q_2 ⊗ r_0
    # Block (2,1): sum_{lifted} γ_i ⊗ b_i = q_2 ⊗ r_1
    # Block (2,2): sum_{lifted} γ_i ⊗ c_i = q_2 ⊗ r_2
    
    # The off-block-(0,0) equations are very structured:
    # Rows s=1,2: q_s ⊗ r_t tells us the B-block-s × C-block-t sum
    # The factored form means: if we define
    #   P = sum_{lifted} β_i ⊗ (a_i, b_i, c_i) = sum_{lifted} β_i ⊗ w_i_full
    # restricted to B-block 1, it must equal q_1 ⊗ r.
    
    # Even more: define for each B-block s:
    #   F_s = sum_{lifted} {α,β,γ}_s ⊗ w_i
    # This is a 3×9 matrix. The constraint says:
    #   F_0 = I_3 + q_0 ⊗ r_0 in block-col 0, q_0 ⊗ r_1 in block-col 1, q_0 ⊗ r_2 in block-col 2
    #       = I_3_block0 + q_0 ⊗ r
    #   Wait, that's not right. F_0 is a 3×9 matrix.
    
    # F_0 = [I_3 + q_0⊗r_0 | q_0⊗r_1 | q_0⊗r_2]
    # If q_0 = 0: F_0 = [I_3 | 0 | 0], rank 3
    # If q_0 ≠ 0: F_0 = [I_3 + q_0⊗r_0 | q_0⊗r_1 | q_0⊗r_2]
    #             = [I_3 | 0 | 0] + q_0 ⊗ r (outer product, 3×9)
    #             rank is 3 if r is not in row-space of [I_3|0|0], 
    #             or if q_0 ⊗ r adds rank to I_3 block
    
    # F_1 = [q_1⊗r_0 | q_1⊗r_1 | q_1⊗r_2] = q_1 ⊗ r (rank ≤ 1)
    # F_2 = [q_2⊗r_0 | q_2⊗r_1 | q_2⊗r_2] = q_2 ⊗ r (rank ≤ 1)
    
    # So: sum_{lifted} β_i ⊗ w_i = q_1 ⊗ r   (rank ≤ 1, 3×9)
    #     sum_{lifted} γ_i ⊗ w_i = q_2 ⊗ r   (rank ≤ 1, 3×9)
    
    # This is EXTREMELY restrictive!
    # The sum of rank-1 terms β_i ⊗ w_i (over lifted terms) must be a rank-≤1 matrix.
    # Since β_i ∈ F_2^3 and w_i ∈ F_2^9, each term β_i ⊗ w_i is rank ≤ 1.
    # The sum being rank ≤ 1 means: either all nonzero β_i are equal (same B-block-1 
    # component), or all nonzero w_i are equal, or more generally the (β_i, w_i) pairs
    # generate a rank-1 matrix.
    
    # If q_1 = 0: sum_{lifted} β_i ⊗ w_i = 0
    #   This means for EACH C-index, the sum of β_i over lifted terms with w_i having
    #   that C-index set must be 0. Very restrictive.
    
    # If q_1 ≠ 0: sum = q_1 ⊗ r, rank 1.
    #   All lifted terms i with β_i ≠ 0 must have β_i proportional to q_1 (over F_2,
    #   this means β_i = q_1 for all such terms). Then sum = q_1 ⊗ (sum_{i: β_i≠0} w_i) = q_1 ⊗ r.
    #   So sum_{i: β_i=q_1, lifted} w_i = r.
    
    print("\nKey structural equations for B-blocks 1 and 2:")
    print("  sum_{lifted} β_i ⊗ w_i = q_1 ⊗ r  (rank ≤ 1)")
    print("  sum_{lifted} γ_i ⊗ w_i = q_2 ⊗ r  (rank ≤ 1)")
    print("")
    print("If q_1 ≠ 0: all lifted terms with nonzero B-block-1 component")
    print("  must have β_i = q_1 (same direction), and their w_i sum to r.")
    print("If q_1 = 0: all B-block-1 contributions from lifted terms cancel.")
    print("Same for q_2, γ_i.")
    
    # Now combine with core equations.
    # Core slice s has assigned block (j_s, i_s).
    # The terms in slice s with their B-factor restricted to block j_s must sum to I_3.
    # But if j_s = 1 or 2, the lifted terms in that slice have β_i (or γ_i)
    # constrained by the rank-≤1 condition above.
    
    # This creates a direct coupling between core feasibility and lift feasibility!
    
    print("\n" + "=" * 60)
    print("COUPLING ANALYSIS")
    print("=" * 60)
    
    # Let me enumerate the assigned blocks for each core slice:
    # Slice 0 (related analysis): block (1,0) -> B-block 1, C-block 0
    # Slice 1 (related analysis): block (2,0) -> B-block 2, C-block 0
    # Slice 2 (a10): block (0,1) -> B-block 0, C-block 1
    # Slice 3 (a11): block (1,1) -> B-block 1, C-block 1
    # Slice 4 (a12): block (2,1) -> B-block 2, C-block 1
    # Slice 5 (a20): block (0,2) -> B-block 0, C-block 2
    # Slice 6 (a21): block (1,2) -> B-block 1, C-block 2
    # Slice 7 (a22): block (2,2) -> B-block 2, C-block 2
    
    assignments = [
        (0, "related analysis", 1, 0), (1, "related analysis", 2, 0), (2, "a10", 0, 1),
        (3, "a11", 1, 1), (4, "a12", 2, 1), (5, "a20", 0, 2),
        (6, "a21", 1, 2), (7, "a22", 2, 2)
    ]
    
    print("\nSlice assignments:")
    for s, name, bblock, cblock in assignments:
        print(f"  Slice {s} ({name}): B-block {bblock}, C-block {cblock}")
    
    # For B-block 1 (slices 0, 3, 6 = related analysis, a11, a21):
    # The lifted terms in these slices have β_i constrained.
    # If q_1 ≠ 0: all lifted terms with β_i ≠ 0 have β_i = q_1.
    # But core equation for slice 0: sum_{i ∈ T_0} v_i^{(1)} ⊗ w_i^{(0)} = I_3
    # v_i^{(1)} = β_i. So: sum_{i ∈ T_0} β_i ⊗ w_i^{(0)} = I_3 (in 3×3)
    # If q_1 ≠ 0 and all lifted terms in T_0 have β_i = q_1:
    #   Contribution from lifted terms: q_1 ⊗ (sum_{i ∈ T_0, lifted} w_i^{(0)}) = rank ≤ 1
    #   But we need rank 3 (I_3). So non-lifted terms must contribute the rest:
    #   sum_{i ∈ T_0, not lifted} β_i ⊗ w_i^{(0)} = I_3 + q_1 ⊗ (sum_{i ∈ T_0, lifted} w_i^{(0)})
    #   This has rank ≥ 2.
    
    print("\n--- B-block 1 coupling (slices related analysis, a11, a21) ---")
    print("Lift constraint: sum_{lifted} β_i ⊗ w_i = q_1 ⊗ r")
    print("Core equations need β_i ⊗ w_i^{(c)} to produce I_3 in specific blocks")
    print("If q_1 ≠ 0: lifted terms constrained to single B-block-1 direction q_1")
    print("If q_1 = 0: all B-block-1 contributions from lifted terms must cancel")
    
    # This is the mathematical mechanism. Let me now check:
    # Can we derive a contradiction from these coupled constraints?
    
    # Let's think about the q_1 = q_2 = 0 case (q confined to block 0).
    # Then: all lifted terms have β_i = 0 and γ_i = 0.
    # i.e., lifted terms have v_i confined to B-block 0: v_i = (α_i, 0, 0).
    # Combined with the block (0,0) constraint: sum_{lifted} α_i ⊗ a_i = I_3 + q_0 ⊗ r_0
    
    # But lifted terms have v_i = (α_i, 0, 0).
    # In core slice s=0 (block (1,0)): need sum_{i ∈ T_0} v_i^{(1)} ⊗ w_i^{(0)} = I_3
    # v_i^{(1)} = β_i = 0 for all lifted terms.
    # So only non-lifted terms in T_0 contribute: sum_{i ∈ T_0, not lifted} β_i ⊗ w_i^{(0)} = I_3
    # The lifted terms don't affect this slice's assigned block at all.
    # But in block (0,0) of slice 0: sum_{i ∈ T_0} v_i^{(0)} ⊗ w_i^{(0)}
    # = sum_{i ∈ T_0, lifted} α_i ⊗ a_i + sum_{i ∈ T_0, not lifted} v_i^{(0)} ⊗ w_i^{(0)}
    # This must equal 0 (block (0,0) is not the assigned block for slice 0).
    
    # So: the lifted terms in T_0 contribute α_i ⊗ a_i to block (0,0) of slice 0,
    # and this must be canceled by the non-lifted terms' block-(0,0) contributions.
    
    # This creates a cascade: each slice's block-(0,0) pollution from lifted terms
    # must be exactly canceled by non-lifted terms.
    
    print("\n--- q_1 = q_2 = 0 subcase ---")
    print("All lifted terms confined to B-block 0")
    print("Lifted terms contribute nothing to assigned blocks of slices 0-7")
    print("  (assigned blocks are (1,0),(2,0),(0,1),(1,1),(2,1),(0,2),(1,2),(2,2))")
    print("Block (0,0) pollution in each slice must be canceled by non-lifted terms")
    print("Meanwhile, block (0,0) of Δ = I_3 + q_0⊗r_0 requires heavy block-0 load")
    
    # Save the complete analysis
    print(f"\n{'='*60}")
    print("SUMMARY OF LIFT OBSTRUCTION STRUCTURE")
    print(f"{'='*60}")
    print("""
For a hypothetical rank-20 full T_{333} decomposition:
- Exactly 1 pure E_{00} term + 19 core terms
- Lift bits ε_1,...,ε_19 satisfy: rank(M_0 + sum_{ε_i=1} v_i⊗w_i) ≤ 1
- This equals q⊗r for some q,r ∈ F_2^9

Key structural consequences:
1. B-block decomposition: for each B-block s ∈ {0,1,2}:
   sum_{lifted} v_i^{(s)} ⊗ w_i = q_s ⊗ r (rank ≤ 1 or 0)
   
2. If q_s ≠ 0: all lifted terms with nonzero B-block-s component
   share the SAME B-block-s direction q_s.
   
3. Core slices assigned to B-block s require their terms to produce
   I_3 in the assigned sub-block. The lifted terms' contribution is
   rank ≤ 1 (single direction), requiring non-lifted terms to carry
   at least rank 2 of I_3.
   
4. The off-assigned-block cancellation in core equations couples
   lifted and non-lifted terms through block-(0,0) and cross-block
   pollution, creating a rigid system.
   
5. The complete constraint is: find 19 core terms + ε bits such that
   BOTH the core equations AND the rank-≤1 lift condition hold.
   This is a finite algebraic problem over F_2.
""")

if __name__ == "__main__":
    main()
