#!/usr/bin/env python3
"""
Deeper analysis of E11 core decomposition structure over F_2.

Explores:
  1. Block structure of core slices and rank-one sharing
  2. Projected A-direction analysis from rank-23 scheme
  3. Affine geometry of residual condition
  4. Necessary conditions for rank-19 core

The 9x9 B⊗C matrix space decomposes into 3x3 blocks indexed by
  (B-block, C-block) where B-block k = {e_{k1}, e_{k2}, e_{k3}}
  and C-block i = {e_{i1}, e_{i2}, e_{i3}}.
  
Core slices occupy blocks (k,i) -> e_{ik} for (i,k) != (1,1):
  (2,1)->e_{12}, (3,1)->e_{13}, (1,2)->e_{21}, (2,2)->e_{22},
  (3,2)->e_{23}, (1,3)->e_{31}, (2,3)->e_{32}, (3,3)->e_{33}
  
M_0 occupies block (1,1).
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


def build_matmul_tensor():
    T = np.zeros((9, 9, 9), dtype=int)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+k, 3*k+j, 3*i+j] = 1
    return T


def analyze_block_sharing():
    """
    Analyze which rank-one bc^T matrices can contribute to multiple core slices.
    
    A rank-one matrix bc^T where b is nonzero in B-blocks p1,...,pa
    and c is nonzero in C-blocks q1,...,qb contributes to core slices
    at positions {(pk, ql)} that are in the core set (i.e., not (1,1)).
    
    But it also must actually match the core slice content at those positions.
    Each core slice in block (k,i) is the 3x3 identity matrix.
    So the (k,i)-block of bc^T must equal I_3 summed with contributions from
    other terms assigned to that same core slice.
    """
    print("=== Block sharing structure ===")
    
    # B-blocks: 0={0,1,2}, 1={3,4,5}, 2={6,7,8}
    # C-blocks: 0={0,1,2}, 1={3,4,5}, 2={6,7,8}
    # Core blocks: (bk, ci) -> core direction, excluding (0,0)
    # (bk, ci) where bk=k-1, ci=i-1 -> e_{ik} in core (i!=1 or k!=1)
    
    # For a rank-one bc^T in the (bk, ci) block:
    # bc^T restricted to rows 3*bk:3*bk+3, cols 3*ci:3*ci+3
    # = b_block * c_block^T where b_block = b[3*bk:3*bk+3], c_block = c[3*ci:3*ci+3]
    
    # The target at each core block is I_3. So we need:
    # sum of (b_block * c_block^T) for all terms assigned to this block = I_3
    
    # Q: How many distinct rank-one 3x3 matrices over F_2 are there?
    count_r1_3x3 = 0
    r1_3x3 = []
    for b_int in range(1, 8):  # nonzero 3-bit vectors
        for c_int in range(1, 8):
            b = np.array([(b_int >> i) & 1 for i in range(3)])
            c = np.array([(c_int >> i) & 1 for i in range(3)])
            r1_3x3.append((b, c, np.outer(b, c)))
            count_r1_3x3 += 1
    
    print(f"Total rank-one 3x3 matrices over F_2: {count_r1_3x3}")
    print(f"  (= (2^3-1)^2 = 7^2 = 49)")
    
    # Which pairs of rank-one 3x3 matrices sum to I_3?
    I3 = np.eye(3, dtype=int)
    decomps_of_I3 = []
    for r in range(2, 8):  # try decompositions of size 2..7
        # For size 2: find all pairs X1, X2 with X1 + X2 = I3
        if r == 2:
            for i, (b1, c1, X1) in enumerate(r1_3x3):
                X2_needed = (I3 - X1) % 2
                rk = f2_rank(X2_needed)
                if rk == 1:
                    # Find b2, c2
                    for j, (b2, c2, X2) in enumerate(r1_3x3):
                        if np.all(X2 == X2_needed):
                            if i <= j:  # avoid double counting
                                decomps_of_I3.append((i, j))
            print(f"\n  Rank-2 decompositions of I_3 over F_2: NONE (I_3 has rank 3)")
        elif r == 3:
            # I_3 is sum of 3 rank-one matrices: e1e1^T + e2e2^T + e3e3^T
            # Are there other 3-term decompositions?
            count_3term = 0
            for i, (b1, c1, X1) in enumerate(r1_3x3):
                for j, (b2, c2, X2) in enumerate(r1_3x3):
                    if j <= i:
                        continue
                    X3_needed = (I3 + X1 + X2) % 2  # over F_2: I3 - X1 - X2 = I3 + X1 + X2
                    rk = f2_rank(X3_needed)
                    if rk == 1:
                        for k_idx, (b3, c3, X3) in enumerate(r1_3x3):
                            if k_idx <= j:
                                continue
                            if np.all(X3 == X3_needed):
                                count_3term += 1
            print(f"  Rank-3 decompositions of I_3: {count_3term} (unordered triples)")
            
            # Show them
            shown = 0
            for i, (b1, c1, X1) in enumerate(r1_3x3):
                for j, (b2, c2, X2) in enumerate(r1_3x3):
                    if j <= i: continue
                    X3_needed = (I3 + X1 + X2) % 2
                    rk = f2_rank(X3_needed)
                    if rk != 1: continue
                    for k_idx, (b3, c3, X3) in enumerate(r1_3x3):
                        if k_idx <= j: continue
                        if np.all(X3 == X3_needed):
                            if shown < 5:
                                print(f"    [{b1}⊗{c1}] + [{b2}⊗{c2}] + [{b3}⊗{c3}]")
                                shown += 1
            if count_3term > 5:
                print(f"    ... ({count_3term - 5} more)")
    
    return r1_3x3


def analyze_sharing_potential(r1_3x3):
    """
    For each pair of core blocks (k1,i1) and (k2,i2), determine if a single 
    rank-one 9x9 matrix can contribute to BOTH blocks simultaneously while
    matching the target content.
    
    A rank-one 9x9 matrix bc^T contributes to blocks (k,i) where 
    b has nonzero components in B-block k AND c has nonzero in C-block i.
    
    In the (k,i) block, the contribution is b_k ⊗ c_i^T (3x3 rank-one submatrix).
    
    For the core slice at (k,i), the target is I_3.
    So bc^T contributes b_k c_i^T to the target I_3.
    
    Two blocks (k1,i1) and (k2,i2) can share a rank-one matrix if:
    - k1 = k2 (same B-block, different C-blocks): b_k1 c_i1^T and b_k1 c_i2^T
    - i1 = i2 (same C-block, different B-blocks): b_k1 c_i1^T and b_k2 c_i1^T
    - All different: b_k1 c_i1^T, b_k1 c_i2^T, b_k2 c_i1^T, b_k2 c_i2^T
    """
    print("\n=== Cross-block sharing analysis ===")
    
    # Core blocks: all (bk, ci) except (0,0), indexed as bk=0,1,2 ci=0,1,2
    core_blocks = [(bk, ci) for bk in range(3) for ci in range(3) if (bk, ci) != (0, 0)]
    
    print(f"Core blocks: {core_blocks} (8 total)")
    
    # For a rank-one matrix bc^T that hits blocks {(bk, ci)} where bk ∈ supp_B, ci ∈ supp_C:
    # It contributes b_{bk} c_{ci}^T to each block (bk, ci).
    # This is a 3x3 rank-one matrix.
    # The contribution to block (bk, ci) is constrained by:
    #   sum of all contributions at (bk, ci) = I_3
    
    # Key insight: if a rank-one 9x9 matrix contributes to m core blocks,
    # it "saves" m-1 terms compared to using separate rank-one matrices.
    # But it also constrains the blocks: the block-level contributions are
    # all rank-one with shared b or c components.
    
    # For blocks sharing B-row (same bk): contributions are b_k c_{i1}^T and b_k c_{i2}^T
    # These share the B-factor within the block.
    # For blocks sharing C-col (same ci): contributions are b_{k1} c_i^T and b_{k2} c_i^T
    # These share the C-factor.
    # For cross-type: all four sub-contributions share a joint structure.
    
    # Let's count maximum possible savings
    # Each "multi-block" term saves (number of blocks hit - 1)
    # We need total savings >= 24 - 19 = 5
    
    # Case 1: B-row sharing (same bk, different ci's)
    # The three C-blocks ci=0,1,2 each need I_3 in its block
    print("\n  B-row sharing (same B-block, multiple C-blocks):")
    for bk in range(3):
        # For B-block bk, C-blocks 0,1,2 (excluding (0,0)):
        available = [(bk, ci) for ci in range(3) if (bk, ci) != (0, 0)]
        if not available:
            continue
        print(f"    B-block {bk}: core blocks = {available}")
        
        # If we share one rank-one matrix across 2 C-blocks ci1, ci2:
        # b_bk ⊗ c_{ci1} and b_bk ⊗ c_{ci2} are rank-one 3x3 contributions
        # with same B-factor b_bk but different C-factors.
        # This is only possible if we're flexible about HOW to decompose I_3
        # in each of those blocks.
        
    # Case 2: C-column sharing (same ci, different bk's)
    print("\n  C-column sharing (same C-block, multiple B-blocks):")
    for ci in range(3):
        available = [(bk, ci) for bk in range(3) if (bk, ci) != (0, 0)]
        if not available:
            continue
        print(f"    C-block {ci}: core blocks = {available}")
    
    # Count: how many 3x3 I_3 decompositions allow a shared b or c factor?
    I3 = np.eye(3, dtype=int)
    
    # For B-row sharing across ci1, ci2:
    # A term has b_bk fixed and c varying. So the 3x3 contribution to 
    # block (bk, ci) is b_bk ⊗ c_{ci}^T.
    # For two blocks: the same b_bk paired with two different c_{ci1}, c_{ci2}
    # Both contribute to their respective I_3 targets.
    # So b_bk ⊗ c_{ci1}^T is part of the I_3 decomposition in block (bk,ci1)
    # and b_bk ⊗ c_{ci2}^T is part of the I_3 decomposition in block (bk,ci2).
    # The constraint is just that each block decomposition includes a term
    # with B-factor b_bk.
    
    # For a single block: I_3 decomposes as sum of 3+ rank-one matrices.
    # For each such decomposition, which B-factors appear?
    # If two blocks in the same B-row can both use the same B-factor 
    # (but different C-factors), we can share.
    
    # Let's enumerate all 3-term rank-one decompositions of I_3 and 
    # find which b-factors appear
    print("\n  Enumerating 3-term decompositions of I_3 over F_2:")
    
    decomps = []
    for i in range(len(r1_3x3)):
        b1, c1, X1 = r1_3x3[i]
        for j in range(i+1, len(r1_3x3)):
            b2, c2, X2 = r1_3x3[j]
            X3_needed = (I3 + X1 + X2) % 2
            if f2_rank(X3_needed) != 1:
                continue
            for k in range(j+1, len(r1_3x3)):
                b3, c3, X3 = r1_3x3[k]
                if np.all(X3 == X3_needed):
                    decomps.append(((b1,c1), (b2,c2), (b3,c3)))
    
    print(f"  Total 3-term decompositions: {len(decomps)}")
    
    # For each decomposition, record the set of b-factors and c-factors
    b_factor_sets = []
    c_factor_sets = []
    for d in decomps:
        bs = tuple(sorted([tuple(x[0]) for x in d]))
        cs = tuple(sorted([tuple(x[1]) for x in d]))
        b_factor_sets.append(bs)
        c_factor_sets.append(cs)
    
    unique_b_sets = list(set(b_factor_sets))
    unique_c_sets = list(set(c_factor_sets))
    print(f"  Unique B-factor sets: {len(unique_b_sets)}")
    print(f"  Unique C-factor sets: {len(unique_c_sets)}")
    
    # Check which decompositions share a b-factor with the standard decomposition
    standard = {(1,0,0), (0,1,0), (0,0,1)}
    for d in decomps[:10]:
        bs = set(tuple(x[0]) for x in d)
        cs = set(tuple(x[1]) for x in d)
        shared_b = bs & standard
        shared_c = cs & standard
        print(f"    b-factors: {[list(x[0]) for x in d]}, "
              f"c-factors: {[list(x[1]) for x in d]}, "
              f"shared_b_with_std: {len(shared_b)}")
    
    return decomps


def check_sharing_between_blocks(decomps):
    """
    For two core blocks in the same B-row or C-column,
    find pairs of I_3 decompositions that share a factor.
    
    This directly computes how many terms can be saved through sharing.
    """
    print("\n=== Compatible decomposition pairs for sharing ===")
    
    # B-row sharing: blocks (bk, ci1) and (bk, ci2) with ci1 != ci2
    # We need a 3-term decomposition of I_3 in each block such that
    # at least one b-factor is shared (same b in both decompositions)
    
    # For each pair of decompositions, count shared b-factors
    share_1 = 0  # pairs sharing exactly 1 b-factor
    share_2 = 0  # pairs sharing exactly 2 b-factors
    share_3 = 0  # pairs sharing all 3 b-factors
    
    for i, d1 in enumerate(decomps):
        bs1 = [tuple(x[0]) for x in d1]
        for j, d2 in enumerate(decomps):
            if j <= i:
                continue
            bs2 = [tuple(x[0]) for x in d2]
            shared = len(set(bs1) & set(bs2))
            if shared == 1:
                share_1 += 1
            elif shared == 2:
                share_2 += 1
            elif shared == 3:
                share_3 += 1
    
    total_pairs = len(decomps) * (len(decomps) - 1) // 2
    print(f"  Total decomposition pairs: {total_pairs}")
    print(f"  Pairs sharing 1 b-factor: {share_1} ({100*share_1/total_pairs:.1f}%)")
    print(f"  Pairs sharing 2 b-factors: {share_2} ({100*share_2/total_pairs:.1f}%)")
    print(f"  Pairs sharing 3 b-factors: {share_3} ({100*share_3/total_pairs:.1f}%)")
    
    # Same for c-factor sharing
    cs_share_1 = 0
    cs_share_2 = 0
    cs_share_3 = 0
    
    for i, d1 in enumerate(decomps):
        cs1 = [tuple(x[1]) for x in d1]
        for j, d2 in enumerate(decomps):
            if j <= i:
                continue
            cs2 = [tuple(x[1]) for x in d2]
            shared = len(set(cs1) & set(cs2))
            if shared == 1:
                cs_share_1 += 1
            elif shared == 2:
                cs_share_2 += 1
            elif shared == 3:
                cs_share_3 += 1
    
    print(f"  Pairs sharing 1 c-factor: {cs_share_1} ({100*cs_share_1/total_pairs:.1f}%)")
    print(f"  Pairs sharing 2 c-factors: {cs_share_2} ({100*cs_share_2/total_pairs:.1f}%)")
    print(f"  Pairs sharing 3 c-factors: {cs_share_3} ({100*cs_share_3/total_pairs:.1f}%)")
    

def analyze_residual_geometry():
    """
    Analyze the residual rank condition:
    For a 19-term core decomposition, the affine space 
    {M_0 + sum_{i in S} X_i : S ⊆ {1,...,19}} must contain a rank-≤1 matrix
    for a rank-20 full decomposition to exist.
    
    This function computes statistics about the rank-≤1 variety.
    """
    print("\n=== Residual rank geometry ===")
    
    # M_0 as a 9x9 matrix
    M0 = np.zeros((9, 9), dtype=int)
    M0[0, 0] = M0[1, 1] = M0[2, 2] = 1
    
    print(f"M_0 rank: {f2_rank(M0)}")
    print(f"M_0 is supported in the (1,1) block")
    
    # Count rank-≤1 matrices in the (1,1) block (3x3)
    count_r0 = 1  # zero matrix
    count_r1 = 7 * 7  # nonzero b and c
    print(f"\nRank-≤1 3x3 matrices over F_2: {count_r0 + count_r1}")
    print(f"  rank-0: {count_r0}, rank-1: {count_r1}")
    
    # For M_0 = I_3 in the (1,1) block, M_0 + sum is rank-≤1 iff
    # sum restricted to (1,1) block brings I_3 down to rank ≤ 1.
    # 
    # Equivalently: I_3 + (sum of X_i in (1,1) block) has rank ≤ 1.
    # 
    # The key is: only X_i terms that have nonzero entries in the (1,1) block
    # can contribute. And a rank-one 9x9 matrix has entries in block (1,1)
    # iff its b-factor has nonzero components in B-block 0 = {0,1,2}
    # AND its c-factor has nonzero components in C-block 0 = {0,1,2}.
    
    I3 = np.eye(3, dtype=int)
    
    # Which rank-one 3x3 matrices X over F_2 have I_3 + X rank ≤ 1?
    count_good = 0
    for b_int in range(1, 8):
        for c_int in range(1, 8):
            b = np.array([(b_int >> i) & 1 for i in range(3)])
            c = np.array([(c_int >> i) & 1 for i in range(3)])
            X = np.outer(b, c)
            R = (I3 + X) % 2
            if f2_rank(R) <= 1:
                count_good += 1
                if count_good <= 10:
                    print(f"  I_3 + [{b}]⊗[{c}]^T has rank {f2_rank(R)}")
    
    print(f"\nRank-one 3x3 X with rank(I_3 + X) ≤ 1: {count_good}")
    
    # Which subsets of rank-one 3x3 matrices sum to I_3 + (rank-≤1)?
    # Equivalently: I_3 = sum_S X_i + Y where Y has rank ≤ 1
    # This means: we need a decomposition of (I_3 - Y) where Y is rank ≤ 1
    # i.e., a rank-≥2 matrix equals sum of rank-one terms
    
    # Actually, for the full residual, M_0 is the full 9x9 matrix with I_3 
    # in the (1,1) block. So the residual M_0 + sum(eps_i X_i) has:
    # - (1,1) block: I_3 + sum of (1,1)-block contributions
    # - other blocks: sum of contributions from shared terms
    # For rank ≤ 1 of the full 9x9 matrix, ALL blocks must be compatible
    # with a single rank-one structure.
    
    # A rank-1 9x9 matrix bc^T has (k,i)-block = b_k ⊗ c_i^T
    # where b_k, c_i are 3-vectors (projections to blocks).
    # If any b_k = 0 or c_i = 0, the corresponding blocks are zero.
    
    # So for M_0 + sum(eps) to have rank ≤ 1:
    # (1,1)-block: I_3 + sum_{(1,1)} = b_1 c_1^T (rank ≤ 1)
    # (k,i)-block for (k,i)!=(1,1): sum_{(k,i)} = b_k c_i^T (rank ≤ 1)
    # AND these must all be compatible (same global b and c).
    
    # For rank = 0 (zero matrix): all blocks must be zero.
    # (1,1): I_3 + sum = 0 => sum = I_3 in (1,1) block
    # other blocks: sum = 0 in each block
    # This means: the sum of selected X_i must equal M_0 exactly.
    
    # For rank = 1 (bc^T): 
    # (1,1): I_3 + sum = b_1 c_1^T => sum = I_3 + b_1 c_1^T
    # other: sum of (k,i)-block contributions = b_k c_i^T
    
    # The "other block" constraints mean: selected X_i must create specific
    # rank-one patterns in non-(1,1) blocks. But these contributions come
    # from the same X_i that also contribute to core slices!
    
    print("\n  Key insight: the residual rank-≤1 condition couples the (1,1) block")
    print("  (where M_0 lives) with ALL other blocks through the global rank-1 constraint.")
    print("  Each X_i that has nonzero entries outside the (1,1) block also contributes")
    print("  to core slices, creating a joint constraint between core decomposition")
    print("  and residual reduction.")
    
    return count_good


def projected_a_analysis():
    """Detailed analysis of projected A-directions from the rank-23 scheme."""
    print("\n=== Projected A-direction analysis from rank-23 scheme ===")
    
    # Parse the scheme
    scheme_path = "data/cn122_3x3_r23_repro/scheme.qmm"
    terms = []
    current = {}
    with open(scheme_path) as f:
        for line in f:
            line = line.strip()
            if line.startswith('term'):
                if current: terms.append(current)
                current = {}
            elif line.startswith('u '): current['u'] = list(map(int, line.split()[1:]))
            elif line.startswith('v '): current['v'] = list(map(int, line.split()[1:]))
            elif line.startswith('w '): current['w'] = list(map(int, line.split()[1:]))
    if current: terms.append(current)
    
    # Reduce mod 2
    proj_dirs = []
    for i, t in enumerate(terms):
        u2 = [abs(x) % 2 for x in t['u']]
        if all(x == 0 for x in u2):
            continue
        proj = tuple(u2[1:])  # project out e_{11}
        eps = u2[0]
        proj_dirs.append({'term': i, 'proj': proj, 'eps': eps, 'weight': sum(proj)})
    
    # Find distinct directions
    unique_dirs = {}
    for d in proj_dirs:
        key = d['proj']
        if key not in unique_dirs:
            unique_dirs[key] = []
        unique_dirs[key].append(d['term'])
    
    print(f"Total F_2 nonzero terms: {len(proj_dirs)}")
    print(f"Distinct projected A-directions: {len(unique_dirs)}")
    
    # Show repeated directions
    for proj, term_list in unique_dirs.items():
        if len(term_list) > 1:
            print(f"  Repeated direction {list(proj)}: terms {term_list}")
    
    # Weight distribution of projected A-directions
    weights = [d['weight'] for d in proj_dirs]
    weight_dist = {}
    for w in weights:
        weight_dist[w] = weight_dist.get(w, 0) + 1
    print(f"\nWeight distribution of projected A-dirs: {dict(sorted(weight_dist.items()))}")
    
    # For a rank-19 core decomposition, we need 19 distinct nonzero directions
    # in F_2^8. How many of the 255 nonzero vectors are weight-w?
    from math import comb
    print(f"\nF_2^8 weight distribution:")
    for w in range(1, 9):
        print(f"  weight {w}: {comb(8, w)} vectors")
    
    # The rank-23 scheme uses 18 distinct directions for 21 terms
    # Effective core rank = 21, but with repeated directions the effective 
    # "distinct-direction rank" would be the rank of the core decomposition 
    # if we merged repeated terms.
    print(f"\nScheme analysis:")
    print(f"  Core terms: {len(proj_dirs)} (from {len(terms)} total)")
    print(f"  Pure E11 terms: {len(terms) - len(proj_dirs)}")
    print(f"  Distinct core directions: {len(unique_dirs)}")
    print(f"  Repeated-direction pairs: {sum(1 for v in unique_dirs.values() if len(v) > 1)}")
    
    # For merged pairs, what's the rank of the merged X_i?
    print(f"\n  For merged repeated-direction terms:")
    for proj, term_list in unique_dirs.items():
        if len(term_list) > 1:
            # Sum the X_i matrices for these terms
            X_sum = np.zeros((9, 9), dtype=int)
            for t_idx in term_list:
                v = np.array([abs(x) % 2 for x in terms[t_idx]['v']])
                w = np.array([abs(x) % 2 for x in terms[t_idx]['w']])
                X_sum = (X_sum + np.outer(v, w)) % 2
            rk = f2_rank(X_sum)
            print(f"    Direction {list(proj)}: merged rank = {rk}")


def main():
    outdir = "data/core_analysis"
    os.makedirs(outdir, exist_ok=True)
    
    print("=" * 60)
    print("E11 CORE DECOMPOSITION STRUCTURE ANALYSIS")
    print("=" * 60)
    
    # Block sharing
    r1_3x3 = analyze_block_sharing()
    
    # Compatible decompositions
    decomps = analyze_sharing_potential(r1_3x3)
    check_sharing_between_blocks(decomps)
    
    # Residual geometry
    analyze_residual_geometry()
    
    # Projected A analysis
    projected_a_analysis()
    
    # Summary
    print("\n" + "=" * 60)
    print("KEY FINDINGS")
    print("=" * 60)
    print("""
1. Each core slice is I_3 in a specific 3x3 block (disjoint supports).
2. Sharing requires rank-one 9x9 matrices that span multiple blocks.
3. The standard I_3 decomposition uses standard basis vectors (no sharing).
4. Non-standard I_3 decompositions allow shared b or c factors across blocks.
5. The residual rank-≤1 condition creates a global coupling between:
   - The (1,1) block (M_0 coverage)
   - All other blocks (core slice matching)
   This coupling is the mathematical heart of the rank-20/rank-≥21 question.
6. The rank-23 scheme gives 21 core terms with only 18 distinct directions.
   Three pairs have repeated projected-A directions.
""")
    
    # Save key results
    with open(os.path.join(outdir, "block_analysis_results.json"), "w") as f:
        json.dump({
            "num_3term_I3_decomps": len(decomps),
            "core_blocks": 8,
            "naive_core_rank_bound": 24,
            "target_core_rank": 19,
            "savings_needed": 5,
        }, f, indent=2)
    
    print(f"\nResults saved to {outdir}/")


if __name__ == "__main__":
    main()
