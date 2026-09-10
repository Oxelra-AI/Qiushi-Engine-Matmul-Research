# Block-Spread Structure for E11 Core — analysis Notes

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Discovery

The E11 8×9×9 core over F₂ has a 3×3 block structure that couples A-support
to B/C completion. This is the first certified constraint that crosses the A/BC
boundary in our E11 encoding.

## Block Structure (Corrected Convention)

Tensor convention: T[3i+j, 3j+k, 3i+k] = 1 for all i,j,k ∈ {0,1,2}.

- Row groups (B-side): R_j = {3j, 3j+1, 3j+2} for j = 0,1,2
- Col groups (C-side): C_i = {3i, 3i+1, 3i+2} for i = 0,1,2
- Both use the SAME contiguous partition: masks [7, 56, 448]
- Core slice s → block R_{j(s)} × C_{i(s)} where j = (s+1)%3, i = (s+1)//3
- Deleted slice (a=0) → block R_0 × C_0

Slice mapping:
  s=0: (j=1,i=0) R₁×C₀  |  s=4: (j=2,i=1) R₂×C₁
  s=1: (j=2,i=0) R₂×C₀  |  s=5: (j=0,i=2) R₀×C₂
  s=2: (j=0,i=1) R₀×C₁  |  s=6: (j=1,i=2) R₁×C₂
  s=3: (j=1,i=1) R₁×C₁  |  s=7: (j=2,i=2) R₂×C₂

## Purity Lemma

If slice s has exactly 3 active terms (capacity 3), then:
- Each term's v is confined to R_{j(s)} (zero outside)
- Each term's w is confined to C_{i(s)} (zero outside)
- The 3 restricted v-vectors form an invertible 3×3 matrix over F₂ (GL₃ element)
- Completion is closed-form: W = V^{-T}, 168 choices

Proof: On the own block, 3 rank-1 matrices sum to I₃ (rank 3), so their restricted
V is invertible. Off-block condition forces V_{k'} W_i^T = 0; since W_i is
invertible, V_{k'} = 0 for all k' ≠ k(s). Symmetric argument for columns.

Consequence: No term serves two distinct capacity-3 slices (block disjointness).
For rank 19: p = #{capacity-3 slices} ≤ 5 (not 6; proved by counting).
Total A-weight ≥ 3p + 4(8-p) = 32-p ≥ 27 (improves the old ≥ 24 bound).

## Certified Constraints R1 and R2

R1: For each slice s, at least 3 terms active in s have v meeting R_{j(s)}
and w meeting C_{i(s)}. (Rank of I₃ on the own block is 3.)

R2: For each slice s and each off-block β ≠ block(s), the number of terms
active in s that hit β is never exactly 1. (A single nonzero rank-1 matrix
on an off-block cannot sum to zero over F₂.)

These are consequences of the Brent equations. They couple A-support to B/C
data for the first time in our encoding.

## Verification

All 519 rank-21 pool decompositions pass:
- Purity: 0 violations
- R1: 0 violations
- R2: 0 violations
- Cap3 separation: 0 violations
- GL₃: 0 violations

Pool statistics (rank 21):
- p distribution: 0 (309), 1 (183), 2 (27)
- Total weight: min 39, max 90
- Block-spread |B(t)| ∈ {1, 2, 3, 4, 6, 9} only (5, 7, 8 impossible)

## Augmented CNF

Base certified CNF: 25,964 vars, 90,628 clauses
Augmented (block-spread): 27,902 vars, 99,396 clauses (+1,938 vars, +8,768 clauses)

New variables: 57 brow + 57 bcol + 1368 block_hit + 456 R1 counter = 1,938
New clauses: 228 brow defs + 228 bcol defs + 5472 block_hit defs + 1624 R1 + 1216 R2 = 8,768

Branch augmented CNFs also generated for all 8 branches.

Validation: rank-21 row 0 satisfies all 7,904 block-spread clause instances.
CaDiCaL 60s pilot: UNKNOWN (expected; structural coupling helps propagation but
doesn't make the problem trivially solvable).

## Strategic Implications

1. The block-spread is the first A↔B/C coupling in the certified layer. All previous
   constraints (Brent, capacity, sorting, orbits) are A-only or BC-only.

2. For construction search: capacity-3 slices have GL₃ closed-form completion.
   Stream Wang-admissible supports → shadow filter → enumerate cap-3 GL₃ choices →
   solve remaining bilinear system. One hit = rank-22 algorithm.

3. For lower-bound analysis: capacity profiles (c_0,...,c_7) with p ≤ 5 and
   weight ≥ 27 form a finite enumerable space. The p=5 corner is especially
   constrained (15 committed + 4 free terms, 3 remaining slices each needing
   ≥ 3 block-hitters from 4 free terms).

4. The block lemmas apply to the full 9×9×9 tensor too: 9 slices, 9 blocks,
   total weight ≥ 27 for rank 20. This may constrain full rank-20 decompositions
   directly.

## Files

- Check script: workspace/scripts/e11_block_spread_check.py
- Augmentation script: workspace/scripts/e11_block_spread_augment.py
- Pool check: workspace/data/block_spread/pool_block_spread_check.json
- Augmented CNF: workspace/data/core_sat/e11_rank19_blockspread.cnf
- Branch augmented: workspace/data/core_sat/branches/e11_rank19_branch{0..7}_bs.cnf
