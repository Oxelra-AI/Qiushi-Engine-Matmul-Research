import QiushiDefs
import QiushiHuaCoset

/-!
# Degenerate affine-coset excess lemma

After normalizing the affine column direction to `e₀` and translating,
if the residual block (rows 1,2 of the base element `p`) has rank ≤ 1,
then:

1. No element of the affine coset `p + e₀ ⊗ F₂³` is invertible.
2. Every "high" element (rank ≥ 2) has rank exactly 2.
3. There are at most 6 rank-two elements in the coset.
4. The total excess (∑ (rank - 1) for high elements) is at most 6.

Since a length-20 decomposition needs A-rank excess ≥ 7,
degenerate cosets cannot supply enough excess.

The argument: rows 1,2 are fixed (rank ≤ 1) while row 0 varies over F₂³.
The span of rows 1,2 is at most 1-dimensional, so it contains 2 elements.
Out of 8 possible row-0 values, 8 − 2 = 6 give row-0 outside the span
of rows 1,2, yielding rank exactly 2.  The other 2 elements have
row-0 in the span, so rank ≤ 1.  No element has rank 3 (that would require
rows 1,2 to span a 2-dimensional space).
-/

open BigOperators

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace QiushiMatmul

-- ════════════════════════════════════════════════════════════════
-- § Finite bitmask computation of degenerate-coset structure
-- ════════════════════════════════════════════════════════════════

/-- The 8 elements of the affine column coset `p + e₀ ⊗ v^T` for `v ∈ F₂³`,
    encoded as matrix codes, given base code `p` and column direction index 0. -/
def cosetElements (baseCode : Nat) : List Nat :=
  (List.range 8).map (fun v => Nat.xor baseCode (v * 1 + v * 2 * 0 + v * 4 * 0))
  -- e₀ ⊗ v^T: row 0 gets XOR'd by v, rows 1,2 unchanged
  -- Actually: e₀ = (1,0,0)^T, v = (v₀,v₁,v₂)
  -- Outer product has entries: (0,j) = v_j, (1,j) = 0, (2,j) = 0
  -- Row-major code: v₀ * 1 + v₁ * 2 + v₂ * 4 (bits 0,1,2)

/-- Properly compute the code of `e₀ ⊗ v^T` from `v : Fin 8`. -/
def outerE0Code (v : Fin 8) : Nat :=
  -- e₀ = (1,0,0), v = 3-bit vector
  -- (e₀ ⊗ v^T)(i,j) = e₀(i) * v(j) = [i=0] * v(j)
  -- Code bits: bit(3*i+j) = [i=0] * bit_j(v)
  -- So bits 0,1,2 get v's bits; bits 3-8 are 0
  v.val

/-- The 8 coset elements from base code `p`. -/
def cosetCodes (p : Nat) : Fin 8 → Nat :=
  fun v => Nat.xor (p &&& 511) (outerE0Code v)

-- ════════════════════════════════════════════════════════════════
-- § The rank profile of a degenerate coset
-- ════════════════════════════════════════════════════════════════

/-- Residual rank: the rank of rows 1,2 of a 9-bit coded matrix.
    This equals rankCode of the matrix with row 0 zeroed out. -/
def residualRank (p : Nat) : Nat :=
  rankCode (p &&& (511 - 7))  -- zero out bits 0,1,2 (row 0)

/-- Count of rank-2 elements in the coset. -/
def cosetRank2Count (p : Nat) : Nat :=
  (List.range 8).countP (fun v => rankCode (Nat.xor (p &&& 511) v) = 2)

/-- Count of rank-3 (invertible) elements in the coset. -/
def cosetRank3Count (p : Nat) : Nat :=
  (List.range 8).countP (fun v => rankCode (Nat.xor (p &&& 511) v) = 3)

/-- Maximum excess from the coset (sum of (rank - 1) for rank ≥ 2 elements). -/
def cosetExcess (p : Nat) : Nat :=
  ((List.range 8).map (fun v =>
    let r := rankCode (Nat.xor (p &&& 511) v)
    if r ≥ 2 then r - 1 else 0)).sum

-- ════════════════════════════════════════════════════════════════
-- § Degenerate coset lemma (decidable)
-- ════════════════════════════════════════════════════════════════

set_option maxHeartbeats 4000000 in
theorem degenerate_coset_no_invertible : ∀ p : Fin 512,
    residualRank p.val ≤ 1 →
    cosetRank3Count p.val = 0 ∧ cosetExcess p.val ≤ 6 := by decide

set_option maxHeartbeats 4000000 in
theorem degenerate_coset_rank0_excess : ∀ p : Fin 512,
    residualRank p.val = 0 →
    cosetRank2Count p.val = 0 ∧ cosetExcess p.val = 0 := by decide

set_option maxHeartbeats 4000000 in
theorem degenerate_coset_rank1_profile : ∀ p : Fin 512,
    residualRank p.val = 1 →
    cosetRank2Count p.val = 6 ∧ cosetRank3Count p.val = 0 ∧ cosetExcess p.val = 6 := by decide

-- ════════════════════════════════════════════════════════════════
-- § Excess contradiction
-- ════════════════════════════════════════════════════════════════

/-- A length-20 decomposition needs A-rank excess ≥ 7 (from split-rank 27 − 20 = 7).
    A degenerate coset has excess ≤ 6. Therefore degenerate cosets cannot
    contain all the high-rank A-factors needed for a length-20 decomposition.

    Formally: if the high-rank factors are confined to a degenerate coset,
    their total excess ≤ 6 < 7. -/
theorem degenerate_excess_contradiction (p : Fin 512) (h : residualRank p.val ≤ 1) :
    cosetExcess p.val < 7 := by
  have ⟨_, hexcess⟩ := degenerate_coset_no_invertible p h
  omega

end QiushiMatmul
