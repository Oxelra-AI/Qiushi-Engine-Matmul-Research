import QiushiDefs
import QiushiOccupation

/-!
# Generic occupation-to-QuotientRankAtLeast reduction

This module provides the generic infrastructure to connect occupation
certificates (branch-and-bound integer infeasibility proofs) to the
`QuotientRankAtLeast` predicate used by the theorem.

Key tools:
- `cosetCount`: counts terms in a quotient decomposition by A-coset
- `sum_cosetCount_le_killSet`: pairwise-distinct coset representatives in U
  contribute at most `killSet D U` terms
- `total_cosetCount_le`: total coset count over distinct reps ≤ r
- `quotientRankAtLeast_of_contradiction`: trivial reduction
-/

open Matrix BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace QiushiMatmul

-- ============================================================================
-- Coset counting
-- ============================================================================

/-- Number of terms in a quotient decomposition whose A-factor is in the
W-coset containing `M`.  Concretely, `cosetCount D M = |{t : D.A t + M ∈ W}|`. -/
def cosetCount {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r) (M : Mat3) : ℕ :=
  (Finset.univ.filter (fun t : Fin r => D.A t + M ∈ W)).card

/-- The filter set underlying a coset count. -/
def cosetFilter {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r) (M : Mat3) : Finset (Fin r) :=
  Finset.univ.filter (fun t : Fin r => D.A t + M ∈ W)

theorem cosetCount_eq_card_cosetFilter {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r) (M : Mat3) :
    cosetCount D M = (cosetFilter D M).card := rfl

-- ============================================================================
-- Coset count at zero = dead count
-- ============================================================================

/-- `cosetCount D 0` is the number of terms with `D.A t ∈ W` (dead terms). -/
theorem cosetCount_zero_eq_killSet {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r) :
    cosetCount D (0 : Mat3) = (killSet D W).card := by
  simp only [cosetCount, killSet, add_zero]

-- ============================================================================
-- Inclusion: coset filter ⊆ killSet
-- ============================================================================

/-- Char-2 self-annihilation for matrices. -/
theorem mat3_add_self_eq_zero (M : Mat3) : M + M = 0 := by
  ext i j; exact CharTwo.add_self_eq_zero _

/-- If `M ∈ U` and `W ≤ U`, then every term counted by `cosetFilter D M` is in `killSet D U`. -/
theorem cosetFilter_subset_killSet {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r : ℕ} (D : QuotientTensorDecomp W r)
    (M : Mat3) (hM : M ∈ U) :
    cosetFilter D M ⊆ killSet D U := by
  intro t ht
  simp only [cosetFilter, killSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  -- D.A t + M ∈ W ⊆ U and M ∈ U, so D.A t = (D.A t + M) + M ∈ U
  have h1 : D.A t + M ∈ U := hWU ht
  have h2 : D.A t = D.A t + M + M := by
    rw [add_assoc, mat3_add_self_eq_zero M, add_zero]
  rw [h2]
  exact U.add_mem h1 hM

-- ============================================================================
-- Disjointness of coset filters
-- ============================================================================

/-- If `M₁ + M₂ ∉ W`, then their coset filters are disjoint. -/
theorem cosetFilter_disjoint {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r)
    (M₁ M₂ : Mat3) (h : M₁ + M₂ ∉ W) :
    Disjoint (cosetFilter D M₁) (cosetFilter D M₂) := by
  simp only [cosetFilter]
  rw [Finset.disjoint_filter]
  intro t _ h1 h2
  -- (D.A t + M₁) + (D.A t + M₂) = M₁ + M₂ + (D.A t + D.A t) = M₁ + M₂ ∈ W
  exfalso
  apply h
  have hsum : D.A t + M₁ + (D.A t + M₂) ∈ W := W.add_mem h1 h2
  have hAA := mat3_add_self_eq_zero (D.A t)
  have heq : D.A t + M₁ + (D.A t + M₂) = M₁ + M₂ := by
    have : D.A t + M₁ + (D.A t + M₂) = D.A t + D.A t + (M₁ + M₂) := by abel
    rw [this, hAA, zero_add]
  rwa [heq] at hsum

-- ============================================================================
-- Sum of coset counts ≤ killSet card
-- ============================================================================

/-- Sum of `cosetCount` over pairwise-distinct coset representatives that lie
in `U` is at most `(killSet D U).card`. -/
theorem sum_cosetCount_le_killSet {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r : ℕ} (D : QuotientTensorDecomp W r)
    (S : Finset Mat3)
    (hU : ∀ M ∈ S, M ∈ U)
    (hdist : ∀ M₁ ∈ S, ∀ M₂ ∈ S, M₁ ≠ M₂ → M₁ + M₂ ∉ W) :
    ∑ M ∈ S, cosetCount D M ≤ (killSet D U).card := by
  simp only [cosetCount_eq_card_cosetFilter]
  calc ∑ M ∈ S, (cosetFilter D M).card
      = (S.biUnion (cosetFilter D)).card := by
        rw [Finset.card_biUnion]
        intro M₁ hM₁ M₂ hM₂ hne
        exact cosetFilter_disjoint D M₁ M₂ (hdist M₁ hM₁ M₂ hM₂ hne)
    _ ≤ (killSet D U).card := by
        apply Finset.card_le_card
        exact Finset.biUnion_subset.mpr (fun M hM =>
          cosetFilter_subset_killSet hWU D M (hU M hM))

-- ============================================================================
-- Total coset count ≤ r
-- ============================================================================

/-- Total coset count over any set of pairwise-distinct representatives ≤ r. -/
theorem total_cosetCount_le {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r)
    (S : Finset Mat3)
    (hdist : ∀ M₁ ∈ S, ∀ M₂ ∈ S, M₁ ≠ M₂ → M₁ + M₂ ∉ W) :
    ∑ M ∈ S, cosetCount D M ≤ r := by
  simp only [cosetCount_eq_card_cosetFilter]
  calc ∑ M ∈ S, (cosetFilter D M).card
      = (S.biUnion (cosetFilter D)).card := by
        rw [Finset.card_biUnion]
        intro M₁ hM₁ M₂ hM₂ hne
        exact cosetFilter_disjoint D M₁ M₂ (hdist M₁ hM₁ M₂ hM₂ hne)
    _ ≤ (Finset.univ : Finset (Fin r)).card := by
        apply Finset.card_le_card
        exact Finset.biUnion_subset.mpr (fun _ _ => Finset.filter_subset _ _)
    _ = r := Fintype.card_fin r

-- ============================================================================
-- Relaxed cap from occupation inequality
-- ============================================================================

/-- Combined occupation + relaxation: `killSet D U` has size ≤ `target - m`
whenever `m ≤ r ≤ target` and `QuotientRankAtLeast U m`. -/
theorem killSet_le_target {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r : ℕ} (D : QuotientTensorDecomp W r)
    {m : ℕ} (hm : QuotientRankAtLeast U m) (hmr : m ≤ r)
    {target : ℕ} (hrt : r ≤ target) :
    (killSet D U).card ≤ target - m := by
  have h := occupation_inequality hWU D hm hmr
  omega

-- ============================================================================
-- Direct False from high quotient bound
-- ============================================================================

/-- If `QuotientRankAtLeast U m` with `m > r` and `W ≤ U`, then any
`QuotientTensorDecomp W r` is impossible. -/
theorem quotient_bound_exceeds_length {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r : ℕ} (D : QuotientTensorDecomp W r)
    {m : ℕ} (hm : QuotientRankAtLeast U m) (hmr : r < m) :
    False := by
  have hpart := kill_surv_card_eq D U
  have hsurv_lt : (survSet D U).card < m := by omega
  exact (hm _ hsurv_lt).false (furtherQuotient hWU D)

-- ============================================================================
-- Trivial reduction
-- ============================================================================

/-- Any way to derive False from a `QuotientTensorDecomp W r` with `r < n`
gives `QuotientRankAtLeast W n`. -/
theorem quotientRankAtLeast_of_contradiction (W : Submodule F2 Mat3) (n : ℕ)
    (h : ∀ r : ℕ, r < n → QuotientTensorDecomp W r → False) :
    QuotientRankAtLeast W n := by
  intro r hr
  exact ⟨h r hr⟩

-- ============================================================================
-- Composition: occupation sum bound + occupation inequality
-- ============================================================================

/-- For a set S of distinct coset reps lying in U, the sum of cosetCounts
is ≤ target - m. Combines `sum_cosetCount_le_killSet` with the relaxed cap. -/
theorem sum_cosetCount_le_cap {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r : ℕ} (D : QuotientTensorDecomp W r)
    (S : Finset Mat3)
    (hU : ∀ M ∈ S, M ∈ U) (hdist : ∀ M₁ ∈ S, ∀ M₂ ∈ S, M₁ ≠ M₂ → M₁ + M₂ ∉ W)
    {m : ℕ} (hm : QuotientRankAtLeast U m) (hmr : m ≤ r) (target : ℕ) (hrt : r ≤ target) :
    ∑ M ∈ S, cosetCount D M ≤ target - m :=
  le_trans (sum_cosetCount_le_killSet hWU D S hU hdist) (killSet_le_target hWU D hm hmr hrt)

-- ============================================================================
-- Coset count nonnegativity (trivial for ℕ, stated for Int casting)
-- ============================================================================

/-- Cast version: coset count is nonneg as Int. -/
theorem cosetCount_nonneg_int {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r) (M : Mat3) :
    (0 : Int) ≤ (cosetCount D M : Int) := Int.natCast_nonneg _

end QiushiMatmul
end
