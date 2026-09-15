import QiushiDefs
import QiushiOccupation
import QiushiOccupationAPI

/-!
# Exact total weight for occupation systems

The occupation API proves only upper bounds.  A no-model theorem needs
the exact total weight: the occupation vector sums to exactly the target,
not merely at most.  This module provides that theorem fiberwise.

Key results:
- `occupation_total_weight`: ∑_b fiberCard f b = r for any f : Fin r → β
- `zero_fiber_eq_killSet`: the zero fiber is exactly the killSet
- `fiber_subset_killSet_of_mem_idem`: fibers in U are in killSet D U
- `occupation_system_holds`: occupation rows + total weight
- `quotientRankAtLeast_of_occupation_noModel`: no-model → QuotientRankAtLeast
-/

open Matrix BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace QiushiMatmul

-- ============================================================================
-- Fiber partition of the index set
-- ============================================================================

/-- The fiber of `t` under a classification function `f`. -/
def fiberOf {r : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → β) (b : β) : Finset (Fin r) :=
  Finset.univ.filter (fun t => f t = b)

/-- The cardinality of a fiber. -/
def fiberCard {r : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → β) (b : β) : ℕ :=
  (fiberOf f b).card

/-- **Exact total weight.**  The sum of fiber cardinalities over all values
equals `r`.  This is the identity that prevents the zero solution from
satisfying the occupation system. -/
theorem occupation_total_weight {r : ℕ} {β : Type*} [DecidableEq β] [Fintype β]
    (f : Fin r → β) :
    ∑ b : β, fiberCard f b = r := by
  have h : (Finset.univ : Finset (Fin r)).card =
      ∑ b ∈ (Finset.univ : Finset β),
        ((Finset.univ : Finset (Fin r)).filter (fun a => f a = b)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun a _ => Finset.mem_univ (f a))
  -- h : Finset.univ.card = ∑ b, {a | f a = b}.card
  -- We know Finset.univ.card = Fintype.card (Fin r) = r
  have hcard : (Finset.univ : Finset (Fin r)).card = r := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hcard] at h
  -- h : r = ∑ b ∈ univ, {a ∈ univ | f a = b}.card
  -- goal : ∑ b : β, fiberCard f b = r
  -- h : r = ∑ b, {a | f a = b}.card
  -- fiberCard f b = {a | f a = b}.card by definition (fiberOf = univ.filter)
  -- so the LHS sums are equal
  exact h.symm

-- ============================================================================
-- Zero fiber = killSet
-- ============================================================================

/-- When `red M = 0 ↔ M ∈ W`, the zero fiber is exactly the killSet. -/
theorem zero_fiber_eq_killSet {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r)
    (red : Mat3 → Mat3)
    (hred_zero : ∀ M : Mat3, red M = 0 ↔ M ∈ W) :
    fiberOf (fun t => red (D.A t)) 0 = killSet D W := by
  ext t
  simp [fiberOf, killSet, hred_zero]

-- ============================================================================
-- Row constraint: fiber in U ⊆ killSet (with idempotent red)
-- ============================================================================

/-- If `red` classifies by W-coset and is idempotent, then the fiber of any
`M ∈ U` is contained in `killSet D U`. -/
theorem fiber_subset_killSet_of_mem_idem {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r : ℕ} (D : QuotientTensorDecomp W r)
    (red : Mat3 → Mat3)
    (hred_cos : ∀ M₁ M₂ : Mat3, red M₁ = red M₂ → M₁ + M₂ ∈ W)
    (hred_idem : ∀ M : Mat3, red (red M) = red M)
    (M : Mat3) (hM : M ∈ U) :
    fiberOf (fun t => red (D.A t)) M ⊆ killSet D U := by
  intro t ht
  simp [fiberOf] at ht
  simp [killSet]
  -- red (D.A t) = M
  -- congr: red (red (D.A t)) = red M
  -- idem: red (red (D.A t)) = red (D.A t) = M
  -- so red M = M
  have h1 : red M = M := by
    have h2 : red (red (D.A t)) = red M := congr_arg red ht
    rw [hred_idem] at h2
    -- h2 : red (D.A t) = red M
    rw [ht] at h2
    -- h2 : M = red M
    exact h2.symm
  -- red (D.A t) = M = red M, so by hred_cos: D.A t + M ∈ W
  have h3 : D.A t + M ∈ W := hred_cos (D.A t) M (by rw [ht, h1])
  -- D.A t = (D.A t + M) + M ∈ U
  have h4 : D.A t = (D.A t + M) + M := by
    rw [add_assoc, mat3_add_self_eq_zero M, add_zero]
  rw [h4]
  exact U.add_mem (hWU h3) hM

-- ============================================================================
-- Occupation system at exact total weight
-- ============================================================================

/-- The occupation row bound: for a set S of representatives in U with
distinct red values, the sum of fiber cards is ≤ target - m. -/
theorem occupation_system_holds {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r : ℕ} (D : QuotientTensorDecomp W r)
    (red : Mat3 → Mat3)
    (hred_cos : ∀ M₁ M₂ : Mat3, red M₁ = red M₂ → M₁ + M₂ ∈ W)
    (hred_idem : ∀ M : Mat3, red (red M) = red M)
    (S : Finset Mat3)
    (hS_U : ∀ M ∈ S, M ∈ U)
    {m : ℕ} (hm : QuotientRankAtLeast U m) (hmr : m ≤ r)
    {target : ℕ} (hrt : r ≤ target) :
    ∑ M ∈ S, fiberCard (fun t => red (D.A t)) M ≤ target - m := by
  have hsub : ∀ M ∈ S, fiberOf (fun t => red (D.A t)) M ⊆ killSet D U :=
    fun M hM => fiber_subset_killSet_of_mem_idem hWU D red hred_cos hred_idem M (hS_U M hM)
  -- Fibers for distinct values are disjoint (by injectivity of the fiber map)
  have hdisj : ∀ M₁ ∈ S, ∀ M₂ ∈ S, M₁ ≠ M₂ →
      Disjoint (fiberOf (fun t => red (D.A t)) M₁)
               (fiberOf (fun t => red (D.A t)) M₂) := by
    intro M₁ hM₁ M₂ hM₂ hne
    simp [fiberOf]
    rw [Finset.disjoint_filter]
    intro t _ h1 h2
    exact hne (h1 ▸ h2)
  -- Sum ≤ killSet
  have hsum_le : ∑ M ∈ S, fiberCard (fun t => red (D.A t)) M ≤ (killSet D U).card := by
    simp [fiberCard]
    calc ∑ M ∈ S, (fiberOf (fun t => red (D.A t)) M).card
        = (S.biUnion (fun M => fiberOf (fun t => red (D.A t)) M)).card := by
          rw [Finset.card_biUnion]
          intro M₁ hM₁ M₂ hM₂ hne
          exact hdisj M₁ hM₁ M₂ hM₂ hne
      _ ≤ (killSet D U).card := by
          apply Finset.card_le_card
          exact Finset.biUnion_subset.mpr (fun M hM => hsub M hM)
  -- killSet ≤ target - m
  exact le_trans hsum_le (killSet_le_target hWU D hm hmr hrt)

-- ============================================================================
-- Discharge theorem: no-model implies QuotientRankAtLeast
-- ============================================================================

/-- If every `QuotientTensorDecomp W r` with `r ≤ T` is impossible,
then `QuotientRankAtLeast W (T+1)` holds. -/
theorem quotientRankAtLeast_of_occupation_noModel
    (W : Submodule F2 Mat3) (T : ℕ)
    (h : ∀ r : ℕ, r ≤ T → ∀ D : QuotientTensorDecomp W r, False) :
    QuotientRankAtLeast W (T + 1) := by
  intro r hr
  exact ⟨h r (Nat.lt_succ_iff.mp hr)⟩

end QiushiMatmul
end
